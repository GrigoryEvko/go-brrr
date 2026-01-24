//! Function index building for cross-file call graph analysis.
//!
//! Builds indexes of all function definitions in a project for efficient
//! lookup during call resolution. Supports multiple lookup strategies:
//! - By simple name (returns all matching functions)
//! - By qualified name (module.Class.method)
//! - By file + name (for resolving local calls)
//!
//! # Memory Efficiency
//!
//! Uses arena-based storage where each function is stored exactly once in a
//! contiguous `Vec<FunctionDef>`. All lookup indexes use `usize` indices into
//! this arena, eliminating duplicate storage and reducing memory usage by ~3x
//! compared to storing function references in multiple HashMaps.

use std::path::{Path, PathBuf};

use rustc_hash::{FxHashMap, FxHashSet};

use rayon::prelude::*;
use tree_sitter::Parser;

use crate::ast::extractor::AstExtractor;
use crate::callgraph::types::FunctionRef;
use crate::error::Result;

/// Metadata about a function definition.
///
/// Extends FunctionRef with additional context needed for precise resolution.
/// Stored once in the FunctionIndex arena; all lookups return references.
#[derive(Debug, Clone)]
pub struct FunctionDef {
    /// Reference to the function (file, name, qualified_name).
    /// Stored directly (no Arc) since arena provides single ownership.
    pub func_ref: FunctionRef,
    /// Whether this is a method (belongs to a class)
    pub is_method: bool,
    /// Parent class name if this is a method
    pub class_name: Option<String>,
    /// Starting line number
    pub line_number: usize,
    /// Source language
    pub language: String,
    /// Simple module name (file basename without extension).
    ///
    /// For "pkg/subpkg/module.py" this would be "module".
    /// Used for Python-compatible short lookups like "module.func".
    pub simple_module: Option<String>,
}

/// Arena-based function index that stores each function once
/// and uses indices for multiple lookup strategies.
///
/// Provides O(1) lookup by name, qualified name, file+name, or class+method.
/// Handles ambiguity when multiple functions share the same name.
///
/// # Memory Efficiency
///
/// Each `FunctionDef` is stored exactly once in the `functions` arena.
/// All lookup maps use `usize` indices into this arena, reducing memory
/// from ~7x duplication (with Arc clones) to 1x + indices.
///
/// For a project with 10,000 functions:
/// - Old: 10,000 FunctionDefs + ~50,000 Arc<FunctionRef> clones
/// - New: 10,000 FunctionDefs + ~50,000 usize indices (8 bytes each)
#[derive(Debug, Default)]
pub struct FunctionIndex {
    /// Arena storing all function definitions (single storage).
    /// Each function is stored exactly once; indices reference into this Vec.
    functions: Vec<FunctionDef>,

    /// Index: function name -> indices into functions arena.
    /// Used for initial candidate lookup before disambiguation.
    by_name: FxHashMap<String, Vec<usize>>,

    /// Index: qualified name -> index into functions arena.
    ///
    /// Format varies by language:
    /// - Python: module.Class.method or module.function
    /// - TypeScript: file/Class.method or file/function
    /// - Go: package.Function or package.Type.Method
    /// - Rust: crate::module::function or crate::module::Type::method
    by_qualified: FxHashMap<String, usize>,

    /// Index: file path -> indices into functions arena.
    /// Used for resolving local/relative calls.
    by_file: FxHashMap<String, Vec<usize>>,

    /// Index: (class_name, method_name) -> indices into functions arena.
    ///
    /// Enables O(1) method lookup by class and method name, avoiding
    /// full scan of all definitions. Multiple entries possible when
    /// same class/method name exists in different files.
    by_class_method: FxHashMap<(String, String), Vec<usize>>,

    /// Index: (simple_module, func_name) -> indices into functions arena.
    ///
    /// Simple module is the file basename without extension (e.g., "module" from
    /// "pkg/subpkg/module.py"). This enables lookups like "module.func" to work
    /// even when the full qualified name is "pkg.subpkg.module.func".
    ///
    /// This matches Python's 4-key indexing strategy:
    /// 1. (module_name, func_name) - full module path
    /// 2. (simple_module, func_name) - basename only (THIS FIELD)
    /// 3. "module_name.func_name" - string key in by_qualified
    /// 4. "simple_module.func_name" - string key in by_qualified
    by_simple_module: FxHashMap<(String, String), Vec<usize>>,

    /// Statistics for debugging
    pub stats: IndexStats,
}

/// Index building statistics.
#[derive(Debug, Default, Clone)]
pub struct IndexStats {
    /// Total files processed
    pub files_processed: usize,
    /// Files that failed to parse
    pub parse_errors: usize,
    /// Total functions indexed
    pub functions_indexed: usize,
    /// Total methods indexed
    pub methods_indexed: usize,
}

/// Result of extracting functions from a single file.
struct FileExtraction {
    functions: Vec<FunctionDef>,
}

impl FunctionIndex {
    /// Build index from a list of source files using parallel extraction.
    ///
    /// Uses rayon for parallel file processing, then merges results.
    ///
    /// # Arguments
    /// * `files` - List of source file paths to index
    ///
    /// # Returns
    /// * `Result<Self>` - Built index or error
    pub fn build(files: &[PathBuf]) -> Result<Self> {
        Self::build_with_root(files, None)
    }

    /// Build index with an explicit project root for relative path calculation.
    ///
    /// # Arguments
    /// * `files` - List of source file paths to index
    /// * `root` - Optional project root for computing relative paths
    ///
    /// # Returns
    /// * `Result<Self>` - Built index or error
    pub fn build_with_root(files: &[PathBuf], root: Option<&Path>) -> Result<Self> {
        let mut index = Self::default();

        // Extract functions in parallel
        let results: Vec<FileExtraction> = files
            .par_iter()
            .filter_map(|path| {
                match extract_functions_from_file(path, root) {
                    Ok(extraction) => Some(extraction),
                    Err(_) => {
                        // Parse errors are expected for some files
                        None
                    }
                }
            })
            .collect();

        // Track parse errors (files that didn't produce results)
        let successful_files = results.len();
        index.stats.parse_errors = files.len().saturating_sub(successful_files);
        index.stats.files_processed = successful_files;

        // Merge results into index
        for extraction in results {
            for func_def in extraction.functions {
                index.insert(func_def);
            }
        }

        Ok(index)
    }

    /// Insert a function definition into the arena and all indexes.
    ///
    /// Creates multiple lookup indices per function:
    /// 1. by_name: function name -> arena indices
    /// 2. by_qualified: "module.func" -> arena index
    /// 3. by_file: file path -> arena indices
    /// 4. by_class_method: (class, method) -> arena indices
    /// 5. by_simple_module: (simple_module, func) -> arena indices
    ///
    /// Each function is stored exactly once in the arena; indices are O(1) to store.
    fn insert(&mut self, func_def: FunctionDef) {
        let idx = self.functions.len();
        let name = func_def.func_ref.name.clone();
        let file = func_def.func_ref.file.clone();

        // Update statistics
        if func_def.is_method {
            self.stats.methods_indexed += 1;
        } else {
            self.stats.functions_indexed += 1;
        }

        // Index by simple name
        self.by_name.entry(name.clone()).or_default().push(idx);

        // Index by qualified name (full module path)
        if let Some(ref qname) = func_def.func_ref.qualified_name {
            self.by_qualified.insert(qname.clone(), idx);
        }

        // Index by simple module (Python compatibility: "module.func" lookups)
        if let Some(ref simple_module) = func_def.simple_module {
            // Add to by_simple_module: (simple_module, func_name) -> Vec<usize>
            let key = (simple_module.clone(), name.clone());
            self.by_simple_module.entry(key).or_default().push(idx);

            // Also add "simple_module.func_name" to by_qualified for string lookups
            // This matches Python's: index[f"{simple_module}.{node.name}"] = str(rel_path)
            //
            // BUG FIX: Skip simple_qname for nested class methods and nested classes.
            // For nested items, the simple_qname loses context and creates ambiguous entries.
            // Example: nested.Outer.Middle.Inner -> simple: nested.Inner (WRONG, loses path)
            //
            // Nesting detection:
            // - For methods (is_method=true): nested if class_name contains a dot (e.g., "Outer.Middle")
            // - For classes (is_method=false): nested if class_name is Some (parent class exists)
            let is_nested_item = if func_def.is_method {
                func_def
                    .class_name
                    .as_ref()
                    .is_some_and(|c| c.contains('.'))
            } else {
                func_def.class_name.is_some()
            };

            if !is_nested_item {
                let simple_qname =
                    build_simple_qualified_name(simple_module, &name, &func_def.language);
                // Only insert if different from full qualified name to avoid overwrite
                if func_def.func_ref.qualified_name.as_ref() != Some(&simple_qname) {
                    // Don't overwrite if a more specific definition exists
                    self.by_qualified.entry(simple_qname).or_insert(idx);
                }
            }
        }

        // Index by file
        self.by_file.entry(file).or_default().push(idx);

        // Index by (class_name, method_name) for O(1) method lookup
        if func_def.is_method {
            if let Some(ref class_name) = func_def.class_name {
                let key = (class_name.clone(), name.clone());
                self.by_class_method.entry(key).or_default().push(idx);
            }
        }

        // Store function in arena (must be last, after all borrows of func_def)
        self.functions.push(func_def);
    }

    /// Look up all functions with a given simple name.
    ///
    /// Returns all functions matching the name, which may be in different
    /// files or classes. Use `lookup_qualified` or `lookup_in_file` for
    /// more precise lookups.
    ///
    /// # Arguments
    /// * `name` - Simple function name (without module/class prefix)
    ///
    /// # Returns
    /// * `Vec<&FunctionRef>` - All matching function references
    pub fn lookup(&self, name: &str) -> Vec<&FunctionRef> {
        self.by_name
            .get(name)
            .map(|indices| {
                indices
                    .iter()
                    .map(|&idx| &self.functions[idx].func_ref)
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Look up a function by its fully qualified name.
    ///
    /// # Arguments
    /// * `qname` - Fully qualified name (e.g., "module.Class.method")
    ///
    /// # Returns
    /// * `Option<&FunctionRef>` - Function reference if found
    pub fn lookup_qualified(&self, qname: &str) -> Option<&FunctionRef> {
        self.by_qualified
            .get(qname)
            .map(|&idx| &self.functions[idx].func_ref)
    }

    /// Look up a function in a specific file by name.
    ///
    /// Useful for resolving calls within the same file or to known modules.
    ///
    /// # Arguments
    /// * `file` - File path (relative or absolute)
    /// * `name` - Function name
    ///
    /// # Returns
    /// * `Option<&FunctionRef>` - Function reference if found
    #[allow(dead_code)]
    pub fn lookup_in_file(&self, file: &str, name: &str) -> Option<&FunctionRef> {
        self.by_file.get(file).and_then(|indices| {
            indices
                .iter()
                .find(|&&idx| self.functions[idx].func_ref.name == name)
                .map(|&idx| &self.functions[idx].func_ref)
        })
    }

    /// Look up a method in a specific class.
    ///
    /// Uses the `by_class_method` secondary index for O(1) average-case lookup.
    /// Returns all methods matching the class and method name (may exist in
    /// multiple files with the same class name).
    ///
    /// # Arguments
    /// * `class_name` - Name of the class
    /// * `method_name` - Name of the method
    ///
    /// # Returns
    /// * `Vec<&FunctionRef>` - All matching method references
    ///
    /// # Performance
    /// O(1) average case via HashMap lookup, O(k) where k is the number of
    /// methods with the same class/method name in different files.
    #[allow(dead_code)]
    pub fn lookup_method(&self, class_name: &str, method_name: &str) -> Vec<&FunctionRef> {
        let key = (class_name.to_string(), method_name.to_string());
        self.by_class_method
            .get(&key)
            .map(|indices| {
                indices
                    .iter()
                    .map(|&idx| &self.functions[idx].func_ref)
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Look up functions by simple module name and function name.
    ///
    /// Enables lookups like "module.func" even when the full qualified name
    /// is "pkg.subpkg.module.func". This matches Python's indexing strategy
    /// where both full and simple module names are indexed.
    ///
    /// # Arguments
    /// * `simple_module` - Module basename without extension (e.g., "utils", "helper")
    /// * `func_name` - Function name
    ///
    /// # Returns
    /// * `Vec<&FunctionRef>` - All matching function references
    ///
    /// # Performance
    /// O(1) average case via HashMap lookup.
    ///
    /// # Example
    /// ```ignore
    /// // For a function defined in pkg/subpkg/utils.py:
    /// index.lookup_simple("utils", "helper_func") // Finds it!
    /// ```
    #[allow(dead_code)]
    pub fn lookup_simple(&self, simple_module: &str, func_name: &str) -> Vec<&FunctionRef> {
        let key = (simple_module.to_string(), func_name.to_string());
        self.by_simple_module
            .get(&key)
            .map(|indices| {
                indices
                    .iter()
                    .map(|&idx| &self.functions[idx].func_ref)
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Get full metadata for a function by qualified name.
    ///
    /// # Arguments
    /// * `qname` - Fully qualified name
    ///
    /// # Returns
    /// * `Option<&FunctionDef>` - Full function metadata if found
    #[allow(dead_code)]
    pub fn get_definition(&self, qname: &str) -> Option<&FunctionDef> {
        self.by_qualified
            .get(qname)
            .map(|&idx| &self.functions[idx])
    }

    /// Get all functions in the index.
    #[allow(dead_code)]
    pub fn all_functions(&self) -> impl Iterator<Item = &FunctionRef> {
        self.functions.iter().map(|def| &def.func_ref)
    }

    /// Get the number of indexed functions.
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.functions.len()
    }

    /// Check if the index is empty.
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }

    /// Get all file paths in the index.
    #[allow(dead_code)]
    pub fn files(&self) -> impl Iterator<Item = &String> {
        self.by_file.keys()
    }

    /// Check if a function exists by simple name.
    #[allow(dead_code)]
    pub fn contains(&self, name: &str) -> bool {
        self.by_name.contains_key(name)
    }

    /// Get statistics about the index.
    #[allow(dead_code)]
    pub fn statistics(&self) -> &IndexStats {
        &self.stats
    }

    /// Iterate over all function definitions.
    ///
    /// Provides access to full FunctionDef metadata for all indexed functions.
    #[allow(dead_code)]
    pub fn iter(&self) -> impl Iterator<Item = &FunctionDef> {
        self.functions.iter()
    }
}

/// Recursively collect (name, line_number) tuples of all nested classes.
///
/// This is used to identify which classes in `module_info.classes` are nested
/// (and should be skipped in the top-level loop). The tree-sitter query returns
/// ALL class definitions including nested ones, but we only want to process
/// top-level classes directly - nested classes are handled via recursion.
///
/// Using (name, line_number) tuple instead of just name disambiguates classes
/// with the same name in different scopes.
fn collect_nested_class_ids<'a>(
    classes: &'a [crate::ast::types::ClassInfo],
) -> FxHashSet<(&'a str, usize)> {
    let mut nested_ids = FxHashSet::default();

    fn collect_inner<'a>(
        class: &'a crate::ast::types::ClassInfo,
        result: &mut FxHashSet<(&'a str, usize)>,
    ) {
        for inner in &class.inner_classes {
            result.insert((inner.name.as_str(), inner.line_number));
            collect_inner(inner, result);
        }
    }

    for class in classes {
        collect_inner(class, &mut nested_ids);
    }

    nested_ids
}

/// Recursively collect (name, line_number) tuples of all methods in all classes,
/// including methods in nested classes.
///
/// This is used to identify which functions in `module_info.functions` are actually
/// class methods (and should be skipped when processing top-level functions).
/// Tree-sitter queries can match methods both as class members AND as standalone
/// functions, so we need to deduplicate.
fn collect_all_method_identities<'a>(
    classes: &'a [crate::ast::types::ClassInfo],
) -> FxHashSet<(&'a str, usize)> {
    let mut method_ids = FxHashSet::default();

    fn collect_from_class<'a>(
        class: &'a crate::ast::types::ClassInfo,
        result: &mut FxHashSet<(&'a str, usize)>,
    ) {
        // Collect methods from this class
        for method in &class.methods {
            result.insert((method.name.as_str(), method.line_number));
        }
        // Recursively collect from nested classes
        for inner in &class.inner_classes {
            collect_from_class(inner, result);
        }
    }

    for class in classes {
        collect_from_class(class, &mut method_ids);
    }

    method_ids
}

/// Extract all function definitions from a single source file.
///
/// Parses the file, extracts functions and class methods, and builds
/// qualified names appropriate for the source language.
fn extract_functions_from_file(path: &PathBuf, root: Option<&Path>) -> Result<FileExtraction> {
    let module_info = AstExtractor::extract_file(path)?;

    // Compute relative path for qualified names
    let rel_path = if let Some(root) = root {
        path.strip_prefix(root)
            .map(|p| p.to_path_buf())
            .unwrap_or_else(|_| path.clone())
    } else {
        path.clone()
    };

    let file_str = path.display().to_string();
    let mut functions = Vec::new();

    // Compute module name from path
    // For Go, we need to parse the package declaration from the source file
    // using the absolute path (not rel_path) to ensure file reading works.
    let module_name = if module_info.language == "go" {
        // Use absolute path to read and parse Go package declaration
        get_go_module_name(path, None)
    } else {
        compute_module_name(&rel_path, &module_info.language)
    };

    // Compute simple module name (file basename without extension)
    // For "pkg/subpkg/module.py" this would be "module"
    let simple_module = path
        .file_stem()
        .and_then(|s| s.to_str())
        .map(|s| s.to_string());

    // First, collect all method identities from classes (including nested classes) to avoid duplicates.
    // The function_query in some languages (like Python) matches methods inside
    // classes, causing them to appear in both module_info.functions AND
    // module_info.classes[].methods. We prioritize class methods since they
    // have proper class context.
    //
    // BUG FIX: Use (name, line_number) tuple instead of just line_number for
    // deduplication. Using only line numbers is fragile because:
    // - Multiple lambdas or functions can start on the same line (minified code)
    // - Two different entities on the same line would cause one to be incorrectly skipped
    // The (name, line_number) tuple correctly identifies the same function appearing
    // in both module_info.functions and module_info.classes[].methods.
    //
    // BUG FIX: Recursively collect methods from inner_classes too. Methods in nested
    // classes were being indexed as top-level functions because they weren't in
    // method_identities.
    let method_identities: FxHashSet<(&str, usize)> =
        collect_all_method_identities(&module_info.classes);

    // Extract top-level functions (skip those that are actually class methods)
    for func in &module_info.functions {
        // Skip if this function is actually a method we'll index from a class.
        // Match by both name AND line number to avoid false positives.
        if method_identities.contains(&(func.name.as_str(), func.line_number)) {
            continue;
        }

        let qname = build_qualified_name(&module_name, None, &func.name, &module_info.language);

        // INVARIANT: is_method == true requires class_name.is_some()
        // Top-level functions are NEVER methods, regardless of what FunctionInfo.is_method
        // says. Python's is_method detection based on `self` parameter can incorrectly
        // flag standalone functions that happen to have a `self` parameter.
        functions.push(FunctionDef {
            func_ref: FunctionRef {
                file: file_str.clone(),
                name: func.name.clone(),
                qualified_name: Some(qname),
            },
            is_method: false, // Top-level functions are never methods
            class_name: None,
            line_number: func.line_number,
            language: module_info.language.clone(),
            simple_module: simple_module.clone(),
        });
    }

    // Extract class methods recursively (handles nested classes)
    //
    // Note: The tree-sitter query matches ALL class definitions including nested ones,
    // so `module_info.classes` contains both top-level and nested classes. We need to
    // identify and skip nested classes since they'll be indexed via recursion from their
    // parent class (with proper qualified names like Outer.Middle.Inner.method).
    //
    // Strategy: Build a set of all nested class names (collected from inner_classes fields),
    // then skip any class in the top-level loop that matches by (name, line_number) tuple.
    // Using line_number disambiguates classes with the same name in different scopes.
    let nested_class_ids: FxHashSet<(&str, usize)> =
        collect_nested_class_ids(&module_info.classes);

    for class in &module_info.classes {
        // Skip classes that appear as nested classes (identified by name + line number)
        // These will be indexed via recursion from their parent with proper qualified names.
        if nested_class_ids.contains(&(class.name.as_str(), class.line_number)) {
            continue;
        }

        // Also skip classes marked with nested_in: decorator (belt and suspenders)
        let is_nested_by_decorator = class.decorators.iter().any(|d| d.starts_with("nested_in:"));
        if is_nested_by_decorator {
            continue;
        }

        index_class_recursive(
            class,
            None, // No parent class for top-level classes
            &module_name,
            &file_str,
            &module_info.language,
            &simple_module,
            &mut functions,
        );
    }

    Ok(FileExtraction { functions })
}

/// Recursively index a class and all its nested classes.
///
/// This function handles nested class hierarchies by tracking the parent class path.
/// For a nested class structure like:
///
/// ```python
/// class Outer:
///     class Middle:
///         class Inner:
///             def deep_method(self): pass
/// ```
///
/// It generates qualified names like:
/// - `module.Outer`
/// - `module.Outer.Middle`
/// - `module.Outer.Middle.Inner`
/// - `module.Outer.Middle.Inner.deep_method`
///
/// # Arguments
/// * `class` - The class to index
/// * `parent_class_path` - Full path of parent classes (e.g., "Outer.Middle" for Inner)
/// * `module_name` - Module name prefix
/// * `file_str` - File path string
/// * `language` - Source language
/// * `simple_module` - Simple module name (basename without extension)
/// * `functions` - Output vector to accumulate function definitions
fn index_class_recursive(
    class: &crate::ast::types::ClassInfo,
    parent_class_path: Option<&str>,
    module_name: &str,
    file_str: &str,
    language: &str,
    simple_module: &Option<String>,
    functions: &mut Vec<FunctionDef>,
) {
    // Build the full class path including parent context
    let full_class_path = match parent_class_path {
        Some(parent) => format!("{}.{}", parent, class.name),
        None => class.name.clone(),
    };

    // Index all methods with the full class path
    for method in &class.methods {
        let qname =
            build_qualified_name(module_name, Some(&full_class_path), &method.name, language);

        functions.push(FunctionDef {
            func_ref: FunctionRef {
                file: file_str.to_string(),
                name: method.name.clone(),
                qualified_name: Some(qname),
            },
            is_method: true,
            class_name: Some(full_class_path.clone()),
            line_number: method.line_number,
            language: language.to_string(),
            simple_module: simple_module.clone(),
        });
    }

    // Index the class itself (for constructor calls)
    let class_qname = build_qualified_name(module_name, parent_class_path, &class.name, language);

    functions.push(FunctionDef {
        func_ref: FunctionRef {
            file: file_str.to_string(),
            name: class.name.clone(),
            qualified_name: Some(class_qname),
        },
        is_method: false,
        class_name: parent_class_path.map(|s| s.to_string()),
        line_number: class.line_number,
        language: language.to_string(),
        simple_module: simple_module.clone(),
    });

    // Recursively index nested classes
    for inner_class in &class.inner_classes {
        index_class_recursive(
            inner_class,
            Some(&full_class_path),
            module_name,
            file_str,
            language,
            simple_module,
            functions,
        );
    }
}

/// Extract Go package name from source code using tree-sitter.
///
/// Go package names come from the `package` declaration in the source file,
/// NOT from the directory name. This is critical for correct module naming.
///
/// # Examples
/// - `cmd/myapp/main.go` with `package main` returns Some("main")
/// - `internal/utils/helper.go` with `package utils` returns Some("utils")
///
/// # Arguments
/// * `source` - Source code bytes
///
/// # Returns
/// * `Option<String>` - Package name if found, None if parsing fails
fn extract_go_package_name(source: &[u8]) -> Option<String> {
    let mut parser = Parser::new();
    parser.set_language(&tree_sitter_go::LANGUAGE.into()).ok()?;

    let tree = parser.parse(source, None)?;
    let root = tree.root_node();

    // Go AST structure: source_file -> package_clause -> package_identifier
    // The package_clause is typically the first child of source_file
    let mut cursor = root.walk();
    for child in root.children(&mut cursor) {
        if child.kind() == "package_clause" {
            // Find the package_identifier within the package_clause
            let mut inner_cursor = child.walk();
            for inner_child in child.children(&mut inner_cursor) {
                if inner_child.kind() == "package_identifier" {
                    let name = inner_child.utf8_text(source).ok()?.to_string();
                    return Some(name);
                }
            }
        }
    }

    None
}

/// Extract Go package name with fallback to directory name.
///
/// Attempts to parse the package declaration from the source file.
/// Falls back to the parent directory name if parsing fails.
///
/// # Arguments
/// * `path` - Path to the Go source file
/// * `source` - Source code bytes (optional, read from file if None)
///
/// # Returns
/// * `String` - Package name (from source or fallback)
fn get_go_module_name(path: &Path, source: Option<&[u8]>) -> String {
    // Try to extract from source
    let package_name = match source {
        Some(src) => extract_go_package_name(src),
        None => {
            // Read file if source not provided
            std::fs::read(path)
                .ok()
                .and_then(|bytes| extract_go_package_name(&bytes))
        }
    };

    if let Some(name) = package_name {
        return name;
    }

    // Fallback: use directory name (original behavior)
    path.parent()
        .and_then(|p| p.file_name())
        .and_then(|n| n.to_str())
        .unwrap_or("main")
        .to_string()
}

/// Compute module name from file path based on language conventions.
///
/// - Python: path/to/module.py -> path.to.module
/// - TypeScript: path/to/module.ts -> path/to/module
/// - Go: package name from `package` declaration (NOT directory name)
/// - Rust: path::to::module
///
/// Note: For Go, use `compute_module_name_go` which accepts source code
/// for accurate package name extraction.
fn compute_module_name(path: &Path, language: &str) -> String {
    let stem = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("unknown");

    let parent_parts: Vec<&str> = path
        .parent()
        .map(|p| p.iter().filter_map(|c| c.to_str()).collect())
        .unwrap_or_default();

    match language {
        "python" => {
            if parent_parts.is_empty() {
                stem.to_string()
            } else {
                format!("{}.{}", parent_parts.join("."), stem)
            }
        }
        "typescript" | "javascript" => {
            if parent_parts.is_empty() {
                stem.to_string()
            } else {
                format!("{}/{}", parent_parts.join("/"), stem)
            }
        }
        "go" => {
            // Go package name comes from the `package` declaration in source.
            // Use get_go_module_name which reads the file and parses the package.
            // This is called from compute_module_name which doesn't have source,
            // so we pass None to trigger file reading.
            get_go_module_name(path, None)
        }
        "rust" => {
            if parent_parts.is_empty() {
                stem.to_string()
            } else {
                format!("{}::{}", parent_parts.join("::"), stem)
            }
        }
        "java" => {
            // Java uses package.ClassName
            if parent_parts.is_empty() {
                stem.to_string()
            } else {
                format!("{}.{}", parent_parts.join("."), stem)
            }
        }
        "c" => {
            // C doesn't have namespaces, use file stem
            stem.to_string()
        }
        _ => stem.to_string(),
    }
}

/// Build a fully qualified name for a function or method.
///
/// Format varies by language:
/// - Python: module.Class.method or module.function
/// - TypeScript: module/Class.method or module/function (module separator is /, class-method is .)
/// - Go: package.Type.Method or package.Function
/// - Rust: module::Type::method or module::function
///
/// # Performance
/// Uses pre-allocated String with exact capacity to avoid reallocation.
/// Called for every function indexed, so allocation efficiency matters.
#[inline]
fn build_qualified_name(module: &str, class: Option<&str>, name: &str, language: &str) -> String {
    // Determine separators based on language
    // TypeScript/JavaScript: module separator is /, but class.method uses .
    // Rust/C: use :: for everything
    // Others (Python, Java, Go): use . for everything
    let (module_sep, class_sep) = match language {
        "typescript" | "javascript" => ("/", "."),
        "rust" | "c" => ("::", "::"),
        _ => (".", "."), // Python, Java, Go, and default
    };

    // Calculate exact capacity needed to avoid reallocation
    let capacity = module.len()
        + module_sep.len()
        + class.map(|c| c.len() + class_sep.len()).unwrap_or(0)
        + name.len();

    let mut result = String::with_capacity(capacity);

    result.push_str(module);

    if let Some(c) = class {
        result.push_str(module_sep);
        result.push_str(c);
        result.push_str(class_sep);
        result.push_str(name);
    } else {
        result.push_str(module_sep);
        result.push_str(name);
    }

    result
}

/// Build a simple qualified name using just the module basename and function name.
///
/// This is used for Python-compatible short lookups like "module.func" where
/// "module" is just the filename without path (e.g., "utils" from "pkg/utils.py").
///
/// Format varies by language separator:
/// - Python/Java/Go: module.func
/// - TypeScript/JavaScript: module/func
/// - Rust/C: module::func
///
/// # Performance
/// Uses pre-allocated String with exact capacity to avoid reallocation.
/// Called for every function indexed, so allocation efficiency matters.
#[inline]
fn build_simple_qualified_name(simple_module: &str, name: &str, language: &str) -> String {
    let sep = match language {
        "rust" | "c" => "::",
        "typescript" | "javascript" => "/",
        _ => ".",
    };

    // Calculate exact capacity: module + separator + name
    let capacity = simple_module.len() + sep.len() + name.len();
    let mut result = String::with_capacity(capacity);

    result.push_str(simple_module);
    result.push_str(sep);
    result.push_str(name);

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::TempDir;

    fn create_temp_file(dir: &TempDir, name: &str, content: &str) -> PathBuf {
        let path = dir.path().join(name);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        let mut file = std::fs::File::create(&path).unwrap();
        file.write_all(content.as_bytes()).unwrap();
        path
    }

    #[test]
    fn test_build_index_python() {
        let dir = TempDir::new().unwrap();

        let content = r#"
def standalone():
    pass

class MyClass:
    def method(self):
        pass

async def async_func():
    pass
"#;
        let file = create_temp_file(&dir, "module.py", content);

        let index = FunctionIndex::build(&[file]).unwrap();

        // Check statistics
        assert!(index.stats.files_processed >= 1);
        assert!(index.len() >= 3); // standalone, method, async_func, MyClass

        // Lookup by simple name
        let funcs = index.lookup("standalone");
        assert!(!funcs.is_empty());

        let methods = index.lookup("method");
        assert!(!methods.is_empty());
    }

    #[test]
    fn test_build_index_typescript() {
        let dir = TempDir::new().unwrap();

        let content = r#"
function greet(name: string): void {
    console.log(name);
}

class Service {
    handle(): void {}
}

const arrow = () => {};
"#;
        let file = create_temp_file(&dir, "api.ts", content);

        let index = FunctionIndex::build(&[file]).unwrap();

        // Check we found functions
        assert!(!index.is_empty());

        let greet = index.lookup("greet");
        assert!(!greet.is_empty());
    }

    #[test]
    fn test_lookup_qualified() {
        let dir = TempDir::new().unwrap();

        let content = r#"
class Controller:
    def handle(self):
        pass
"#;
        let file = create_temp_file(&dir, "web.py", content);

        let index = FunctionIndex::build_with_root(&[file], Some(dir.path())).unwrap();

        // Should be able to look up with qualified name
        let result = index.lookup_qualified("web.Controller.handle");
        assert!(result.is_some());
    }

    #[test]
    fn test_lookup_in_file() {
        let dir = TempDir::new().unwrap();

        let content = r#"
def helper():
    pass

def main():
    helper()
"#;
        let file = create_temp_file(&dir, "script.py", content);
        let file_str = file.display().to_string();

        let index = FunctionIndex::build(&[file]).unwrap();

        let result = index.lookup_in_file(&file_str, "helper");
        assert!(result.is_some());
        assert_eq!(result.unwrap().name, "helper");
    }

    #[test]
    fn test_lookup_method() {
        let dir = TempDir::new().unwrap();

        let content = r#"
class Service:
    def process(self):
        pass

class Handler:
    def process(self):
        pass
"#;
        let file = create_temp_file(&dir, "handlers.py", content);

        let index = FunctionIndex::build(&[file]).unwrap();

        // Both classes have 'process', lookup should find both
        let all_process = index.lookup("process");
        assert_eq!(all_process.len(), 2);

        // Lookup specific class method
        let service_process = index.lookup_method("Service", "process");
        assert_eq!(service_process.len(), 1);

        let handler_process = index.lookup_method("Handler", "process");
        assert_eq!(handler_process.len(), 1);
    }

    #[test]
    fn test_multiple_files_same_function_name() {
        let dir = TempDir::new().unwrap();

        let content1 = "def helper(): pass";
        let content2 = "def helper(): pass";

        let file1 = create_temp_file(&dir, "module1.py", content1);
        let file2 = create_temp_file(&dir, "module2.py", content2);

        let index = FunctionIndex::build(&[file1, file2]).unwrap();

        // Should find both functions with same name
        let helpers = index.lookup("helper");
        assert_eq!(helpers.len(), 2);
    }

    #[test]
    fn test_compute_module_name_python() {
        let path = Path::new("pkg/subpkg/module.py");
        let module = compute_module_name(path, "python");
        assert_eq!(module, "pkg.subpkg.module");
    }

    #[test]
    fn test_compute_module_name_typescript() {
        let path = Path::new("src/utils/helpers.ts");
        let module = compute_module_name(path, "typescript");
        assert_eq!(module, "src/utils/helpers");
    }

    #[test]
    fn test_compute_module_name_rust() {
        let path = Path::new("src/lib/parser.rs");
        let module = compute_module_name(path, "rust");
        assert_eq!(module, "src::lib::parser");
    }

    #[test]
    fn test_build_qualified_name_python() {
        let qname = build_qualified_name("module", Some("Class"), "method", "python");
        assert_eq!(qname, "module.Class.method");

        let qname = build_qualified_name("module", None, "func", "python");
        assert_eq!(qname, "module.func");
    }

    #[test]
    fn test_build_qualified_name_typescript() {
        let qname = build_qualified_name("utils", Some("Helper"), "run", "typescript");
        assert_eq!(qname, "utils/Helper.run");

        let qname = build_qualified_name("utils", None, "parse", "typescript");
        assert_eq!(qname, "utils/parse");
    }

    #[test]
    fn test_build_qualified_name_rust() {
        let qname = build_qualified_name("parser", Some("Lexer"), "tokenize", "rust");
        assert_eq!(qname, "parser::Lexer::tokenize");

        let qname = build_qualified_name("utils", None, "helper", "rust");
        assert_eq!(qname, "utils::helper");
    }

    #[test]
    fn test_empty_index() {
        let index = FunctionIndex::default();

        assert!(index.is_empty());
        assert_eq!(index.len(), 0);
        assert!(index.lookup("anything").is_empty());
        assert!(index.lookup_qualified("any.thing").is_none());
    }

    #[test]
    fn test_class_indexed_for_constructors() {
        let dir = TempDir::new().unwrap();

        let content = r#"
class MyService:
    def __init__(self):
        pass
"#;
        let file = create_temp_file(&dir, "service.py", content);

        let index = FunctionIndex::build(&[file]).unwrap();

        // The class itself should be indexed (for constructor calls like MyService())
        let classes = index.lookup("MyService");
        assert!(!classes.is_empty());
    }

    #[test]
    fn test_deduplication_uses_name_and_line_not_just_line() {
        // BUG FIX TEST: Verify that deduplication uses (name, line_number) tuple
        // instead of just line_number. This prevents incorrectly skipping
        // different functions that happen to start on the same line
        // (e.g., multiple lambdas in minified code).
        let dir = TempDir::new().unwrap();

        // Python code with a method and a standalone function
        // The method should be indexed from the class, and the standalone
        // function should be indexed separately even if they share a name
        // with different semantics (method vs function).
        let content = r#"
def helper():
    """Standalone function"""
    pass

class MyClass:
    def process(self):
        """Method with unique name"""
        pass

def process_data():
    """Another standalone function"""
    pass
"#;
        let file = create_temp_file(&dir, "module.py", content);
        let index = FunctionIndex::build(&[file]).unwrap();

        // All three should be indexed:
        // 1. helper (standalone function)
        // 2. process (method of MyClass)
        // 3. process_data (standalone function)
        let helpers = index.lookup("helper");
        assert_eq!(helpers.len(), 1, "helper function should be indexed");

        let processes = index.lookup("process");
        assert_eq!(processes.len(), 1, "process method should be indexed");

        let process_datas = index.lookup("process_data");
        assert_eq!(
            process_datas.len(),
            1,
            "process_data function should be indexed"
        );

        // Also verify the method lookup works
        let method = index.lookup_method("MyClass", "process");
        assert_eq!(
            method.len(),
            1,
            "MyClass.process method should be found via method lookup"
        );
    }

    #[test]
    fn test_deduplication_skips_method_appearing_in_functions_list() {
        // Verify that methods appearing in both module_info.functions and
        // module_info.classes[].methods are correctly deduplicated (indexed
        // only once, from the class context which has proper parent info).
        let dir = TempDir::new().unwrap();

        let content = r#"
class Controller:
    def handle(self):
        pass

    def process(self):
        pass
"#;
        let file = create_temp_file(&dir, "api.py", content);
        let index = FunctionIndex::build(&[file]).unwrap();

        // Each method should appear exactly once
        let handles = index.lookup("handle");
        assert_eq!(
            handles.len(),
            1,
            "handle should appear exactly once (not duplicated)"
        );

        let processes = index.lookup("process");
        assert_eq!(
            processes.len(),
            1,
            "process should appear exactly once (not duplicated)"
        );

        // Both should be found as methods of Controller
        assert_eq!(index.lookup_method("Controller", "handle").len(), 1);
        assert_eq!(index.lookup_method("Controller", "process").len(), 1);
    }

    #[test]
    fn test_simple_module_lookup() {
        // Test Python-compatible simple module lookups (4-key indexing strategy)
        let dir = TempDir::new().unwrap();

        let content = r#"
def helper():
    pass

class Service:
    def process(self):
        pass
"#;
        // Create file in nested directory: pkg/subpkg/utils.py
        let file = create_temp_file(&dir, "pkg/subpkg/utils.py", content);

        let index = FunctionIndex::build_with_root(&[file], Some(dir.path())).unwrap();

        // 1. Full qualified name should work
        let result = index.lookup_qualified("pkg.subpkg.utils.helper");
        assert!(result.is_some(), "full qualified lookup should work");

        // 2. Simple module lookup should work (utils.helper)
        let result = index.lookup_simple("utils", "helper");
        assert!(
            !result.is_empty(),
            "simple module lookup (utils, helper) should work"
        );

        // 3. Method with simple module should also work
        let result = index.lookup_simple("utils", "process");
        assert!(
            !result.is_empty(),
            "simple module lookup for method should work"
        );
    }

    #[test]
    fn test_simple_module_typescript() {
        // Test simple module lookup for TypeScript (uses / separator)
        let dir = TempDir::new().unwrap();

        let content = r#"
function greet(name: string): void {
    console.log(name);
}
"#;
        let file = create_temp_file(&dir, "src/utils/helpers.ts", content);

        let index = FunctionIndex::build_with_root(&[file], Some(dir.path())).unwrap();

        // Simple module lookup should work
        let result = index.lookup_simple("helpers", "greet");
        assert!(
            !result.is_empty(),
            "TypeScript simple module lookup should work"
        );
    }

    #[test]
    fn test_build_simple_qualified_name_helper() {
        // Test the build_simple_qualified_name helper
        assert_eq!(
            build_simple_qualified_name("module", "func", "python"),
            "module.func"
        );
        assert_eq!(
            build_simple_qualified_name("helpers", "greet", "typescript"),
            "helpers/greet"
        );
        assert_eq!(
            build_simple_qualified_name("parser", "tokenize", "rust"),
            "parser::tokenize"
        );
    }

    // =========================================================================
    // Go package name extraction tests (BUG FIX)
    // =========================================================================

    #[test]
    fn test_extract_go_package_name_main() {
        // Test: cmd/myapp/main.go with `package main` should return "main"
        let source = br#"
package main

import "fmt"

func main() {
    fmt.Println("Hello")
}
"#;
        let result = extract_go_package_name(source);
        assert_eq!(result, Some("main".to_string()));
    }

    #[test]
    fn test_extract_go_package_name_utils() {
        // Test: internal/utils/helper.go with `package utils` should return "utils"
        let source = br#"
package utils

func Helper() string {
    return "helper"
}
"#;
        let result = extract_go_package_name(source);
        assert_eq!(result, Some("utils".to_string()));
    }

    #[test]
    fn test_extract_go_package_name_with_comment() {
        // Test: package declaration with preceding doc comment
        let source = br#"
// Package myserver implements a web server.
package myserver

import "net/http"

func Serve() {
}
"#;
        let result = extract_go_package_name(source);
        assert_eq!(result, Some("myserver".to_string()));
    }

    #[test]
    fn test_extract_go_package_name_invalid_source() {
        // Test: invalid Go source should return None
        let source = b"this is not valid go code";
        let result = extract_go_package_name(source);
        // tree-sitter is lenient, but without package clause, should return None
        assert_eq!(result, None);
    }

    #[test]
    fn test_go_module_name_uses_package_not_directory() {
        // Integration test: verify Go indexing uses package name, not directory name
        let dir = TempDir::new().unwrap();

        // Create file in cmd/myapp/ but with package main
        let content = r#"
package main

func Run() string {
    return "running"
}
"#;
        let file = create_temp_file(&dir, "cmd/myapp/main.go", content);
        let index = FunctionIndex::build_with_root(&[file], Some(dir.path())).unwrap();

        // The function should be qualified with "main" (package name),
        // NOT "myapp" (directory name)
        let result = index.lookup_qualified("main.Run");
        assert!(
            result.is_some(),
            "Function should be qualified as main.Run (from package declaration)"
        );

        // Verify it's NOT qualified as myapp.Run (directory name - wrong behavior)
        let wrong_result = index.lookup_qualified("myapp.Run");
        assert!(
            wrong_result.is_none(),
            "Function should NOT be qualified as myapp.Run (directory name)"
        );
    }

    #[test]
    fn test_go_package_utils_not_internal_utils() {
        // Integration test: internal/utils/helper.go with `package utils`
        // should be qualified as utils.Helper, not internal/utils.Helper
        let dir = TempDir::new().unwrap();

        let content = r#"
package utils

func Helper() string {
    return "helper"
}
"#;
        let file = create_temp_file(&dir, "internal/utils/helper.go", content);
        let index = FunctionIndex::build_with_root(&[file], Some(dir.path())).unwrap();

        // Should be qualified with "utils" (package name)
        let result = index.lookup_qualified("utils.Helper");
        assert!(
            result.is_some(),
            "Function should be qualified as utils.Helper (from package declaration)"
        );
    }

    #[test]
    fn test_is_method_class_name_invariant() {
        // BUG FIX TEST: Verify that is_method and class_name are always consistent.
        // INVARIANT: is_method == true => class_name.is_some()
        // This prevents the bug where top-level functions with `self` parameter
        // were incorrectly marked as methods but had class_name: None.
        let dir = TempDir::new().unwrap();

        // Python code with a standalone function that has `self` parameter
        // (unusual but valid - e.g., decorator implementations, factory functions)
        let content = r#"
def standalone_with_self(self, data):
    """A standalone function that happens to have a 'self' parameter.
    This should NOT be marked as a method because it's not inside a class."""
    return data

def normal_function():
    """A normal function without self parameter."""
    pass

class MyClass:
    def actual_method(self):
        """This IS a method inside a class."""
        pass
"#;
        let file = create_temp_file(&dir, "module.py", content);
        let index = FunctionIndex::build(&[file]).unwrap();

        // Verify the invariant: is_method == true => class_name.is_some()
        for def in index.iter() {
            if def.is_method {
                assert!(
                    def.class_name.is_some(),
                    "INVARIANT VIOLATION: {} has is_method=true but class_name=None",
                    def.func_ref
                        .qualified_name
                        .as_deref()
                        .unwrap_or(&def.func_ref.name)
                );
            }
        }

        // Specifically verify standalone_with_self is NOT marked as method
        let standalone = index.lookup("standalone_with_self");
        assert_eq!(standalone.len(), 1, "Should find standalone_with_self");

        // Get the full definition to check is_method
        let qname = standalone[0].qualified_name.as_ref().unwrap();
        let def = index.get_definition(qname).unwrap();
        assert!(
            !def.is_method,
            "standalone_with_self should NOT be marked as a method even though it has 'self' param"
        );
        assert!(
            def.class_name.is_none(),
            "standalone_with_self should not have a class_name"
        );

        // Verify actual_method IS correctly marked as a method
        let actual_method = index.lookup_method("MyClass", "actual_method");
        assert_eq!(actual_method.len(), 1, "Should find MyClass.actual_method");

        let method_qname = actual_method[0].qualified_name.as_ref().unwrap();
        let method_def = index.get_definition(method_qname).unwrap();
        assert!(
            method_def.is_method,
            "actual_method should be marked as a method"
        );
        assert_eq!(
            method_def.class_name,
            Some("MyClass".to_string()),
            "actual_method should have class_name = MyClass"
        );
    }

    #[test]
    fn test_go_package_with_method() {
        // Test Go method indexing with correct package name
        let dir = TempDir::new().unwrap();

        let content = r#"
package myservice

type Service struct {}

func (s *Service) Run() string {
    return "running"
}

func NewService() *Service {
    return &Service{}
}
"#;
        let file = create_temp_file(&dir, "pkg/server/service.go", content);
        let index = FunctionIndex::build_with_root(&[file], Some(dir.path())).unwrap();

        // Function should be qualified as myservice.NewService
        let result = index.lookup_qualified("myservice.NewService");
        assert!(
            result.is_some(),
            "Function should be qualified as myservice.NewService"
        );

        // Go receiver methods are qualified as package.MethodName
        // The receiver type is stored in decorators but NOT used as class_name
        // because Go doesn't have classes in the traditional OOP sense.
        let method_result = index.lookup_qualified("myservice.Run");
        assert!(
            method_result.is_some(),
            "Receiver method should be qualified as myservice.Run"
        );

        // Receiver method should be findable by simple name
        let methods = index.lookup("Run");
        assert!(
            !methods.is_empty(),
            "Receiver method Run should be found by simple name"
        );

        // INVARIANT: is_method == true => class_name.is_some()
        // Go receiver methods are indexed as top-level functions because Go doesn't
        // have classes. The receiver type (e.g., *Service) is stored in decorators,
        // not as class_name. Therefore, is_method should be false to maintain the
        // invariant. The receiver information is preserved in FunctionInfo.decorators.
        let run_def = index.get_definition("myservice.Run");
        assert!(
            run_def.is_some(),
            "Should have definition for myservice.Run"
        );
        let def = run_def.unwrap();

        // Go receiver methods are NOT marked as is_method because they don't have
        // class_name set (Go uses receivers, not classes)
        assert!(
            !def.is_method || def.class_name.is_some(),
            "INVARIANT: is_method=true requires class_name to be set"
        );

        // Since class_name is None for Go receivers, is_method should be false
        assert!(
            def.class_name.is_none(),
            "Go receiver methods don't have class_name (receiver is in decorators)"
        );
        assert!(
            !def.is_method,
            "Go receiver methods indexed without class_name should have is_method=false"
        );
    }

    #[test]
    fn test_nested_class_qualified_names() {
        // BUG FIX TEST: Verify nested classes produce correct qualified names.
        // For nested classes like:
        //   class Outer:
        //       class Middle:
        //           class Inner:
        //               def deep_method(self): pass
        //
        // Expected qualified names:
        //   - module.Outer
        //   - module.Outer.Middle
        //   - module.Outer.Middle.Inner
        //   - module.Outer.Middle.Inner.deep_method
        //
        // Previously buggy output: module.Inner.deep_method (missing parent class path)
        let dir = TempDir::new().unwrap();

        let content = r#"
class Outer:
    def outer_method(self):
        pass

    class Middle:
        def middle_method(self):
            pass

        class Inner:
            def deep_method(self):
                pass
"#;
        let file = create_temp_file(&dir, "nested.py", content);
        let index = FunctionIndex::build_with_root(&[file], Some(dir.path())).unwrap();

        // Verify top-level class
        let outer = index.lookup_qualified("nested.Outer");
        assert!(outer.is_some(), "Should find Outer class as nested.Outer");

        // Verify first-level nested class with FULL path
        let middle = index.lookup_qualified("nested.Outer.Middle");
        assert!(
            middle.is_some(),
            "Should find Middle class as nested.Outer.Middle (not just nested.Middle)"
        );

        // Verify deeply nested class with FULL path
        let inner = index.lookup_qualified("nested.Outer.Middle.Inner");
        assert!(
            inner.is_some(),
            "Should find Inner class as nested.Outer.Middle.Inner (not just nested.Inner)"
        );

        // Verify method in deeply nested class has FULL qualified name
        let deep_method = index.lookup_qualified("nested.Outer.Middle.Inner.deep_method");
        assert!(
            deep_method.is_some(),
            "Should find deep_method as nested.Outer.Middle.Inner.deep_method"
        );

        // Verify the method's class_name is the full path
        let method_def = index.get_definition("nested.Outer.Middle.Inner.deep_method");
        assert!(
            method_def.is_some(),
            "Should have definition for deep_method"
        );
        let def = method_def.unwrap();
        assert!(def.is_method, "deep_method should be marked as a method");
        assert_eq!(
            def.class_name,
            Some("Outer.Middle.Inner".to_string()),
            "deep_method's class_name should be the full nested path"
        );

        // Verify outer_method is correctly qualified
        let outer_method = index.lookup_qualified("nested.Outer.outer_method");
        assert!(
            outer_method.is_some(),
            "Should find outer_method as nested.Outer.outer_method"
        );

        // Verify middle_method is correctly qualified
        let middle_method = index.lookup_qualified("nested.Outer.Middle.middle_method");
        assert!(
            middle_method.is_some(),
            "Should find middle_method as nested.Outer.Middle.middle_method"
        );

        // Verify lookups don't find incorrectly qualified names
        let wrong_inner = index.lookup_qualified("nested.Inner");
        assert!(
            wrong_inner.is_none(),
            "Should NOT find Inner as nested.Inner (missing parent class path)"
        );

        let wrong_method = index.lookup_qualified("nested.Inner.deep_method");
        assert!(
            wrong_method.is_none(),
            "Should NOT find deep_method as nested.Inner.deep_method"
        );
    }

    #[test]
    fn test_nested_class_method_lookup() {
        // Verify method lookup by (class_name, method_name) works with nested classes.
        // The class_name should be the full nested path.
        let dir = TempDir::new().unwrap();

        let content = r#"
class Parent:
    class Child:
        def child_method(self):
            pass
"#;
        let file = create_temp_file(&dir, "hierarchy.py", content);
        let index = FunctionIndex::build_with_root(&[file], Some(dir.path())).unwrap();

        // lookup_method should find with full class path
        let found = index.lookup_method("Parent.Child", "child_method");
        assert!(
            !found.is_empty(),
            "Should find child_method with class_name='Parent.Child'"
        );

        // lookup_method should NOT find with incomplete class path
        let not_found = index.lookup_method("Child", "child_method");
        assert!(
            not_found.is_empty(),
            "Should NOT find child_method with class_name='Child' (needs full path)"
        );
    }
}
