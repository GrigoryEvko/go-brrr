//! AST type definitions.
//!
//! Core data structures for representing extracted code elements.

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::collections::HashMap;
use std::path::Path;

/// Default language for AST types (matches Python implementation).
fn default_language() -> String {
    "python".to_string()
}

/// Default entry type for file tree entries.
fn default_entry_type() -> String {
    "file".to_string()
}

/// Information about a function or method.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionInfo {
    /// Function name
    #[serde(default)]
    pub name: String,
    /// Parameter names (with optional type annotations)
    #[serde(default)]
    pub params: Vec<String>,
    /// Return type annotation if present
    #[serde(default)]
    pub return_type: Option<String>,
    /// Docstring or doc comment
    #[serde(default)]
    pub docstring: Option<String>,
    /// Whether this is a method (has self/this)
    #[serde(default)]
    pub is_method: bool,
    /// Whether this is an async function
    #[serde(default)]
    pub is_async: bool,
    /// Decorators/attributes applied
    #[serde(default)]
    pub decorators: Vec<String>,
    /// Starting line number (1-indexed)
    #[serde(default)]
    pub line_number: usize,
    /// Ending line number (1-indexed)
    #[serde(default)]
    pub end_line_number: Option<usize>,
    /// Source language
    #[serde(default = "default_language")]
    pub language: String,
}

impl Default for FunctionInfo {
    fn default() -> Self {
        Self {
            name: String::new(),
            params: Vec::new(),
            return_type: None,
            docstring: None,
            is_method: false,
            is_async: false,
            decorators: Vec::new(),
            line_number: 0,
            end_line_number: None,
            language: default_language(),
        }
    }
}

impl FunctionInfo {
    /// Generate a language-appropriate signature string.
    pub fn signature(&self) -> String {
        let async_prefix = if self.is_async { "async " } else { "" };
        let params = self.params.join(", ");

        match self.language.as_str() {
            "python" => {
                let ret = self
                    .return_type
                    .as_ref()
                    .map(|r| format!(" -> {}", r))
                    .unwrap_or_default();
                format!("{}def {}({}){}", async_prefix, self.name, params, ret)
            }
            "rust" => {
                let ret = self
                    .return_type
                    .as_ref()
                    .map(|r| format!(" -> {}", r))
                    .unwrap_or_default();
                format!("{}fn {}({}){}", async_prefix, self.name, params, ret)
            }
            "go" => {
                let ret = self
                    .return_type
                    .as_ref()
                    .map(|r| format!(" {}", r))
                    .unwrap_or_default();
                format!("func {}({}){}", self.name, params, ret)
            }
            "typescript" | "javascript" | "tsx" | "jsx" => {
                let ret = self
                    .return_type
                    .as_ref()
                    .map(|r| format!(": {}", r))
                    .unwrap_or_default();
                format!("{}function {}({}){}", async_prefix, self.name, params, ret)
            }
            "java" | "csharp" => {
                let ret = self.return_type.as_deref().unwrap_or("void");
                format!("{} {}({})", ret, self.name, params)
            }
            "c" | "cpp" => {
                let ret = self.return_type.as_deref().unwrap_or("void");
                format!("{} {}({})", ret, self.name, params)
            }
            "ruby" | "elixir" => {
                format!("def {}({})", self.name, params)
            }
            "kotlin" => {
                let ret = self
                    .return_type
                    .as_ref()
                    .map(|r| format!(": {}", r))
                    .unwrap_or_default();
                format!("fun {}({}){}", self.name, params, ret)
            }
            "swift" => {
                let ret = self
                    .return_type
                    .as_ref()
                    .map(|r| format!(" -> {}", r))
                    .unwrap_or_default();
                format!("func {}({}){}", self.name, params, ret)
            }
            "scala" => {
                let ret = self
                    .return_type
                    .as_ref()
                    .map(|r| format!(": {}", r))
                    .unwrap_or_default();
                format!("def {}({}){}", self.name, params, ret)
            }
            "lua" => {
                format!("function {}({})", self.name, params)
            }
            // Default to Python-style for unknown languages
            _ => {
                let ret = self
                    .return_type
                    .as_ref()
                    .map(|r| format!(" -> {}", r))
                    .unwrap_or_default();
                format!("{}def {}({}){}", async_prefix, self.name, params, ret)
            }
        }
    }
}

/// Information about a field or member variable.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FieldInfo {
    /// Field name
    #[serde(default)]
    pub name: String,
    /// Field type
    #[serde(default)]
    pub field_type: Option<String>,
    /// Visibility modifier (public/private/protected)
    #[serde(default)]
    pub visibility: Option<String>,
    /// Whether field is static
    #[serde(default)]
    pub is_static: bool,
    /// Whether field is final/const
    #[serde(default)]
    pub is_final: bool,
    /// Initial value expression (if any)
    #[serde(default)]
    pub default_value: Option<String>,
    /// Annotations/attributes
    #[serde(default)]
    pub annotations: Vec<String>,
    /// Starting line number (1-indexed)
    #[serde(default)]
    pub line_number: usize,
}

/// Information about a class or struct.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClassInfo {
    /// Class name
    #[serde(default)]
    pub name: String,
    /// Base classes / implemented interfaces
    #[serde(default)]
    pub bases: Vec<String>,
    /// Docstring or doc comment
    #[serde(default)]
    pub docstring: Option<String>,
    /// Methods defined in this class
    #[serde(default)]
    pub methods: Vec<FunctionInfo>,
    /// Fields/member variables
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub fields: Vec<FieldInfo>,
    /// BUG #7 FIX: Inner/nested classes
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub inner_classes: Vec<ClassInfo>,
    /// Decorators/attributes applied
    #[serde(default)]
    pub decorators: Vec<String>,
    /// Starting line number (1-indexed)
    #[serde(default)]
    pub line_number: usize,
    /// Ending line number (1-indexed)
    #[serde(default)]
    pub end_line_number: Option<usize>,
    /// Source language
    #[serde(default = "default_language")]
    pub language: String,
}

impl Default for ClassInfo {
    fn default() -> Self {
        Self {
            name: String::new(),
            bases: Vec::new(),
            docstring: None,
            methods: Vec::new(),
            fields: Vec::new(),
            inner_classes: Vec::new(),
            decorators: Vec::new(),
            line_number: 0,
            end_line_number: None,
            language: default_language(),
        }
    }
}

impl ClassInfo {
    /// Generate a language-appropriate class signature string.
    ///
    /// Produces idiomatic class declarations for each supported language:
    /// - Python: `class Foo(Base1, Base2)`
    /// - TypeScript/JavaScript: `class Foo extends Base`
    /// - Go: `type Foo struct`
    /// - Rust: `struct Foo`
    /// - Java/Kotlin/C#: `class Foo extends Base`
    pub fn signature(&self) -> String {
        let bases_str = self.bases.join(", ");

        match self.language.as_str() {
            "typescript" | "javascript" | "tsx" | "jsx" => {
                let mut sig = format!("class {}", self.name);
                if let Some(first_base) = self.bases.first() {
                    sig.push_str(&format!(" extends {}", first_base));
                }
                sig
            }
            "go" => format!("type {} struct", self.name),
            "rust" => format!("struct {}", self.name),
            "java" | "kotlin" | "csharp" => {
                if bases_str.is_empty() {
                    format!("class {}", self.name)
                } else {
                    format!("class {} extends {}", self.name, bases_str)
                }
            }
            _ => {
                // Python default
                if bases_str.is_empty() {
                    format!("class {}", self.name)
                } else {
                    format!("class {}({})", self.name, bases_str)
                }
            }
        }
    }
}

/// Information about an import statement.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ImportInfo {
    /// Module being imported
    #[serde(default)]
    pub module: String,
    /// Specific names imported (empty for `import module`)
    #[serde(default)]
    pub names: Vec<String>,
    /// Aliases (original_name -> alias)
    #[serde(default)]
    pub aliases: HashMap<String, String>,
    /// Whether this is a `from X import Y` style
    #[serde(default)]
    pub is_from: bool,
    /// Relative import level (0 for absolute)
    #[serde(default)]
    pub level: usize,
    /// Starting line number (1-indexed)
    #[serde(default)]
    pub line_number: usize,
    /// Visibility modifier (e.g., "pub", "pub(crate)" for Rust re-exports).
    /// None for private imports, Some(...) for public re-exports.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub visibility: Option<String>,
}

impl ImportInfo {
    /// Reconstruct the original import statement from parsed components.
    ///
    /// Generates idiomatic import syntax based on the `is_from` flag:
    /// - `from X import Y` style: `from {level_dots}{module} import {names}`
    /// - `import X` style: `import {module} [as alias]`
    ///
    /// Handles relative imports (level > 0 adds leading dots) and aliases.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use go_brrr::ast::types::ImportInfo;
    ///
    /// // from os.path import join, dirname as d
    /// let import = ImportInfo {
    ///     module: "os.path".to_string(),
    ///     names: vec!["join".to_string(), "dirname".to_string()],
    ///     aliases: [("dirname".to_string(), "d".to_string())].into_iter().collect(),
    ///     is_from: true,
    ///     level: 0,
    ///     line_number: 1,
    ///     visibility: None,
    /// };
    /// assert_eq!(import.statement(), "from os.path import join, dirname as d");
    ///
    /// // from .. import utils
    /// let relative = ImportInfo {
    ///     module: "".to_string(),
    ///     names: vec!["utils".to_string()],
    ///     aliases: HashMap::new(),
    ///     is_from: true,
    ///     level: 2,
    ///     line_number: 2,
    ///     visibility: None,
    /// };
    /// assert_eq!(relative.statement(), "from .. import utils");
    ///
    /// // import numpy as np
    /// let aliased = ImportInfo {
    ///     module: "numpy".to_string(),
    ///     names: vec![],
    ///     aliases: [("numpy".to_string(), "np".to_string())].into_iter().collect(),
    ///     is_from: false,
    ///     level: 0,
    ///     line_number: 3,
    ///     visibility: None,
    /// };
    /// assert_eq!(aliased.statement(), "import numpy as np");
    /// ```
    pub fn statement(&self) -> String {
        if self.is_from {
            let level_dots = ".".repeat(self.level);
            let names_with_aliases: Vec<String> = self
                .names
                .iter()
                .map(|name| {
                    if let Some(alias) = self.aliases.get(name) {
                        format!("{} as {}", name, alias)
                    } else {
                        name.clone()
                    }
                })
                .collect();

            if self.module.is_empty() {
                format!("from {} import {}", level_dots, names_with_aliases.join(", "))
            } else {
                format!(
                    "from {}{} import {}",
                    level_dots,
                    self.module,
                    names_with_aliases.join(", ")
                )
            }
        } else {
            // Regular import: import module [as alias]
            if let Some(alias) = self.aliases.get(&self.module) {
                format!("import {} as {}", self.module, alias)
            } else {
                format!("import {}", self.module)
            }
        }
    }
}

/// Module-level call graph information.
///
/// Tracks which functions in this module call which other functions.
/// This is a lightweight, per-module representation of call relationships,
/// distinct from the project-wide `CallGraph` in the callgraph module.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CallGraphInfo {
    /// Map of caller function name to list of called function names.
    /// Key is the caller (e.g., "process_data" or "MyClass.method"),
    /// value is a list of callees (function names being called).
    pub calls: HashMap<String, Vec<String>>,

    /// Reverse mapping: function name to list of functions that call it.
    /// Key is the callee, value is list of callers.
    /// This enables efficient reverse lookups for impact analysis.
    #[serde(default, skip_serializing_if = "HashMap::is_empty")]
    pub called_by: HashMap<String, Vec<String>>,
}

impl CallGraphInfo {
    /// Create a new empty call graph.
    ///
    /// Part of public API for library consumers building call graphs programmatically.
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a function call, updating both forward and reverse mappings.
    ///
    /// Part of public API for library consumers building call graphs programmatically.
    ///
    /// # Arguments
    /// * `caller` - The name of the calling function
    /// * `callee` - The name of the called function
    #[allow(dead_code)]
    pub fn add_call(&mut self, caller: &str, callee: &str) {
        // Update forward mapping: caller -> callees
        let callees = self.calls.entry(caller.to_string()).or_default();
        if !callees.contains(&callee.to_string()) {
            callees.push(callee.to_string());
        }

        // Update reverse mapping: callee -> callers
        let callers = self.called_by.entry(callee.to_string()).or_default();
        if !callers.contains(&caller.to_string()) {
            callers.push(caller.to_string());
        }
    }

    /// Check if the call graph is empty.
    ///
    /// Part of public API for library consumers querying call graphs.
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.calls.is_empty()
    }

    /// Get all functions called by the given function.
    ///
    /// Part of public API for library consumers querying call graphs.
    #[allow(dead_code)]
    pub fn get_callees(&self, caller: &str) -> Option<&Vec<String>> {
        self.calls.get(caller)
    }

    /// Get all functions that call the given function.
    ///
    /// Part of public API for library consumers querying call graphs.
    #[allow(dead_code)]
    pub fn get_callers(&self, callee: &str) -> Option<&Vec<String>> {
        self.called_by.get(callee)
    }
}

/// Information about a complete module/file.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleInfo {
    /// File path (serializes as "file_path" for Python compatibility)
    #[serde(rename = "file_path", default)]
    pub path: String,
    /// Detected language
    #[serde(default = "default_language")]
    pub language: String,
    /// Module-level docstring (e.g., Python module docstrings)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub docstring: Option<String>,
    /// Top-level functions
    #[serde(default)]
    pub functions: Vec<FunctionInfo>,
    /// Classes/structs
    #[serde(default)]
    pub classes: Vec<ClassInfo>,
    /// Import statements
    #[serde(default)]
    pub imports: Vec<ImportInfo>,
    /// Module-level call graph (function relationships within this module).
    /// None if not computed (call graph extraction is optional/expensive).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub call_graph: Option<CallGraphInfo>,
}

impl Default for ModuleInfo {
    fn default() -> Self {
        Self {
            path: String::new(),
            language: default_language(),
            docstring: None,
            functions: Vec::new(),
            classes: Vec::new(),
            imports: Vec::new(),
            call_graph: None,
        }
    }
}

impl ModuleInfo {
    /// Convert to dictionary format with computed signatures.
    ///
    /// Returns a complete JSON representation suitable for serialization,
    /// with all function and class signatures pre-computed. This format
    /// matches the Python `ModuleInfo.to_dict()` output for compatibility.
    ///
    /// Serialization helper for library consumers needing full module representation.
    #[allow(dead_code)]
    pub fn to_dict(&self) -> Value {
        let imports: Vec<Value> = self
            .imports
            .iter()
            .map(|i| {
                json!({
                    "module": i.module,
                    "names": i.names,
                    "aliases": i.aliases,
                    "is_from": i.is_from,
                    "level": i.level,
                    "line_number": i.line_number,
                })
            })
            .collect();

        let classes: Vec<Value> = self
            .classes
            .iter()
            .map(|c| {
                let methods: Vec<Value> = c
                    .methods
                    .iter()
                    .map(|m| {
                        json!({
                            "name": m.name,
                            "line_number": m.line_number,
                            "end_line_number": m.end_line_number,
                            "signature": m.signature(),
                            "params": m.params,
                            "return_type": m.return_type,
                            "docstring": m.docstring,
                            "is_async": m.is_async,
                            "decorators": m.decorators,
                        })
                    })
                    .collect();

                json!({
                    "name": c.name,
                    "line_number": c.line_number,
                    "end_line_number": c.end_line_number,
                    "signature": c.signature(),
                    "bases": c.bases,
                    "docstring": c.docstring,
                    "decorators": c.decorators,
                    "methods": methods,
                })
            })
            .collect();

        let functions: Vec<Value> = self
            .functions
            .iter()
            .map(|f| {
                json!({
                    "name": f.name,
                    "line_number": f.line_number,
                    "end_line_number": f.end_line_number,
                    "signature": f.signature(),
                    "params": f.params,
                    "return_type": f.return_type,
                    "docstring": f.docstring,
                    "is_async": f.is_async,
                    "decorators": f.decorators,
                })
            })
            .collect();

        let call_graph = self
            .call_graph
            .as_ref()
            .filter(|cg| !cg.calls.is_empty())
            .map(|cg| {
                json!({
                    "calls": cg.calls,
                    "called_by": cg.called_by,
                })
            })
            .unwrap_or_else(|| json!({}));

        json!({
            "file_path": self.path,
            "language": self.language,
            "docstring": self.docstring,
            "imports": imports,
            "classes": classes,
            "functions": functions,
            "call_graph": call_graph,
        })
    }

    /// Convert to compact format optimized for LLM context.
    ///
    /// Returns a condensed JSON representation that minimizes token usage
    /// while preserving essential information.
    ///
    /// Serialization helper for library consumers needing compact representation.
    #[allow(dead_code)]
    pub fn to_compact(&self) -> Value {
        self.to_compact_with_limits(200, 100)
    }

    /// Convert to compact format with custom docstring length limits.
    ///
    /// Serialization helper for library consumers needing compact representation.
    #[allow(dead_code)]
    pub fn to_compact_with_limits(
        &self,
        max_module_doc_len: usize,
        max_class_doc_len: usize,
    ) -> Value {
        let truncate = |s: &str, max_len: usize| -> String {
            if s.len() > max_len {
                format!("{}...", &s[..max_len])
            } else {
                s.to_string()
            }
        };

        let filename = Path::new(&self.path)
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| self.path.clone());

        let mut result = json!({
            "file": filename,
            "lang": self.language,
        });

        if let Some(ref doc) = self.docstring {
            result["doc"] = json!(truncate(doc, max_module_doc_len));
        }

        if !self.imports.is_empty() {
            let import_stmts: Vec<String> = self.imports.iter().map(|i| i.statement()).collect();
            result["imports"] = json!(import_stmts);
        }

        if !self.classes.is_empty() {
            let mut classes_map = serde_json::Map::new();
            for c in &self.classes {
                let mut class_info = serde_json::Map::new();

                if !c.bases.is_empty() {
                    class_info.insert("bases".to_string(), json!(c.bases));
                }

                if let Some(ref doc) = c.docstring {
                    class_info.insert("doc".to_string(), json!(truncate(doc, max_class_doc_len)));
                }

                if !c.methods.is_empty() {
                    let method_sigs: Vec<String> =
                        c.methods.iter().map(|m| m.signature()).collect();
                    class_info.insert("methods".to_string(), json!(method_sigs));
                }

                classes_map.insert(c.name.clone(), Value::Object(class_info));
            }
            result["classes"] = Value::Object(classes_map);
        }

        if !self.functions.is_empty() {
            let func_sigs: Vec<String> = self.functions.iter().map(|f| f.signature()).collect();
            result["functions"] = json!(func_sigs);
        }

        if let Some(ref cg) = self.call_graph {
            if !cg.calls.is_empty() {
                result["calls"] = json!(cg.calls);
            }
        }

        result
    }
}

/// File tree entry.
///
/// JSON schema matches Python implementation:
/// ```json
/// {
///   "name": "project",
///   "type": "dir",
///   "path": ".",
///   "children": [
///     {"name": "src", "type": "dir", "path": "src", "children": [...]},
///     {"name": "main.py", "type": "file", "path": "src/main.py"}
///   ]
/// }
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileTreeEntry {
    /// File or directory name
    #[serde(default)]
    pub name: String,
    /// Entry type: "dir" or "file" (matches Python schema)
    #[serde(rename = "type", default = "default_entry_type")]
    pub entry_type: String,
    /// Relative path from project root
    #[serde(default)]
    pub path: String,
    /// Children (for directories)
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub children: Vec<FileTreeEntry>,
    /// Indicates this directory was not expanded due to depth limit.
    /// When true, children may be incomplete or empty because max_depth was reached.
    #[serde(skip_serializing_if = "std::ops::Not::not", default)]
    pub depth_limited: bool,
}

impl Default for FileTreeEntry {
    fn default() -> Self {
        Self {
            name: String::new(),
            entry_type: default_entry_type(),
            path: String::new(),
            children: Vec::new(),
            depth_limited: false,
        }
    }
}

impl FileTreeEntry {
    /// Check if this entry is a directory.
    #[inline]
    pub fn is_dir(&self) -> bool {
        self.entry_type == "dir"
    }

    /// Create a new directory entry.
    pub fn new_dir(name: String, path: String, children: Vec<FileTreeEntry>) -> Self {
        Self {
            name,
            entry_type: "dir".to_string(),
            path,
            children,
            depth_limited: false,
        }
    }

    /// Create a new file entry.
    pub fn new_file(name: String, path: String) -> Self {
        Self {
            name,
            entry_type: "file".to_string(),
            path,
            children: vec![],
            depth_limited: false,
        }
    }

    /// Create a placeholder entry for a directory that hit the depth limit.
    ///
    /// This marker indicates the directory exists but its contents were not
    /// traversed to prevent stack overflow from deeply nested structures.
    pub fn depth_limit_reached(path: &std::path::Path, root: &std::path::Path) -> Self {
        // BUG-012 FIX: Use to_string_lossy() to preserve as much information as possible
        // for non-UTF8 paths instead of silently converting to ".".
        // The replacement character U+FFFD indicates lossy conversion occurred.
        let name = path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| ".".to_string());

        let rel_path = if path == root {
            ".".to_string()
        } else {
            path.strip_prefix(root)
                .map(|p| p.display().to_string())
                .unwrap_or_default()
        };

        Self {
            name,
            entry_type: "dir".to_string(),
            path: rel_path,
            children: vec![],
            depth_limited: true,
        }
    }
}

/// Code structure summary.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CodeStructure {
    /// Path analyzed
    #[serde(default)]
    pub path: String,
    /// Functions found
    #[serde(default)]
    pub functions: Vec<FunctionSummary>,
    /// Classes found
    #[serde(default)]
    pub classes: Vec<ClassSummary>,
    /// Number of files successfully parsed and analyzed.
    /// This is the primary metric - use this to know how many files contributed data.
    #[serde(default)]
    pub files_processed: usize,
    /// Number of files that failed AST extraction (parse errors, encoding issues, etc.).
    #[serde(default, skip_serializing_if = "is_zero")]
    pub files_failed: usize,
    /// Number of files skipped due to early termination (max_results limit) or security.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub files_skipped: usize,
    /// Total source files found matching the language filter.
    /// Equals: files_processed + files_failed + files_skipped.
    #[serde(default)]
    pub total_files: usize,
}

/// Helper for serde skip_serializing_if to omit zero values from JSON output.
fn is_zero(n: &usize) -> bool {
    *n == 0
}

/// Brief function summary for structure output.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FunctionSummary {
    #[serde(default)]
    pub name: String,
    #[serde(default)]
    pub file: String,
    #[serde(default)]
    pub line: usize,
    #[serde(default)]
    pub signature: String,
}

/// Brief class summary for structure output.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ClassSummary {
    #[serde(default)]
    pub name: String,
    #[serde(default)]
    pub file: String,
    #[serde(default)]
    pub line: usize,
    #[serde(default)]
    pub method_count: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_import_info_statement_from_import() {
        // from os.path import join, dirname
        let import = ImportInfo {
            module: "os.path".to_string(),
            names: vec!["join".to_string(), "dirname".to_string()],
            aliases: HashMap::new(),
            is_from: true,
            level: 0,
            line_number: 1,
            visibility: None,
        };
        assert_eq!(import.statement(), "from os.path import join, dirname");
    }

    #[test]
    fn test_import_info_statement_from_import_with_alias() {
        // from os.path import join, dirname as d
        let mut aliases = HashMap::new();
        aliases.insert("dirname".to_string(), "d".to_string());

        let import = ImportInfo {
            module: "os.path".to_string(),
            names: vec!["join".to_string(), "dirname".to_string()],
            aliases,
            is_from: true,
            level: 0,
            line_number: 1,
            visibility: None,
        };
        assert_eq!(import.statement(), "from os.path import join, dirname as d");
    }

    #[test]
    fn test_import_info_statement_relative_import() {
        // from .. import utils
        let import = ImportInfo {
            module: "".to_string(),
            names: vec!["utils".to_string()],
            aliases: HashMap::new(),
            is_from: true,
            level: 2,
            line_number: 1,
            visibility: None,
        };
        assert_eq!(import.statement(), "from .. import utils");
    }

    #[test]
    fn test_import_info_statement_relative_import_with_module() {
        // from ...package import module
        let import = ImportInfo {
            module: "package".to_string(),
            names: vec!["module".to_string()],
            aliases: HashMap::new(),
            is_from: true,
            level: 3,
            line_number: 1,
            visibility: None,
        };
        assert_eq!(import.statement(), "from ...package import module");
    }

    #[test]
    fn test_import_info_statement_simple_import() {
        // import os
        let import = ImportInfo {
            module: "os".to_string(),
            names: vec![],
            aliases: HashMap::new(),
            is_from: false,
            level: 0,
            line_number: 1,
            visibility: None,
        };
        assert_eq!(import.statement(), "import os");
    }

    #[test]
    fn test_import_info_statement_import_with_alias() {
        // import numpy as np
        let mut aliases = HashMap::new();
        aliases.insert("numpy".to_string(), "np".to_string());

        let import = ImportInfo {
            module: "numpy".to_string(),
            names: vec![],
            aliases,
            is_from: false,
            level: 0,
            line_number: 1,
            visibility: None,
        };
        assert_eq!(import.statement(), "import numpy as np");
    }

    #[test]
    fn test_import_info_statement_single_level_relative() {
        // from . import config
        let import = ImportInfo {
            module: "".to_string(),
            names: vec!["config".to_string()],
            aliases: HashMap::new(),
            is_from: true,
            level: 1,
            line_number: 1,
            visibility: None,
        };
        assert_eq!(import.statement(), "from . import config");
    }

    // Tests for Default trait implementations (AST-BUG-10 fix)

    #[test]
    fn test_function_info_default() {
        let func = FunctionInfo::default();
        assert!(func.name.is_empty());
        assert!(func.params.is_empty());
        assert!(func.return_type.is_none());
        assert!(func.docstring.is_none());
        assert!(!func.is_method);
        assert!(!func.is_async);
        assert!(func.decorators.is_empty());
        assert_eq!(func.line_number, 0);
        assert!(func.end_line_number.is_none());
        assert_eq!(func.language, "python"); // Custom default
    }

    #[test]
    fn test_class_info_default() {
        let class = ClassInfo::default();
        assert!(class.name.is_empty());
        assert!(class.bases.is_empty());
        assert!(class.docstring.is_none());
        assert!(class.methods.is_empty());
        assert!(class.fields.is_empty());
        assert!(class.inner_classes.is_empty());
        assert!(class.decorators.is_empty());
        assert_eq!(class.line_number, 0);
        assert!(class.end_line_number.is_none());
        assert_eq!(class.language, "python"); // Custom default
    }

    #[test]
    fn test_import_info_default() {
        let import = ImportInfo::default();
        assert!(import.module.is_empty());
        assert!(import.names.is_empty());
        assert!(import.aliases.is_empty());
        assert!(!import.is_from);
        assert_eq!(import.level, 0);
        assert_eq!(import.line_number, 0);
        assert!(import.visibility.is_none());
    }

    #[test]
    fn test_module_info_default() {
        let module = ModuleInfo::default();
        assert!(module.path.is_empty());
        assert_eq!(module.language, "python"); // Custom default
        assert!(module.docstring.is_none());
        assert!(module.functions.is_empty());
        assert!(module.classes.is_empty());
        assert!(module.imports.is_empty());
        assert!(module.call_graph.is_none());
    }

    #[test]
    fn test_field_info_default() {
        let field = FieldInfo::default();
        assert!(field.name.is_empty());
        assert!(field.field_type.is_none());
        assert!(field.visibility.is_none());
        assert!(!field.is_static);
        assert!(!field.is_final);
        assert!(field.default_value.is_none());
        assert!(field.annotations.is_empty());
        assert_eq!(field.line_number, 0);
    }

    #[test]
    fn test_file_tree_entry_default() {
        let entry = FileTreeEntry::default();
        assert!(entry.name.is_empty());
        assert_eq!(entry.entry_type, "file"); // Custom default
        assert!(entry.path.is_empty());
        assert!(entry.children.is_empty());
        assert!(!entry.depth_limited);
    }

    #[test]
    fn test_code_structure_default() {
        let structure = CodeStructure::default();
        assert!(structure.path.is_empty());
        assert!(structure.functions.is_empty());
        assert!(structure.classes.is_empty());
        assert_eq!(structure.files_processed, 0);
        assert_eq!(structure.files_failed, 0);
        assert_eq!(structure.files_skipped, 0);
        assert_eq!(structure.total_files, 0);
    }

    #[test]
    fn test_function_summary_default() {
        let summary = FunctionSummary::default();
        assert!(summary.name.is_empty());
        assert!(summary.file.is_empty());
        assert_eq!(summary.line, 0);
        assert!(summary.signature.is_empty());
    }

    #[test]
    fn test_class_summary_default() {
        let summary = ClassSummary::default();
        assert!(summary.name.is_empty());
        assert!(summary.file.is_empty());
        assert_eq!(summary.line, 0);
        assert_eq!(summary.method_count, 0);
    }

    #[test]
    fn test_deserialize_with_missing_fields() {
        // Verify serde deserialization works with missing fields
        let json = r#"{"name": "test_func"}"#;
        let func: FunctionInfo = serde_json::from_str(json).unwrap();
        assert_eq!(func.name, "test_func");
        assert_eq!(func.language, "python"); // Uses custom default
        assert!(func.params.is_empty());
    }

    #[test]
    fn test_deserialize_class_with_missing_fields() {
        let json = r#"{"name": "TestClass", "line_number": 10}"#;
        let class: ClassInfo = serde_json::from_str(json).unwrap();
        assert_eq!(class.name, "TestClass");
        assert_eq!(class.line_number, 10);
        assert_eq!(class.language, "python"); // Uses custom default
        assert!(class.methods.is_empty());
    }

    // Tests for to_dict() and to_compact() methods (AST-BUG-11 & BUG-12 fix)

    #[test]
    fn test_module_info_to_dict() {
        let module = ModuleInfo {
            path: "/src/test.py".to_string(),
            language: "python".to_string(),
            docstring: Some("Test module".to_string()),
            functions: vec![FunctionInfo {
                name: "test_func".to_string(),
                params: vec!["x: int".to_string()],
                return_type: Some("str".to_string()),
                line_number: 10,
                language: "python".to_string(),
                ..Default::default()
            }],
            classes: vec![],
            imports: vec![],
            call_graph: None,
        };

        let dict = module.to_dict();
        assert_eq!(dict["file_path"], "/src/test.py");
        assert_eq!(dict["language"], "python");
        assert_eq!(dict["docstring"], "Test module");
        assert_eq!(dict["functions"][0]["name"], "test_func");
        assert_eq!(
            dict["functions"][0]["signature"],
            "def test_func(x: int) -> str"
        );
    }

    #[test]
    fn test_module_info_to_dict_with_classes() {
        let module = ModuleInfo {
            path: "/src/api.py".to_string(),
            language: "python".to_string(),
            docstring: None,
            functions: vec![],
            classes: vec![ClassInfo {
                name: "UserController".to_string(),
                bases: vec!["BaseController".to_string()],
                docstring: Some("User API controller".to_string()),
                methods: vec![FunctionInfo {
                    name: "get_user".to_string(),
                    params: vec!["self".to_string(), "user_id: int".to_string()],
                    return_type: Some("User".to_string()),
                    is_method: true,
                    language: "python".to_string(),
                    ..Default::default()
                }],
                language: "python".to_string(),
                ..Default::default()
            }],
            imports: vec![ImportInfo {
                module: "flask".to_string(),
                names: vec!["Flask".to_string(), "request".to_string()],
                is_from: true,
                ..Default::default()
            }],
            call_graph: None,
        };

        let dict = module.to_dict();
        assert_eq!(dict["classes"][0]["name"], "UserController");
        assert_eq!(
            dict["classes"][0]["signature"],
            "class UserController(BaseController)"
        );
        assert_eq!(dict["classes"][0]["methods"][0]["name"], "get_user");
        assert_eq!(
            dict["classes"][0]["methods"][0]["signature"],
            "def get_user(self, user_id: int) -> User"
        );
        assert_eq!(dict["imports"][0]["module"], "flask");
    }

    #[test]
    fn test_module_info_to_compact() {
        let module = ModuleInfo {
            path: "/src/test.py".to_string(),
            language: "python".to_string(),
            docstring: Some("A".repeat(300)), // Long docstring
            functions: vec![FunctionInfo {
                name: "test_func".to_string(),
                params: vec!["x: int".to_string()],
                return_type: Some("str".to_string()),
                language: "python".to_string(),
                ..Default::default()
            }],
            classes: vec![ClassInfo {
                name: "TestClass".to_string(),
                bases: vec!["Base".to_string()],
                docstring: Some("B".repeat(200)), // Long docstring
                methods: vec![FunctionInfo {
                    name: "method".to_string(),
                    params: vec!["self".to_string()],
                    language: "python".to_string(),
                    ..Default::default()
                }],
                language: "python".to_string(),
                ..Default::default()
            }],
            imports: vec![ImportInfo {
                module: "os".to_string(),
                is_from: false,
                ..Default::default()
            }],
            call_graph: None,
        };

        let compact = module.to_compact();
        assert_eq!(compact["file"], "test.py");
        assert_eq!(compact["lang"], "python");
        // Module docstring truncated to 200 chars + "..."
        let doc = compact["doc"].as_str().unwrap();
        assert!(doc.len() <= 203);
        assert!(doc.ends_with("..."));
        assert_eq!(compact["imports"][0], "import os");
        assert_eq!(compact["functions"][0], "def test_func(x: int) -> str");
        // Class docstring truncated to 100 chars + "..."
        let class_doc = compact["classes"]["TestClass"]["doc"].as_str().unwrap();
        assert!(class_doc.len() <= 103);
        assert!(class_doc.ends_with("..."));
        assert_eq!(compact["classes"]["TestClass"]["bases"][0], "Base");
        assert_eq!(
            compact["classes"]["TestClass"]["methods"][0],
            "def method(self)"
        );
    }

    #[test]
    fn test_module_info_to_compact_with_call_graph() {
        let mut cg = CallGraphInfo::new();
        cg.add_call("main", "process_data");
        cg.add_call("main", "cleanup");

        let module = ModuleInfo {
            path: "/src/main.py".to_string(),
            language: "python".to_string(),
            docstring: None,
            functions: vec![
                FunctionInfo {
                    name: "main".to_string(),
                    language: "python".to_string(),
                    ..Default::default()
                },
                FunctionInfo {
                    name: "process_data".to_string(),
                    language: "python".to_string(),
                    ..Default::default()
                },
            ],
            classes: vec![],
            imports: vec![],
            call_graph: Some(cg),
        };

        let compact = module.to_compact();
        assert!(compact["calls"]["main"].as_array().is_some());
        let calls = compact["calls"]["main"].as_array().unwrap();
        assert!(calls.iter().any(|v| v == "process_data"));
        assert!(calls.iter().any(|v| v == "cleanup"));
    }

    #[test]
    fn test_module_info_to_compact_custom_limits() {
        let module = ModuleInfo {
            path: "/src/test.py".to_string(),
            language: "python".to_string(),
            docstring: Some("A".repeat(100)), // 100 chars
            functions: vec![],
            classes: vec![ClassInfo {
                name: "TestClass".to_string(),
                docstring: Some("B".repeat(50)), // 50 chars
                language: "python".to_string(),
                ..Default::default()
            }],
            imports: vec![],
            call_graph: None,
        };

        // With default limits (200, 100), nothing truncated
        let compact = module.to_compact();
        assert!(!compact["doc"].as_str().unwrap().ends_with("..."));
        assert!(
            !compact["classes"]["TestClass"]["doc"]
                .as_str()
                .unwrap()
                .ends_with("...")
        );

        // With custom limits (50, 25), both truncated
        let compact_short = module.to_compact_with_limits(50, 25);
        assert!(compact_short["doc"].as_str().unwrap().ends_with("..."));
        assert!(compact_short["classes"]["TestClass"]["doc"]
            .as_str()
            .unwrap()
            .ends_with("..."));
    }
}
