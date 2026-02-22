//! FST015: Cross-module dependency analysis with cycle detection,
//! layered dependency enforcement, and graph visualization.
//!
//! Analyzes F* module dependencies from open/friend/include/qualified refs:
//! - Builds a project-wide dependency graph from all .fst/.fsti files
//! - Detects dependency cycles (FST009-style) via Tarjan's SCC algorithm
//! - Resolves module names to file paths (Foo.Bar -> Foo.Bar.fst)
//! - Computes transitive closures for dead module detection
//! - Exports the import graph in Graphviz DOT format (--format dot)
//! - Enforces HACL*-style layering: Spec must not depend on Impl/Hacl.Impl
//! - Detects self-dependencies, excessive fan-out, security-sensitive imports
//!
//! The layering rules follow the verified-crypto convention observed in HACL*:
//!   Spec.* (pure math) -> Hacl.Spec.* (low-level spec) -> Hacl.Impl.* (imperative)
//!   Lib.* is utility and may be imported by any layer.
//!   FStar.* is the standard library and may be imported by any layer.

use lazy_static::lazy_static;
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::Write as FmtWrite;
use std::path::{Path, PathBuf};

use super::rules::{Diagnostic, DiagnosticSeverity, Range, Rule, RuleCode};
use super::shared_patterns::{OPEN_MODULE_RE, INCLUDE_MODULE_RE, MODULE_DECL_RE};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

lazy_static! {
    /// Modules that perform I/O -- forbidden in security-critical code.
    static ref IO_MODULES: Vec<&'static str> = vec![
        "FStar.IO",
        "FStar.All",
        "FStar.Printf",
        "FStar.HyperStack.IO",
    ];

    /// RawIntTypes breaks the SEC/PUB abstraction barrier in Lib.IntTypes.
    static ref RAW_INT_MODULE: &'static str = "FStar.RawIntTypes";

    /// Security-critical module name prefixes.
    static ref SECURITY_MODULE_PREFIXES: Vec<&'static str> = vec![
        "Hacl.",
        "Crypto.",
        "Spec.",
        "Impl.",
    ];

    /// Impl-layer module prefixes.
    static ref IMPL_MODULE_PREFIXES: Vec<&'static str> = vec![
        "Hacl.Impl.",
        "Impl.",
    ];

    /// Modules providing safe buffer abstractions.
    static ref SAFE_BUFFER_MODULES: Vec<&'static str> = vec![
        "LowStar.Buffer",
        "LowStar.Monotonic.Buffer",
        "Lib.Buffer",
        "Lib.ByteBuffer",
    ];

    /// Raw/unsafe buffer access modules.
    static ref UNSAFE_BUFFER_MODULES: Vec<&'static str> = vec![
        "LowStar.BufferOps",
        "C.Loops",
    ];
}

lazy_static! {
    /// Module abbreviation: `module L = FStar.List.Tot`
    static ref MODULE_ABBREV: Regex =
        Regex::new(r"^module\s+[A-Za-z_][\w]*\s*=\s*([A-Z][\w.]*)").unwrap_or_else(|e| panic!("regex: {e}"));
    /// `let open Foo.Bar`
    static ref LET_OPEN_STMT: Regex =
        Regex::new(r"let\s+open\s+([A-Z][\w.]*)").unwrap_or_else(|e| panic!("regex: {e}"));
    /// `friend Foo.Bar`
    static ref FRIEND_STMT: Regex =
        Regex::new(r"^friend\s+([A-Z][\w.]*)").unwrap_or_else(|e| panic!("regex: {e}"));
    /// Qualified reference: `Module.Path.ident` in code bodies.
    /// Captures the full module path (everything before the last `.ident`).
    /// Anchored on word boundary to avoid matching inside strings.
    static ref QUALIFIED_REF: Regex =
        Regex::new(r"\b([A-Z][\w]*(?:\.[A-Z][\w]*)*)\.([a-z_][\w']*)").unwrap_or_else(|e| panic!("regex: {e}"));
}

// ---------------------------------------------------------------------------
// Module dependency info (per-file)
// ---------------------------------------------------------------------------

/// Module dependency information extracted from a single source file.
#[derive(Debug, Clone)]
pub struct ModuleDeps {
    /// Module name from `module X.Y.Z` declaration.
    pub name: String,
    /// Modules from `open X` statements (including `let open`).
    pub opens: Vec<String>,
    /// Modules from `friend X` statements.
    pub friends: Vec<String>,
    /// Modules from `include X` statements.
    pub includes: Vec<String>,
    /// Modules from `module Alias = X` abbreviations.
    pub abbreviations: Vec<String>,
    /// Modules referenced via qualified access (e.g., `S.bn_add` where
    /// `module S = Hacl.Spec.Bignum`). Only the alias target is stored
    /// when an abbreviation exists; otherwise the raw module path.
    pub qualified_refs: Vec<String>,
}

impl ModuleDeps {
    /// All explicit dependencies (open/friend/include/abbreviation).
    pub fn all_deps(&self) -> Vec<&str> {
        self.opens
            .iter()
            .chain(self.friends.iter())
            .chain(self.includes.iter())
            .chain(self.abbreviations.iter())
            .map(|s| s.as_str())
            .collect()
    }

    /// All dependencies including qualified refs (deduplicated).
    pub fn all_deps_with_qualified(&self) -> HashSet<&str> {
        self.all_deps()
            .into_iter()
            .chain(self.qualified_refs.iter().map(|s| s.as_str()))
            .collect()
    }

    /// Number of unique explicit dependencies (deduplicated).
    pub fn unique_dep_count(&self) -> usize {
        let deps: HashSet<&str> = self.all_deps().into_iter().collect();
        deps.len()
    }
}

// ---------------------------------------------------------------------------
// Extraction
// ---------------------------------------------------------------------------

/// Extract module dependencies from F* source content.
///
/// Parses module declaration, open/friend/include statements,
/// module abbreviations, scoped opens, and qualified references.
pub fn extract_dependencies(content: &str) -> ModuleDeps {
    let mut deps = ModuleDeps {
        name: String::new(),
        opens: Vec::new(),
        friends: Vec::new(),
        includes: Vec::new(),
        abbreviations: Vec::new(),
        qualified_refs: Vec::new(),
    };

    // First pass: collect aliases so we can resolve qualified refs.
    let mut alias_map: HashMap<String, String> = HashMap::new();

    for line in content.lines() {
        let stripped = line.trim();

        if let Some(caps) = MODULE_ABBREV.captures(stripped) {
            if let Some(m) = caps.get(1) {
                let rhs = m.as_str().to_string();
                // Extract alias name (the LHS of `module Alias = RHS`)
                if let Some(eq_pos) = stripped.find('=') {
                    let lhs = stripped[..eq_pos].trim();
                    // `module Alias` -> extract `Alias`
                    if let Some(alias) = lhs.strip_prefix("module").map(|s| s.trim()) {
                        alias_map.insert(alias.to_string(), rhs.clone());
                    }
                }
                deps.abbreviations.push(rhs);
            }
        } else if let Some(caps) = MODULE_DECL_RE.captures(stripped) {
            if deps.name.is_empty() {
                if let Some(m) = caps.get(1) {
                    deps.name = m.as_str().to_string();
                }
            }
        } else if let Some(caps) = OPEN_MODULE_RE.captures(stripped) {
            if let Some(m) = caps.get(1) {
                deps.opens.push(m.as_str().to_string());
            }
        } else if let Some(caps) = LET_OPEN_STMT.captures(stripped) {
            if let Some(m) = caps.get(1) {
                deps.opens.push(m.as_str().to_string());
            }
        } else if let Some(caps) = FRIEND_STMT.captures(stripped) {
            if let Some(m) = caps.get(1) {
                deps.friends.push(m.as_str().to_string());
            }
        } else if let Some(caps) = INCLUDE_MODULE_RE.captures(stripped) {
            if let Some(m) = caps.get(1) {
                deps.includes.push(m.as_str().to_string());
            }
        }
    }

    // Second pass: collect qualified references from code body.
    // Skip lines that are open/include/friend/module declarations.
    let explicit: HashSet<&str> = deps.all_deps().into_iter().collect();
    let mut qualified_set: HashSet<String> = HashSet::new();

    for line in content.lines() {
        let stripped = line.trim();
        // Skip declaration lines
        if stripped.starts_with("open ")
            || stripped.starts_with("module ")
            || stripped.starts_with("friend ")
            || stripped.starts_with("include ")
        {
            continue;
        }
        // Skip comment-only lines
        if stripped.starts_with("//") || stripped.starts_with("(*") {
            continue;
        }

        for caps in QUALIFIED_REF.captures_iter(line) {
            let Some(m) = caps.get(1) else { continue };
            let module_part = m.as_str();

            // Resolve alias: if `S` is an alias for `Hacl.Spec.Bignum.Addition`,
            // then `S.foo` means a dep on `Hacl.Spec.Bignum.Addition`.
            let resolved = alias_map
                .get(module_part)
                .cloned()
                .unwrap_or_else(|| module_part.to_string());

            // Only add if not already covered by explicit open/include/etc.
            if !explicit.contains(resolved.as_str()) && resolved != deps.name {
                qualified_set.insert(resolved);
            }
        }
    }

    deps.qualified_refs = qualified_set.into_iter().collect();
    deps.qualified_refs.sort();

    deps
}

/// Detect if a module depends on itself.
pub fn detect_self_dependency(deps: &ModuleDeps) -> Option<String> {
    let all: HashSet<&str> = deps.all_deps().into_iter().collect();
    if all.contains(deps.name.as_str()) {
        Some(format!("Module `{}` depends on itself", deps.name))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Cross-module dependency graph
// ---------------------------------------------------------------------------

/// A node in the dependency graph.
#[derive(Debug, Clone)]
pub struct GraphNode {
    /// Module name (e.g., `Hacl.Impl.SHA256`).
    pub name: String,
    /// Resolved file path (if found on disk).
    pub file: Option<PathBuf>,
    /// Per-file dependency info.
    pub deps: ModuleDeps,
}

/// Project-wide dependency graph built from all .fst/.fsti files.
#[derive(Debug, Clone)]
pub struct DependencyGraph {
    /// Module name -> node (sorted for deterministic output).
    pub nodes: BTreeMap<String, GraphNode>,
    /// Adjacency list: module -> set of modules it depends on.
    pub edges: BTreeMap<String, BTreeSet<String>>,
    /// Module name -> file path mapping.
    pub module_to_file: HashMap<String, PathBuf>,
}

impl DependencyGraph {
    /// Build a dependency graph from a list of (file_path, file_content) pairs.
    pub fn build(files: &[(PathBuf, String)]) -> Self {
        let mut nodes = BTreeMap::new();
        let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut module_to_file: HashMap<String, PathBuf> = HashMap::new();

        for (path, content) in files {
            let deps = extract_dependencies(content);
            if deps.name.is_empty() {
                continue;
            }

            let name = deps.name.clone();
            module_to_file.insert(name.clone(), path.clone());

            let mut dep_set = BTreeSet::new();
            for dep in deps.all_deps() {
                if dep != name {
                    dep_set.insert(dep.to_string());
                }
            }
            for dep in &deps.qualified_refs {
                if dep.as_str() != name {
                    dep_set.insert(dep.clone());
                }
            }

            edges.insert(name.clone(), dep_set);
            nodes.insert(
                name.clone(),
                GraphNode {
                    name,
                    file: Some(path.clone()),
                    deps,
                },
            );
        }

        Self {
            nodes,
            edges,
            module_to_file,
        }
    }

    /// Detect all strongly connected components (cycles) using Tarjan's algorithm.
    ///
    /// Returns only SCCs with more than one node (actual cycles).
    pub fn find_cycles(&self) -> Vec<Vec<String>> {
        let mut index_counter: usize = 0;
        let mut stack: Vec<String> = Vec::new();
        let mut on_stack: HashSet<String> = HashSet::new();
        let mut index_map: HashMap<String, usize> = HashMap::new();
        let mut lowlink: HashMap<String, usize> = HashMap::new();
        let mut sccs: Vec<Vec<String>> = Vec::new();

        for node in self.edges.keys() {
            if !index_map.contains_key(node) {
                self.tarjan_visit(
                    node,
                    &mut index_counter,
                    &mut stack,
                    &mut on_stack,
                    &mut index_map,
                    &mut lowlink,
                    &mut sccs,
                );
            }
        }

        // Only return SCCs with >1 node (true cycles).
        sccs.into_iter().filter(|scc| scc.len() > 1).collect()
    }

    #[allow(clippy::too_many_arguments)]
    fn tarjan_visit(
        &self,
        v: &str,
        index_counter: &mut usize,
        stack: &mut Vec<String>,
        on_stack: &mut HashSet<String>,
        index_map: &mut HashMap<String, usize>,
        lowlink: &mut HashMap<String, usize>,
        sccs: &mut Vec<Vec<String>>,
    ) {
        let v_index = *index_counter;
        *index_counter += 1;
        index_map.insert(v.to_string(), v_index);
        lowlink.insert(v.to_string(), v_index);
        stack.push(v.to_string());
        on_stack.insert(v.to_string());

        if let Some(neighbors) = self.edges.get(v) {
            for w in neighbors {
                if !index_map.contains_key(w.as_str()) {
                    self.tarjan_visit(w, index_counter, stack, on_stack, index_map, lowlink, sccs);
                    let w_low = lowlink.get(w.as_str()).copied().unwrap_or(0);
                    if let Some(v_low) = lowlink.get_mut(v) {
                        if w_low < *v_low {
                            *v_low = w_low;
                        }
                    }
                } else if on_stack.contains(w.as_str()) {
                    let w_idx = index_map.get(w.as_str()).copied().unwrap_or(0);
                    if let Some(v_low) = lowlink.get_mut(v) {
                        if w_idx < *v_low {
                            *v_low = w_idx;
                        }
                    }
                }
            }
        }

        if lowlink[v] == index_map[v] {
            let mut scc = Vec::new();
            while let Some(w) = stack.pop() {
                on_stack.remove(&w);
                scc.push(w.clone());
                if w == v {
                    break;
                }
            }
            scc.sort();
            sccs.push(scc);
        }
    }

    /// Compute transitive closure of dependencies for a given module.
    ///
    /// Returns all modules transitively reachable from `start`.
    pub fn transitive_deps(&self, start: &str) -> BTreeSet<String> {
        let mut visited = BTreeSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(start.to_string());

        while let Some(current) = queue.pop_front() {
            if !visited.insert(current.clone()) {
                continue;
            }
            if let Some(neighbors) = self.edges.get(&current) {
                for neighbor in neighbors {
                    if !visited.contains(neighbor) {
                        queue.push_back(neighbor.clone());
                    }
                }
            }
        }

        visited.remove(start);
        visited
    }

    /// Find modules that are never imported by any other module in the graph.
    ///
    /// These are either entry points or dead code. Modules whose name
    /// contains "Test" or "Main" are excluded (they are legitimate roots).
    pub fn find_unreferenced_modules(&self) -> Vec<String> {
        let mut referenced: HashSet<String> = HashSet::new();

        for deps in self.edges.values() {
            for dep in deps {
                referenced.insert(dep.clone());
            }
        }

        let mut unreferenced: Vec<String> = self
            .nodes
            .keys()
            .filter(|name| {
                !referenced.contains(name.as_str())
                    && !name.contains("Test")
                    && !name.contains("Main")
                    && !name.contains("test")
            })
            .cloned()
            .collect();

        unreferenced.sort();
        unreferenced
    }

    /// Export the dependency graph in Graphviz DOT format.
    ///
    /// Nodes are colored by layer:
    /// - Spec.* -> blue
    /// - Hacl.Spec.* -> cyan
    /// - Hacl.Impl.*/Impl.* -> red
    /// - Lib.* -> green
    /// - FStar.* -> gray
    /// - Other -> white
    ///
    /// Violation edges (Spec -> Impl) are drawn in red.
    pub fn to_dot(&self) -> String {
        let mut out = String::with_capacity(4096);
        let _ = writeln!(out, "digraph fstar_deps {{");
        let _ = writeln!(out, "  rankdir=LR;");
        let _ = writeln!(out, "  node [shape=box, fontname=\"monospace\", fontsize=10];");
        let _ = writeln!(out, "  edge [fontsize=8];");
        let _ = writeln!(out);

        // Emit nodes with color
        for name in self.nodes.keys() {
            let color = layer_color(name);
            let _ = writeln!(
                out,
                "  \"{}\" [style=filled, fillcolor=\"{}\"];",
                name, color
            );
        }

        let _ = writeln!(out);

        // Emit edges, highlighting violations
        for (src, deps) in &self.edges {
            for dst in deps {
                let violation = is_layer_violation(src, dst);
                if violation {
                    let _ = writeln!(
                        out,
                        "  \"{}\" -> \"{}\" [color=red, penwidth=2.0, label=\"violation\"];",
                        src, dst
                    );
                } else {
                    let _ = writeln!(out, "  \"{}\" -> \"{}\";", src, dst);
                }
            }
        }

        let _ = writeln!(out, "}}");
        out
    }

    /// Detect unnecessary transitive dependencies.
    ///
    /// If module A opens both B and C, and B already depends on C (directly or
    /// transitively), then A's explicit dependency on C may be redundant.
    ///
    /// Returns (module_name, redundant_dep, provider) triples:
    /// "module `module_name` opens `redundant_dep` but it is already reachable
    /// transitively via `provider`."
    ///
    /// Note: This is informational. In F*, explicit opens are sometimes needed
    /// to bring names into scope even when the dependency is transitive. The
    /// diagnostic helps identify candidates for cleanup, not definite bugs.
    pub fn find_unnecessary_transitive_deps(&self) -> Vec<TransitiveDep> {
        let mut results = Vec::new();

        for (module, direct_deps) in &self.edges {
            // Skip modules with very few deps -- no redundancy possible
            if direct_deps.len() < 2 {
                continue;
            }

            let direct_vec: Vec<&String> = direct_deps.iter().collect();

            for (i, dep) in direct_vec.iter().enumerate() {
                // Check if this dep is transitively reachable via another direct dep
                for (j, other_dep) in direct_vec.iter().enumerate() {
                    if i == j {
                        continue;
                    }
                    // Is `dep` reachable from `other_dep`?
                    let trans = self.transitive_deps(other_dep);
                    if trans.contains(*dep) {
                        results.push(TransitiveDep {
                            module: module.clone(),
                            redundant_dep: (*dep).clone(),
                            provider: (*other_dep).clone(),
                        });
                        break; // Only report once per redundant dep
                    }
                }
            }
        }

        results.sort_by(|a, b| a.module.cmp(&b.module).then_with(|| a.redundant_dep.cmp(&b.redundant_dep)));
        results
    }

    /// Compute fan-in (number of modules that import a given module).
    ///
    /// High fan-in modules are "popular" dependencies -- changes to them
    /// affect many downstream modules. This is useful for identifying
    /// critical modules that need extra review.
    ///
    /// Returns modules with fan-in >= `threshold`, sorted by fan-in descending.
    pub fn find_high_fan_in(&self, threshold: usize) -> Vec<FanInEntry> {
        let mut fan_in: HashMap<String, BTreeSet<String>> = HashMap::new();

        for (src, deps) in &self.edges {
            for dep in deps {
                fan_in
                    .entry(dep.clone())
                    .or_default()
                    .insert(src.clone());
            }
        }

        let mut results: Vec<FanInEntry> = fan_in
            .into_iter()
            .filter(|(_, importers)| importers.len() >= threshold)
            .map(|(module, importers)| FanInEntry {
                module,
                fan_in: importers.len(),
                importers: importers.into_iter().collect(),
            })
            .collect();

        results.sort_by(|a, b| b.fan_in.cmp(&a.fan_in).then_with(|| a.module.cmp(&b.module)));
        results
    }

    /// Detect layered dependency violations.
    ///
    /// Enforces the HACL*-style layering:
    /// - Spec.* must NOT depend on Impl.* or Hacl.Impl.*
    /// - Hacl.Spec.* must NOT depend on Hacl.Impl.*
    /// - No module should depend on a test module
    pub fn find_layer_violations(&self) -> Vec<LayerViolation> {
        let mut violations = Vec::new();

        for (src, deps) in &self.edges {
            for dst in deps {
                if is_layer_violation(src, dst) {
                    violations.push(LayerViolation {
                        source: src.clone(),
                        target: dst.clone(),
                        source_layer: classify_layer(src),
                        target_layer: classify_layer(dst),
                    });
                }
            }
        }

        violations.sort_by(|a, b| a.source.cmp(&b.source).then_with(|| a.target.cmp(&b.target)));
        violations
    }
}

/// A layering violation between two modules.
#[derive(Debug, Clone)]
pub struct LayerViolation {
    pub source: String,
    pub target: String,
    pub source_layer: ModuleLayer,
    pub target_layer: ModuleLayer,
}

/// An unnecessary transitive dependency.
#[derive(Debug, Clone)]
pub struct TransitiveDep {
    /// Module that has the redundant dependency.
    pub module: String,
    /// The dependency that may be redundant.
    pub redundant_dep: String,
    /// The other direct dependency that already transitively provides the redundant dep.
    pub provider: String,
}

/// A module with high fan-in (many importers).
#[derive(Debug, Clone)]
pub struct FanInEntry {
    /// The module that is heavily imported.
    pub module: String,
    /// Number of modules that import this one.
    pub fan_in: usize,
    /// List of modules that import this one.
    pub importers: Vec<String>,
}

// ---------------------------------------------------------------------------
// Module layering classification
// ---------------------------------------------------------------------------

/// Layer classification for F* modules following HACL* conventions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModuleLayer {
    /// Pure mathematical specification (Spec.*)
    Spec,
    /// Low-level functional specification (Hacl.Spec.*)
    HaclSpec,
    /// Imperative implementation (Hacl.Impl.*, Impl.*)
    Impl,
    /// Shared library (Lib.*)
    Lib,
    /// F* standard library (FStar.*)
    Stdlib,
    /// Test modules (*.Test.*)
    Test,
    /// Everything else
    Other,
}

impl std::fmt::Display for ModuleLayer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ModuleLayer::Spec => write!(f, "Spec"),
            ModuleLayer::HaclSpec => write!(f, "Hacl.Spec"),
            ModuleLayer::Impl => write!(f, "Impl"),
            ModuleLayer::Lib => write!(f, "Lib"),
            ModuleLayer::Stdlib => write!(f, "FStar"),
            ModuleLayer::Test => write!(f, "Test"),
            ModuleLayer::Other => write!(f, "Other"),
        }
    }
}

/// Classify a module name into its architectural layer.
pub fn classify_layer(name: &str) -> ModuleLayer {
    if name.contains(".Test.") || name.contains(".test.") || name.ends_with(".Test") {
        return ModuleLayer::Test;
    }
    // Order matters: check more specific prefixes first.
    if name.starts_with("Hacl.Impl.") || name.starts_with("Impl.") {
        ModuleLayer::Impl
    } else if name.starts_with("Hacl.Spec.") {
        ModuleLayer::HaclSpec
    } else if name.starts_with("Spec.") {
        ModuleLayer::Spec
    } else if name.starts_with("Lib.") {
        ModuleLayer::Lib
    } else if name.starts_with("FStar.") || name.starts_with("Prims") {
        ModuleLayer::Stdlib
    } else if name.starts_with("Hacl.") {
        // Hacl.* top-level API modules (e.g., Hacl.Hash.SHA2)
        // Treated as Impl layer since they wrap implementations.
        ModuleLayer::Impl
    } else {
        ModuleLayer::Other
    }
}

/// Check if a dependency from `src` to `dst` violates layering rules.
fn is_layer_violation(src: &str, dst: &str) -> bool {
    let src_layer = classify_layer(src);
    let dst_layer = classify_layer(dst);

    // Lib and Stdlib can be imported by anything -- no violation.
    if matches!(dst_layer, ModuleLayer::Lib | ModuleLayer::Stdlib | ModuleLayer::Other) {
        return false;
    }

    match (src_layer, dst_layer) {
        // Spec must not depend on any Impl
        (ModuleLayer::Spec, ModuleLayer::Impl) => true,
        (ModuleLayer::Spec, ModuleLayer::HaclSpec) => false, // Spec may ref Hacl.Spec
        // Hacl.Spec must not depend on Impl
        (ModuleLayer::HaclSpec, ModuleLayer::Impl) => true,
        // No module should depend on Test modules (except other tests)
        (src, ModuleLayer::Test) if src != ModuleLayer::Test => true,
        _ => false,
    }
}

/// Return a Graphviz fill color for a module layer.
fn layer_color(name: &str) -> &'static str {
    match classify_layer(name) {
        ModuleLayer::Spec => "#cce5ff",     // light blue
        ModuleLayer::HaclSpec => "#d4edda", // light green
        ModuleLayer::Impl => "#f8d7da",     // light red
        ModuleLayer::Lib => "#fff3cd",      // light yellow
        ModuleLayer::Stdlib => "#e2e3e5",   // light gray
        ModuleLayer::Test => "#d1ecf1",     // light cyan
        ModuleLayer::Other => "#ffffff",    // white
    }
}

// ---------------------------------------------------------------------------
// Module name to file path resolution
// ---------------------------------------------------------------------------

/// Resolve an F* module name to a file path.
///
/// F* convention: `Foo.Bar.Baz` maps to `Foo.Bar.Baz.fst` or `Foo.Bar.Baz.fsti`.
/// The file can be in any directory in the search path; the name is the file stem
/// with dots (not directory separators).
///
/// Returns the first matching path found in `search_paths`.
pub fn resolve_module_path(
    module_name: &str,
    search_paths: &[PathBuf],
) -> Option<PathBuf> {
    let fst_name = format!("{}.fst", module_name);
    let fsti_name = format!("{}.fsti", module_name);

    for dir in search_paths {
        let fst_path = dir.join(&fst_name);
        if fst_path.exists() {
            return Some(fst_path);
        }
        let fsti_path = dir.join(&fsti_name);
        if fsti_path.exists() {
            return Some(fsti_path);
        }
    }

    None
}

/// Build a module-to-file mapping by scanning directories for .fst/.fsti files.
///
/// Returns a map from module name (derived from file stem) to file path.
pub fn build_module_file_map(search_paths: &[PathBuf]) -> HashMap<String, PathBuf> {
    let mut map = HashMap::new();

    for dir in search_paths {
        if !dir.is_dir() {
            // If it is a file, extract module name from stem
            if let Some(stem) = dir.file_stem().and_then(|s| s.to_str()) {
                // Check extension
                let ext = dir.extension().and_then(|e| e.to_str());
                if matches!(ext, Some("fst") | Some("fsti")) {
                    map.entry(stem.to_string())
                        .or_insert_with(|| dir.clone());
                }
            }
            continue;
        }
        let entries = match std::fs::read_dir(dir) {
            Ok(e) => e,
            Err(_) => continue,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if !path.is_file() {
                continue;
            }
            let ext = path.extension().and_then(|e| e.to_str());
            if !matches!(ext, Some("fst") | Some("fsti")) {
                continue;
            }
            if let Some(stem) = path.file_stem().and_then(|s| s.to_str()) {
                // .fst takes priority over .fsti
                map.entry(stem.to_string())
                    .or_insert_with(|| path.clone());
            }
        }
    }

    map
}

// ---------------------------------------------------------------------------
// Single-file rule (FST015)
// ---------------------------------------------------------------------------

/// FST015: Module dependency analyzer rule with security-aware checks and
/// layered dependency enforcement.
///
/// Per-file checks (run via the `Rule` trait):
/// - Self-dependency detection
/// - Excessive dependency count (>10 unique)
/// - FStar.IO in security modules
/// - RawIntTypes in Impl modules
/// - Unsafe buffer imports without safe wrappers
/// - Layered dependency violations (Spec importing Impl)
pub struct ModuleDepsRule;

impl ModuleDepsRule {
    pub fn new() -> Self {
        Self
    }

    fn is_security_module(name: &str, file: &Path) -> bool {
        let file_str = file.to_string_lossy();
        SECURITY_MODULE_PREFIXES
            .iter()
            .any(|prefix| name.starts_with(prefix) || file_str.contains(prefix))
    }

    fn is_impl_module(name: &str) -> bool {
        IMPL_MODULE_PREFIXES
            .iter()
            .any(|prefix| name.starts_with(prefix))
    }

    /// Check for I/O modules in security-critical code.
    fn check_io_in_security_module(
        &self,
        file: &Path,
        content: &str,
        deps: &ModuleDeps,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        if deps.name.contains("Test") || deps.name.contains("test") {
            return diagnostics;
        }
        if !Self::is_security_module(&deps.name, file) {
            return diagnostics;
        }

        let all_deps: HashSet<&str> = deps.all_deps().into_iter().collect();

        for io_mod in IO_MODULES.iter() {
            if all_deps.contains(io_mod) {
                let line_num = content
                    .lines()
                    .enumerate()
                    .find(|(_, line)| line.contains(io_mod))
                    .map(|(i, _)| i + 1)
                    .unwrap_or(1);

                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST015,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "`{}` imported in security module `{}`. I/O operations can leak \
                         secret data through timing or observable side effects. \
                         Use ghost/erased logging or remove I/O from production code.",
                        io_mod, deps.name
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for RawIntTypes in Impl modules.
    fn check_raw_int_types_in_impl(
        &self,
        file: &Path,
        content: &str,
        deps: &ModuleDeps,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        if !Self::is_impl_module(&deps.name) {
            return diagnostics;
        }

        let all_deps: HashSet<&str> = deps.all_deps().into_iter().collect();

        if all_deps.contains(*RAW_INT_MODULE) {
            let line_num = content
                .lines()
                .enumerate()
                .find(|(_, line)| line.contains("RawIntTypes"))
                .map(|(i, _)| i + 1)
                .unwrap_or(1);

            diagnostics.push(Diagnostic {
                rule: RuleCode::FST015,
                severity: DiagnosticSeverity::Warning,
                file: file.to_path_buf(),
                range: Range::point(line_num, 1),
                message: format!(
                    "`FStar.RawIntTypes` imported in implementation module `{}`. \
                     This bypasses the SEC/PUB secrecy abstraction from Lib.IntTypes \
                     and can break constant-time guarantees. Use Lib.IntTypes instead.",
                    deps.name
                ),
                fix: None,
            });
        }

        diagnostics
    }

    /// Check for unsafe buffer imports without safe wrappers.
    fn check_unsafe_buffer_imports(
        &self,
        file: &Path,
        deps: &ModuleDeps,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        if !Self::is_security_module(&deps.name, file) {
            return diagnostics;
        }

        let all_deps: HashSet<&str> = deps.all_deps().into_iter().collect();

        let has_unsafe = UNSAFE_BUFFER_MODULES
            .iter()
            .any(|m| all_deps.contains(m));
        let has_safe = SAFE_BUFFER_MODULES
            .iter()
            .any(|m| all_deps.contains(m));

        if has_unsafe && !has_safe {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST015,
                severity: DiagnosticSeverity::Info,
                file: file.to_path_buf(),
                range: Range::point(1, 1),
                message: format!(
                    "Security module `{}` imports low-level buffer operations without \
                     corresponding safe buffer wrappers (LowStar.Buffer, Lib.Buffer). \
                     Safe wrappers enforce bounds checking via pre/post conditions.",
                    deps.name
                ),
                fix: None,
            });
        }

        diagnostics
    }

    /// Check for layered dependency violations in a single file.
    ///
    /// Spec modules must not import Impl modules. This catches the most
    /// common violation without requiring the full project graph.
    fn check_layer_violations(
        &self,
        file: &Path,
        content: &str,
        deps: &ModuleDeps,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let src_layer = classify_layer(&deps.name);

        // Only check Spec and HaclSpec layers for downward violations
        if !matches!(src_layer, ModuleLayer::Spec | ModuleLayer::HaclSpec) {
            return diagnostics;
        }

        for dep in deps.all_deps() {
            if is_layer_violation(&deps.name, dep) {
                let line_num = content
                    .lines()
                    .enumerate()
                    .find(|(_, line)| line.contains(dep))
                    .map(|(i, _)| i + 1)
                    .unwrap_or(1);

                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST015,
                    severity: DiagnosticSeverity::Error,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: format!(
                        "Layer violation: {} module `{}` depends on {} module `{}`. \
                         Spec modules must not depend on implementation modules. \
                         Move shared definitions to a Spec.* or Lib.* module.",
                        src_layer, deps.name,
                        classify_layer(dep), dep
                    ),
                    fix: None,
                });
            }
        }

        diagnostics
    }
}

impl Default for ModuleDepsRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for ModuleDepsRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST015
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let deps = extract_dependencies(content);

        if deps.name.is_empty() {
            return diagnostics;
        }

        // Self-dependency
        if let Some(msg) = detect_self_dependency(&deps) {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST015,
                severity: DiagnosticSeverity::Error,
                file: file.to_path_buf(),
                range: Range::point(1, 1),
                message: msg,
                fix: None,
            });
        }

        // Too many dependencies
        let total_deps = deps.unique_dep_count();
        if total_deps > 10 {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST015,
                severity: DiagnosticSeverity::Warning,
                file: file.to_path_buf(),
                range: Range::point(1, 1),
                message: format!(
                    "Module has {} dependencies - consider splitting into smaller modules",
                    total_deps
                ),
                fix: None,
            });
        }

        // Security checks
        diagnostics.extend(self.check_io_in_security_module(file, content, &deps));
        diagnostics.extend(self.check_raw_int_types_in_impl(file, content, &deps));
        diagnostics.extend(self.check_unsafe_buffer_imports(file, &deps));

        // Layer violations (per-file, no graph needed)
        diagnostics.extend(self.check_layer_violations(file, content, &deps));

        diagnostics
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // =======================================================================
    // Basic extraction tests
    // =======================================================================

    #[test]
    fn test_extract_dependencies() {
        let content = r#"
module MyModule.Test

open FStar.List
open FStar.Seq
friend MyModule.Helper
include MyModule.Base
"#;
        let deps = extract_dependencies(content);
        assert_eq!(deps.name, "MyModule.Test");
        assert_eq!(deps.opens, vec!["FStar.List", "FStar.Seq"]);
        assert_eq!(deps.friends, vec!["MyModule.Helper"]);
        assert_eq!(deps.includes, vec!["MyModule.Base"]);
        assert!(deps.abbreviations.is_empty());
    }

    #[test]
    fn test_extract_module_abbreviation() {
        let content = r#"
module Vale.Interop.X64

open FStar.Mul
module B = LowStar.Buffer
module HS = FStar.HyperStack
"#;
        let deps = extract_dependencies(content);
        assert_eq!(deps.name, "Vale.Interop.X64");
        assert_eq!(deps.opens, vec!["FStar.Mul"]);
        assert_eq!(
            deps.abbreviations,
            vec!["LowStar.Buffer", "FStar.HyperStack"]
        );
    }

    #[test]
    fn test_extract_let_open() {
        let content = r#"
module MyModule

let foo x =
  let open FStar.UInt32 in
  let open FStar.Int.Cast in
  x
"#;
        let deps = extract_dependencies(content);
        assert_eq!(deps.name, "MyModule");
        assert_eq!(deps.opens, vec!["FStar.UInt32", "FStar.Int.Cast"]);
    }

    #[test]
    fn test_module_abbreviation_does_not_corrupt_name() {
        let content = r#"
module Real.Module.Name

open FStar.Mul
module L = FStar.List.Tot
module S = FStar.Seq
"#;
        let deps = extract_dependencies(content);
        assert_eq!(deps.name, "Real.Module.Name");
        assert_eq!(deps.abbreviations, vec!["FStar.List.Tot", "FStar.Seq"]);
    }

    #[test]
    fn test_self_dependency() {
        let deps = ModuleDeps {
            name: "MyModule".to_string(),
            opens: vec!["MyModule".to_string()],
            friends: vec![],
            includes: vec![],
            abbreviations: vec![],
            qualified_refs: vec![],
        };
        assert!(detect_self_dependency(&deps).is_some());
    }

    #[test]
    fn test_no_self_dependency() {
        let deps = ModuleDeps {
            name: "MyModule".to_string(),
            opens: vec!["OtherModule".to_string()],
            friends: vec![],
            includes: vec![],
            abbreviations: vec![],
            qualified_refs: vec![],
        };
        assert!(detect_self_dependency(&deps).is_none());
    }

    #[test]
    fn test_module_deps_all_deps() {
        let deps = ModuleDeps {
            name: "Test".to_string(),
            opens: vec!["A".to_string(), "B".to_string()],
            friends: vec!["C".to_string()],
            includes: vec!["D".to_string()],
            abbreviations: vec!["E".to_string()],
            qualified_refs: vec![],
        };

        let all = deps.all_deps();
        assert_eq!(all.len(), 5);
        assert!(all.contains(&"A"));
        assert!(all.contains(&"B"));
        assert!(all.contains(&"C"));
        assert!(all.contains(&"D"));
        assert!(all.contains(&"E"));
    }

    #[test]
    fn test_unique_dep_count_deduplicates() {
        let deps = ModuleDeps {
            name: "Test".to_string(),
            opens: vec!["A".to_string(), "B".to_string()],
            friends: vec![],
            includes: vec![],
            abbreviations: vec!["A".to_string()],
            qualified_refs: vec![],
        };
        assert_eq!(deps.unique_dep_count(), 2);
    }

    #[test]
    fn test_extract_real_vale_file() {
        let content = r#"
module Vale.Interop.X64

open FStar.Mul
open Vale.Interop.Base
module B = LowStar.Buffer
module BS = Vale.X64.Machine_Semantics_s
module HS = FStar.HyperStack

let foo x =
  let open FStar.UInt32 in
  x
"#;
        let deps = extract_dependencies(content);
        assert_eq!(deps.name, "Vale.Interop.X64");
        assert_eq!(
            deps.opens,
            vec!["FStar.Mul", "Vale.Interop.Base", "FStar.UInt32"]
        );
        assert_eq!(
            deps.abbreviations,
            vec![
                "LowStar.Buffer",
                "Vale.X64.Machine_Semantics_s",
                "FStar.HyperStack"
            ]
        );
    }

    // =======================================================================
    // Qualified reference extraction
    // =======================================================================

    #[test]
    fn test_extract_qualified_refs() {
        let content = r#"
module Hacl.Impl.SHA256

open Lib.IntTypes
module S = Spec.SHA2
module B = LowStar.Buffer

let hash_block (state: B.buffer uint32) =
  let spec_result = S.update state in
  spec_result
"#;
        let deps = extract_dependencies(content);
        assert_eq!(deps.name, "Hacl.Impl.SHA256");
        // S.update resolves to Spec.SHA2, B.buffer resolves to LowStar.Buffer
        // But those are already in abbreviations, so qualified_refs should
        // NOT include them (they are already explicit deps).
        // The test verifies we don't double-count.
        let all_with_q = deps.all_deps_with_qualified();
        assert!(all_with_q.contains("Spec.SHA2"));
        assert!(all_with_q.contains("LowStar.Buffer"));
    }

    #[test]
    fn test_qualified_refs_without_alias() {
        let content = r#"
module MyModule

let x = FStar.List.Tot.length [1; 2; 3]
"#;
        let deps = extract_dependencies(content);
        // FStar.List.Tot is not opened or aliased, should appear in qualified_refs
        // The regex captures "FStar.List.Tot" as the module part before ".length"
        assert!(
            deps.qualified_refs.iter().any(|r| r.contains("FStar")),
            "Qualified ref FStar.List.Tot should be detected: {:?}",
            deps.qualified_refs
        );
    }

    // =======================================================================
    // Security checks (preserved from original)
    // =======================================================================

    #[test]
    fn test_io_in_crypto_module_warns() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Hacl.Impl.SHA256

open FStar.IO
open Lib.IntTypes
"#;
        let path = std::path::PathBuf::from("Hacl.Impl.SHA256.fst");
        let diags = rule.check(&path, content);
        assert!(
            diags
                .iter()
                .any(|d| d.message.contains("FStar.IO") && d.message.contains("security")),
            "FStar.IO in Hacl module should trigger security warning"
        );
    }

    #[test]
    fn test_io_in_test_module_ok() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Hacl.Test.SHA256

open FStar.IO
open Lib.IntTypes
"#;
        let path = std::path::PathBuf::from("Hacl.Test.SHA256.fst");
        let diags = rule.check(&path, content);
        assert!(
            !diags
                .iter()
                .any(|d| d.message.contains("FStar.IO") && d.message.contains("security")),
            "FStar.IO in Test module should NOT trigger security warning"
        );
    }

    #[test]
    fn test_io_in_non_security_module_ok() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Utils.Pretty

open FStar.IO
"#;
        let path = std::path::PathBuf::from("Utils.Pretty.fst");
        let diags = rule.check(&path, content);
        assert!(
            !diags
                .iter()
                .any(|d| d.message.contains("FStar.IO") && d.message.contains("security")),
            "FStar.IO in non-security module should NOT trigger warning"
        );
    }

    #[test]
    fn test_printf_in_security_module_warns() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Spec.Chacha20

open FStar.Printf
"#;
        let path = std::path::PathBuf::from("Spec.Chacha20.fst");
        let diags = rule.check(&path, content);
        assert!(
            diags.iter().any(|d| d.message.contains("FStar.Printf")),
            "FStar.Printf in Spec module should trigger warning"
        );
    }

    #[test]
    fn test_raw_int_types_in_impl_warns() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Hacl.Impl.Curve25519

open FStar.RawIntTypes
open Lib.IntTypes
"#;
        let path = std::path::PathBuf::from("Hacl.Impl.Curve25519.fst");
        let diags = rule.check(&path, content);
        assert!(
            diags
                .iter()
                .any(|d| d.message.contains("RawIntTypes") && d.message.contains("SEC/PUB")),
            "RawIntTypes in Impl module should trigger warning"
        );
    }

    #[test]
    fn test_raw_int_types_in_spec_ok() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Spec.Curve25519

open FStar.RawIntTypes
"#;
        let path = std::path::PathBuf::from("Spec.Curve25519.fst");
        let diags = rule.check(&path, content);
        assert!(
            !diags.iter().any(|d| d.message.contains("SEC/PUB")),
            "RawIntTypes in Spec module should NOT trigger impl-specific warning"
        );
    }

    #[test]
    fn test_unsafe_buffer_without_safe_wrapper_warns() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Hacl.Impl.Blake2

open C.Loops
"#;
        let path = std::path::PathBuf::from("Hacl.Impl.Blake2.fst");
        let diags = rule.check(&path, content);
        assert!(
            diags
                .iter()
                .any(|d| d.message.contains("buffer") && d.message.contains("safe")),
            "Unsafe buffer import without safe wrapper should trigger info"
        );
    }

    #[test]
    fn test_unsafe_buffer_with_safe_wrapper_ok() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Hacl.Impl.Blake2

open C.Loops
open LowStar.Buffer
"#;
        let path = std::path::PathBuf::from("Hacl.Impl.Blake2.fst");
        let diags = rule.check(&path, content);
        assert!(
            !diags
                .iter()
                .any(|d| d.message.contains("buffer") && d.message.contains("safe")),
            "Unsafe buffer with safe wrapper should NOT trigger info"
        );
    }

    #[test]
    fn test_is_security_module_detection() {
        assert!(ModuleDepsRule::is_security_module(
            "Hacl.Impl.SHA256",
            Path::new("test.fst")
        ));
        assert!(ModuleDepsRule::is_security_module(
            "Spec.Chacha20",
            Path::new("test.fst")
        ));
        assert!(ModuleDepsRule::is_security_module(
            "Impl.AES",
            Path::new("test.fst")
        ));
        assert!(ModuleDepsRule::is_security_module(
            "Crypto.AEAD",
            Path::new("test.fst")
        ));
        assert!(!ModuleDepsRule::is_security_module(
            "Utils.Pretty",
            Path::new("test.fst")
        ));
    }

    #[test]
    fn test_is_impl_module_detection() {
        assert!(ModuleDepsRule::is_impl_module("Hacl.Impl.SHA256"));
        assert!(ModuleDepsRule::is_impl_module("Impl.AES"));
        assert!(!ModuleDepsRule::is_impl_module("Spec.Chacha20"));
        assert!(!ModuleDepsRule::is_impl_module("Hacl.Spec.Bignum"));
    }

    // =======================================================================
    // Layer classification
    // =======================================================================

    #[test]
    fn test_classify_layer() {
        assert_eq!(classify_layer("Spec.SHA2"), ModuleLayer::Spec);
        assert_eq!(classify_layer("Spec.Agile.Hash"), ModuleLayer::Spec);
        assert_eq!(classify_layer("Hacl.Spec.SHA2.Vec256"), ModuleLayer::HaclSpec);
        assert_eq!(classify_layer("Hacl.Impl.SHA256"), ModuleLayer::Impl);
        assert_eq!(classify_layer("Impl.AES"), ModuleLayer::Impl);
        assert_eq!(classify_layer("Hacl.Hash.SHA2"), ModuleLayer::Impl);
        assert_eq!(classify_layer("Lib.IntTypes"), ModuleLayer::Lib);
        assert_eq!(classify_layer("Lib.Buffer"), ModuleLayer::Lib);
        assert_eq!(classify_layer("FStar.List.Tot"), ModuleLayer::Stdlib);
        assert_eq!(classify_layer("FStar.HyperStack"), ModuleLayer::Stdlib);
        assert_eq!(classify_layer("Prims"), ModuleLayer::Stdlib);
        assert_eq!(classify_layer("Hacl.Test.SHA256"), ModuleLayer::Test);
        assert_eq!(classify_layer("Vale.Interop"), ModuleLayer::Other);
    }

    // =======================================================================
    // Layer violation detection (per-file)
    // =======================================================================

    #[test]
    fn test_spec_importing_impl_is_violation() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Spec.BadHash

open Hacl.Impl.SHA256
"#;
        let path = std::path::PathBuf::from("Spec.BadHash.fst");
        let diags = rule.check(&path, content);
        assert!(
            diags.iter().any(|d| d.message.contains("Layer violation")),
            "Spec importing Impl should be a layer violation: {:?}",
            diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_spec_importing_stdlib_ok() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Spec.GoodHash

open FStar.Seq
open Lib.IntTypes
"#;
        let path = std::path::PathBuf::from("Spec.GoodHash.fst");
        let diags = rule.check(&path, content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Layer violation")),
            "Spec importing FStar/Lib should NOT be a violation"
        );
    }

    #[test]
    fn test_spec_importing_spec_ok() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Spec.Agile.Hash

open Spec.SHA2
open Spec.Blake2
"#;
        let path = std::path::PathBuf::from("Spec.Agile.Hash.fst");
        let diags = rule.check(&path, content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Layer violation")),
            "Spec importing Spec should NOT be a violation"
        );
    }

    #[test]
    fn test_hacl_spec_importing_impl_is_violation() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Hacl.Spec.BadBignum

open Hacl.Impl.SHA256
"#;
        let path = std::path::PathBuf::from("Hacl.Spec.BadBignum.fst");
        let diags = rule.check(&path, content);
        assert!(
            diags.iter().any(|d| d.message.contains("Layer violation")),
            "Hacl.Spec importing Hacl.Impl should be a layer violation"
        );
    }

    #[test]
    fn test_impl_importing_spec_ok() {
        let rule = ModuleDepsRule::new();
        let content = r#"
module Hacl.Impl.SHA256

open Spec.SHA2
open Hacl.Spec.SHA2
"#;
        let path = std::path::PathBuf::from("Hacl.Impl.SHA256.fst");
        let diags = rule.check(&path, content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Layer violation")),
            "Impl importing Spec should NOT be a violation"
        );
    }

    // =======================================================================
    // Dependency graph
    // =======================================================================

    fn make_graph_files() -> Vec<(PathBuf, String)> {
        vec![
            (
                PathBuf::from("Spec.SHA2.fst"),
                "module Spec.SHA2\n\nopen FStar.Seq\nopen Lib.IntTypes\n".to_string(),
            ),
            (
                PathBuf::from("Hacl.Spec.SHA2.fst"),
                "module Hacl.Spec.SHA2\n\nopen Spec.SHA2\nopen Lib.IntTypes\n".to_string(),
            ),
            (
                PathBuf::from("Hacl.Impl.SHA256.fst"),
                "module Hacl.Impl.SHA256\n\nopen Hacl.Spec.SHA2\nopen Lib.Buffer\n".to_string(),
            ),
            (
                PathBuf::from("Lib.IntTypes.fst"),
                "module Lib.IntTypes\n\nopen FStar.UInt32\n".to_string(),
            ),
        ]
    }

    #[test]
    fn test_build_dependency_graph() {
        let files = make_graph_files();
        let graph = DependencyGraph::build(&files);

        assert_eq!(graph.nodes.len(), 4);
        assert!(graph.edges.contains_key("Spec.SHA2"));
        assert!(graph.edges.contains_key("Hacl.Spec.SHA2"));
        assert!(graph.edges.contains_key("Hacl.Impl.SHA256"));

        let spec_deps = &graph.edges["Spec.SHA2"];
        assert!(spec_deps.contains("FStar.Seq"));
        assert!(spec_deps.contains("Lib.IntTypes"));
    }

    #[test]
    fn test_transitive_deps() {
        let files = make_graph_files();
        let graph = DependencyGraph::build(&files);

        let trans = graph.transitive_deps("Hacl.Impl.SHA256");
        assert!(
            trans.contains("Hacl.Spec.SHA2"),
            "Direct dep should be in transitive closure"
        );
        assert!(
            trans.contains("Spec.SHA2"),
            "Transitive dep (via Hacl.Spec.SHA2) should be included"
        );
        assert!(
            trans.contains("Lib.IntTypes"),
            "Transitive dep (via Hacl.Spec.SHA2 -> Spec.SHA2) should be included"
        );
    }

    #[test]
    fn test_no_cycles_in_acyclic_graph() {
        let files = make_graph_files();
        let graph = DependencyGraph::build(&files);
        let cycles = graph.find_cycles();
        assert!(
            cycles.is_empty(),
            "Acyclic graph should have no cycles: {:?}",
            cycles
        );
    }

    // =======================================================================
    // Cycle detection
    // =======================================================================

    #[test]
    fn test_detect_simple_cycle() {
        let files = vec![
            (
                PathBuf::from("A.fst"),
                "module A\n\nopen B\n".to_string(),
            ),
            (
                PathBuf::from("B.fst"),
                "module B\n\nopen A\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);
        let cycles = graph.find_cycles();

        assert_eq!(cycles.len(), 1, "Should detect exactly one cycle");
        let cycle = &cycles[0];
        assert!(cycle.contains(&"A".to_string()));
        assert!(cycle.contains(&"B".to_string()));
    }

    #[test]
    fn test_detect_three_node_cycle() {
        let files = vec![
            (
                PathBuf::from("A.fst"),
                "module A\n\nopen B\n".to_string(),
            ),
            (
                PathBuf::from("B.fst"),
                "module B\n\nopen C\n".to_string(),
            ),
            (
                PathBuf::from("C.fst"),
                "module C\n\nopen A\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);
        let cycles = graph.find_cycles();

        assert_eq!(cycles.len(), 1);
        let cycle = &cycles[0];
        assert_eq!(cycle.len(), 3);
        assert!(cycle.contains(&"A".to_string()));
        assert!(cycle.contains(&"B".to_string()));
        assert!(cycle.contains(&"C".to_string()));
    }

    #[test]
    fn test_no_false_cycle_from_linear_chain() {
        let files = vec![
            (
                PathBuf::from("A.fst"),
                "module A\n\nopen B\n".to_string(),
            ),
            (
                PathBuf::from("B.fst"),
                "module B\n\nopen C\n".to_string(),
            ),
            (
                PathBuf::from("C.fst"),
                "module C\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);
        let cycles = graph.find_cycles();
        assert!(cycles.is_empty(), "Linear chain should not produce cycles");
    }

    #[test]
    fn test_multiple_independent_cycles() {
        let files = vec![
            (
                PathBuf::from("A.fst"),
                "module A\n\nopen B\n".to_string(),
            ),
            (
                PathBuf::from("B.fst"),
                "module B\n\nopen A\n".to_string(),
            ),
            (
                PathBuf::from("X.fst"),
                "module X\n\nopen Y\n".to_string(),
            ),
            (
                PathBuf::from("Y.fst"),
                "module Y\n\nopen X\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);
        let cycles = graph.find_cycles();
        assert_eq!(
            cycles.len(),
            2,
            "Should detect two independent cycles: {:?}",
            cycles
        );
    }

    // =======================================================================
    // Unreferenced modules (dead code candidates)
    // =======================================================================

    #[test]
    fn test_find_unreferenced_modules() {
        let files = vec![
            (
                PathBuf::from("A.fst"),
                "module A\n\nopen B\n".to_string(),
            ),
            (
                PathBuf::from("B.fst"),
                "module B\n".to_string(),
            ),
            (
                PathBuf::from("Orphan.fst"),
                "module Orphan\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);
        let unreferenced = graph.find_unreferenced_modules();

        // A is never imported by anything (root), Orphan is never imported.
        // B is imported by A. So unreferenced = [A, Orphan].
        assert!(unreferenced.contains(&"A".to_string()));
        assert!(unreferenced.contains(&"Orphan".to_string()));
        assert!(!unreferenced.contains(&"B".to_string()));
    }

    #[test]
    fn test_test_modules_excluded_from_unreferenced() {
        let files = vec![
            (
                PathBuf::from("A.fst"),
                "module A\n".to_string(),
            ),
            (
                PathBuf::from("A.Test.fst"),
                "module A.Test\n\nopen A\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);
        let unreferenced = graph.find_unreferenced_modules();

        // A.Test is never imported but has "Test" in name -> excluded
        assert!(!unreferenced.iter().any(|n| n.contains("Test")));
    }

    // =======================================================================
    // DOT export
    // =======================================================================

    #[test]
    fn test_dot_export_basic() {
        let files = vec![
            (
                PathBuf::from("Spec.Hash.fst"),
                "module Spec.Hash\n\nopen FStar.Seq\n".to_string(),
            ),
            (
                PathBuf::from("Hacl.Impl.Hash.fst"),
                "module Hacl.Impl.Hash\n\nopen Spec.Hash\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);
        let dot = graph.to_dot();

        assert!(dot.starts_with("digraph fstar_deps {"));
        assert!(dot.contains("\"Spec.Hash\""));
        assert!(dot.contains("\"Hacl.Impl.Hash\""));
        assert!(dot.contains("\"Hacl.Impl.Hash\" -> \"Spec.Hash\""));
        assert!(dot.ends_with("}\n"));
    }

    #[test]
    fn test_dot_export_marks_violations() {
        let files = vec![
            (
                PathBuf::from("Spec.Bad.fst"),
                "module Spec.Bad\n\nopen Hacl.Impl.Foo\n".to_string(),
            ),
            (
                PathBuf::from("Hacl.Impl.Foo.fst"),
                "module Hacl.Impl.Foo\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);
        let dot = graph.to_dot();

        assert!(
            dot.contains("color=red"),
            "Violation edge should be marked red in DOT output"
        );
        assert!(
            dot.contains("violation"),
            "Violation edge should have 'violation' label"
        );
    }

    // =======================================================================
    // Graph-level layer violations
    // =======================================================================

    #[test]
    fn test_graph_layer_violations() {
        let files = vec![
            (
                PathBuf::from("Spec.Bad.fst"),
                "module Spec.Bad\n\nopen Hacl.Impl.Foo\n".to_string(),
            ),
            (
                PathBuf::from("Hacl.Impl.Foo.fst"),
                "module Hacl.Impl.Foo\n".to_string(),
            ),
            (
                PathBuf::from("Hacl.Impl.Bar.fst"),
                "module Hacl.Impl.Bar\n\nopen Spec.Bad\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);
        let violations = graph.find_layer_violations();

        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].source, "Spec.Bad");
        assert_eq!(violations[0].target, "Hacl.Impl.Foo");
        assert_eq!(violations[0].source_layer, ModuleLayer::Spec);
        assert_eq!(violations[0].target_layer, ModuleLayer::Impl);
    }

    #[test]
    fn test_no_layer_violations_in_clean_graph() {
        let files = make_graph_files();
        let graph = DependencyGraph::build(&files);
        let violations = graph.find_layer_violations();
        assert!(
            violations.is_empty(),
            "Clean HACL*-style graph should have no violations"
        );
    }

    // =======================================================================
    // Module name to file path resolution
    // =======================================================================

    #[test]
    fn test_resolve_module_path() {
        let temp_dir = tempfile::TempDir::new().unwrap();
        let fst_path = temp_dir.path().join("Spec.SHA2.fst");
        std::fs::write(&fst_path, "module Spec.SHA2\n").unwrap();

        let result = resolve_module_path("Spec.SHA2", &[temp_dir.path().to_path_buf()]);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), fst_path);
    }

    #[test]
    fn test_resolve_module_path_fsti_fallback() {
        let temp_dir = tempfile::TempDir::new().unwrap();
        let fsti_path = temp_dir.path().join("Spec.SHA2.fsti");
        std::fs::write(&fsti_path, "module Spec.SHA2\n").unwrap();

        let result = resolve_module_path("Spec.SHA2", &[temp_dir.path().to_path_buf()]);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), fsti_path);
    }

    #[test]
    fn test_resolve_module_path_not_found() {
        let temp_dir = tempfile::TempDir::new().unwrap();
        let result = resolve_module_path("Nonexistent.Module", &[temp_dir.path().to_path_buf()]);
        assert!(result.is_none());
    }

    #[test]
    fn test_build_module_file_map() {
        let temp_dir = tempfile::TempDir::new().unwrap();
        std::fs::write(temp_dir.path().join("Spec.SHA2.fst"), "").unwrap();
        std::fs::write(temp_dir.path().join("Lib.IntTypes.fsti"), "").unwrap();
        std::fs::write(temp_dir.path().join("README.md"), "").unwrap();

        let map = build_module_file_map(&[temp_dir.path().to_path_buf()]);
        assert!(map.contains_key("Spec.SHA2"));
        assert!(map.contains_key("Lib.IntTypes"));
        assert!(!map.contains_key("README"));
    }

    // =======================================================================
    // Edge cases
    // =======================================================================

    #[test]
    fn test_empty_file() {
        let deps = extract_dependencies("");
        assert!(deps.name.is_empty());
        assert!(deps.opens.is_empty());
        assert!(deps.friends.is_empty());
        assert!(deps.includes.is_empty());
        assert!(deps.abbreviations.is_empty());
        assert!(deps.qualified_refs.is_empty());
    }

    #[test]
    fn test_module_with_no_deps() {
        let content = "module Standalone\n\nlet x = 42\n";
        let deps = extract_dependencies(content);
        assert_eq!(deps.name, "Standalone");
        assert_eq!(deps.unique_dep_count(), 0);
    }

    #[test]
    fn test_graph_with_single_node() {
        let files = vec![(
            PathBuf::from("Solo.fst"),
            "module Solo\n".to_string(),
        )];
        let graph = DependencyGraph::build(&files);
        assert_eq!(graph.nodes.len(), 1);
        assert!(graph.find_cycles().is_empty());
        assert!(graph.edges["Solo"].is_empty());
    }

    #[test]
    fn test_all_deps_with_qualified_includes_everything() {
        let deps = ModuleDeps {
            name: "Test".to_string(),
            opens: vec!["A".to_string()],
            friends: vec!["B".to_string()],
            includes: vec!["C".to_string()],
            abbreviations: vec!["D".to_string()],
            qualified_refs: vec!["E".to_string(), "A".to_string()], // A is duplicate
        };
        let all = deps.all_deps_with_qualified();
        assert_eq!(all.len(), 5); // A, B, C, D, E (A deduplicated)
    }

    #[test]
    fn test_dot_output_is_valid_graphviz() {
        let files = make_graph_files();
        let graph = DependencyGraph::build(&files);
        let dot = graph.to_dot();

        // Basic structural validation
        assert!(dot.starts_with("digraph fstar_deps {"));
        assert!(dot.ends_with("}\n"));

        // Every opening brace has a closing brace (very basic syntax check)
        let opens = dot.matches('{').count();
        let closes = dot.matches('}').count();
        assert_eq!(opens, closes, "Braces must be balanced in DOT output");
    }

    #[test]
    fn test_layer_color_mapping() {
        assert_eq!(layer_color("Spec.SHA2"), "#cce5ff");
        assert_eq!(layer_color("Hacl.Spec.SHA2"), "#d4edda");
        assert_eq!(layer_color("Hacl.Impl.SHA256"), "#f8d7da");
        assert_eq!(layer_color("Lib.Buffer"), "#fff3cd");
        assert_eq!(layer_color("FStar.List"), "#e2e3e5");
        assert_eq!(layer_color("Hacl.Test.SHA256"), "#d1ecf1");
        assert_eq!(layer_color("Vale.Interop"), "#ffffff");
    }

    #[test]
    fn test_is_layer_violation_comprehensive() {
        // Spec -> Impl: violation
        assert!(is_layer_violation("Spec.SHA2", "Hacl.Impl.SHA256"));
        assert!(is_layer_violation("Spec.SHA2", "Impl.AES"));
        // Spec -> Lib: ok
        assert!(!is_layer_violation("Spec.SHA2", "Lib.IntTypes"));
        // Spec -> FStar: ok
        assert!(!is_layer_violation("Spec.SHA2", "FStar.Seq"));
        // Spec -> Spec: ok
        assert!(!is_layer_violation("Spec.SHA2", "Spec.Blake2"));
        // Spec -> HaclSpec: ok
        assert!(!is_layer_violation("Spec.SHA2", "Hacl.Spec.SHA2"));
        // HaclSpec -> Impl: violation
        assert!(is_layer_violation("Hacl.Spec.SHA2", "Hacl.Impl.SHA256"));
        // Impl -> Spec: ok
        assert!(!is_layer_violation("Hacl.Impl.SHA256", "Spec.SHA2"));
        // Any non-test -> Test: violation
        assert!(is_layer_violation("Hacl.Impl.SHA256", "Hacl.Test.SHA256"));
        // Test -> Test: ok
        assert!(!is_layer_violation("Hacl.Test.SHA256", "Hacl.Test.Utils"));
        // Other -> Impl: ok
        assert!(!is_layer_violation("Vale.Interop", "Hacl.Impl.SHA256"));
    }

    #[test]
    fn test_module_deps_display_layer() {
        assert_eq!(format!("{}", ModuleLayer::Spec), "Spec");
        assert_eq!(format!("{}", ModuleLayer::HaclSpec), "Hacl.Spec");
        assert_eq!(format!("{}", ModuleLayer::Impl), "Impl");
        assert_eq!(format!("{}", ModuleLayer::Lib), "Lib");
        assert_eq!(format!("{}", ModuleLayer::Stdlib), "FStar");
        assert_eq!(format!("{}", ModuleLayer::Test), "Test");
        assert_eq!(format!("{}", ModuleLayer::Other), "Other");
    }

    // =======================================================================
    // HACL*-style integration patterns
    // =======================================================================

    #[test]
    fn test_hacl_style_layered_project() {
        // Mimics a real HACL* project structure:
        // specs/ -> code/ (Hacl.Spec) -> code/ (Hacl.Impl)
        let files = vec![
            (
                PathBuf::from("specs/Spec.Chacha20.fst"),
                "module Spec.Chacha20\n\nopen FStar.Mul\nopen FStar.Seq\nopen Lib.IntTypes\nopen Lib.ByteSequence\n".to_string(),
            ),
            (
                PathBuf::from("code/Hacl.Spec.Chacha20.fst"),
                "module Hacl.Spec.Chacha20\n\nopen Spec.Chacha20\nopen Lib.IntTypes\nopen Lib.Sequence\n".to_string(),
            ),
            (
                PathBuf::from("code/Hacl.Impl.Chacha20.fst"),
                "module Hacl.Impl.Chacha20\n\nopen Hacl.Spec.Chacha20\nopen Lib.IntTypes\nopen Lib.Buffer\n\nfriend Hacl.Meta.Chacha20\n".to_string(),
            ),
            (
                PathBuf::from("code/Hacl.Chacha20.fst"),
                "module Hacl.Chacha20\n\nopen Hacl.Impl.Chacha20\n".to_string(),
            ),
        ];

        let graph = DependencyGraph::build(&files);

        // No cycles
        assert!(graph.find_cycles().is_empty());

        // No layer violations
        assert!(graph.find_layer_violations().is_empty());

        // Transitive deps of top-level API include everything
        let api_deps = graph.transitive_deps("Hacl.Chacha20");
        assert!(api_deps.contains("Hacl.Impl.Chacha20"));
        assert!(api_deps.contains("Hacl.Spec.Chacha20"));
        assert!(api_deps.contains("Spec.Chacha20"));

        // DOT output is non-empty
        let dot = graph.to_dot();
        assert!(dot.len() > 100);
    }

    // =======================================================================
    // Unnecessary transitive dependency detection
    // =======================================================================

    #[test]
    fn test_find_unnecessary_transitive_deps() {
        // A depends on B and C. B depends on C.
        // So A's dependency on C is transitively redundant via B.
        let files = vec![
            (
                PathBuf::from("A.fst"),
                "module A\n\nopen B\nopen C\n".to_string(),
            ),
            (
                PathBuf::from("B.fst"),
                "module B\n\nopen C\n".to_string(),
            ),
            (
                PathBuf::from("C.fst"),
                "module C\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);
        let redundant = graph.find_unnecessary_transitive_deps();

        assert_eq!(redundant.len(), 1, "Should detect one redundant dep: {:?}", redundant);
        assert_eq!(redundant[0].module, "A");
        assert_eq!(redundant[0].redundant_dep, "C");
        assert_eq!(redundant[0].provider, "B");
    }

    #[test]
    fn test_no_unnecessary_transitive_deps_in_linear_chain() {
        // A -> B -> C  (no redundancy, A only depends on B)
        let files = vec![
            (
                PathBuf::from("A.fst"),
                "module A\n\nopen B\n".to_string(),
            ),
            (
                PathBuf::from("B.fst"),
                "module B\n\nopen C\n".to_string(),
            ),
            (
                PathBuf::from("C.fst"),
                "module C\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);
        let redundant = graph.find_unnecessary_transitive_deps();
        assert!(
            redundant.is_empty(),
            "Linear chain should have no redundant deps"
        );
    }

    #[test]
    fn test_unnecessary_transitive_deps_diamond() {
        // Diamond: A -> B, A -> C, A -> D, B -> D, C -> D
        // A's dep on D is redundant (reachable via B or C)
        let files = vec![
            (
                PathBuf::from("A.fst"),
                "module A\n\nopen B\nopen C\nopen D\n".to_string(),
            ),
            (
                PathBuf::from("B.fst"),
                "module B\n\nopen D\n".to_string(),
            ),
            (
                PathBuf::from("C.fst"),
                "module C\n\nopen D\n".to_string(),
            ),
            (
                PathBuf::from("D.fst"),
                "module D\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);
        let redundant = graph.find_unnecessary_transitive_deps();

        let a_redundant: Vec<_> = redundant.iter().filter(|r| r.module == "A").collect();
        assert!(
            a_redundant.iter().any(|r| r.redundant_dep == "D"),
            "A's dep on D should be flagged as redundant: {:?}",
            a_redundant
        );
    }

    // =======================================================================
    // High fan-in detection
    // =======================================================================

    #[test]
    fn test_find_high_fan_in() {
        // C is imported by A, B, and D (fan-in = 3)
        let files = vec![
            (
                PathBuf::from("A.fst"),
                "module A\n\nopen C\n".to_string(),
            ),
            (
                PathBuf::from("B.fst"),
                "module B\n\nopen C\n".to_string(),
            ),
            (
                PathBuf::from("C.fst"),
                "module C\n".to_string(),
            ),
            (
                PathBuf::from("D.fst"),
                "module D\n\nopen C\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);

        let high_fan = graph.find_high_fan_in(3);
        assert_eq!(high_fan.len(), 1, "Should find exactly one high fan-in module");
        assert_eq!(high_fan[0].module, "C");
        assert_eq!(high_fan[0].fan_in, 3);
        assert_eq!(high_fan[0].importers.len(), 3);
    }

    #[test]
    fn test_high_fan_in_threshold() {
        // Same graph but with threshold=4 should return nothing
        let files = vec![
            (
                PathBuf::from("A.fst"),
                "module A\n\nopen C\n".to_string(),
            ),
            (
                PathBuf::from("B.fst"),
                "module B\n\nopen C\n".to_string(),
            ),
            (
                PathBuf::from("C.fst"),
                "module C\n".to_string(),
            ),
            (
                PathBuf::from("D.fst"),
                "module D\n\nopen C\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);

        let high_fan = graph.find_high_fan_in(4);
        assert!(
            high_fan.is_empty(),
            "With threshold=4, no module should qualify"
        );
    }

    #[test]
    fn test_high_fan_in_sorted_by_count() {
        // X has fan-in 3, Y has fan-in 2
        let files = vec![
            (
                PathBuf::from("A.fst"),
                "module A\n\nopen X\nopen Y\n".to_string(),
            ),
            (
                PathBuf::from("B.fst"),
                "module B\n\nopen X\nopen Y\n".to_string(),
            ),
            (
                PathBuf::from("C.fst"),
                "module C\n\nopen X\n".to_string(),
            ),
            (
                PathBuf::from("X.fst"),
                "module X\n".to_string(),
            ),
            (
                PathBuf::from("Y.fst"),
                "module Y\n".to_string(),
            ),
        ];
        let graph = DependencyGraph::build(&files);

        let high_fan = graph.find_high_fan_in(2);
        assert_eq!(high_fan.len(), 2, "Both X and Y should qualify");
        assert_eq!(
            high_fan[0].module, "X",
            "X (fan-in 3) should be first (sorted descending)"
        );
        assert_eq!(high_fan[0].fan_in, 3);
        assert_eq!(high_fan[1].module, "Y");
        assert_eq!(high_fan[1].fan_in, 2);
    }

    #[test]
    fn test_high_fan_in_hacl_style() {
        let files = make_graph_files();
        let graph = DependencyGraph::build(&files);

        // Lib.IntTypes is imported by 3 modules (Spec.SHA2, Hacl.Spec.SHA2, Hacl.Impl.SHA256)
        // ...wait, let's check: Spec.SHA2 opens Lib.IntTypes, Hacl.Spec.SHA2 opens Lib.IntTypes
        // Hacl.Impl.SHA256 does NOT open Lib.IntTypes (it opens Lib.Buffer)
        let high_fan = graph.find_high_fan_in(2);
        let lib_int = high_fan.iter().find(|e| e.module == "Lib.IntTypes");
        assert!(
            lib_int.is_some(),
            "Lib.IntTypes should have fan-in >= 2: {:?}",
            high_fan
        );
    }

    // =======================================================================
    // HACL*-style integration patterns (continued)
    // =======================================================================

    #[test]
    fn test_friend_creates_dependency() {
        let content = r#"
module Hacl.Curve25519_51

friend Hacl.Meta.Curve25519
open Hacl.Meta.Curve25519
module C = Hacl.Impl.Curve25519.Field51
"#;
        let deps = extract_dependencies(content);
        assert_eq!(deps.friends, vec!["Hacl.Meta.Curve25519"]);
        assert_eq!(deps.opens, vec!["Hacl.Meta.Curve25519"]);
        assert_eq!(deps.abbreviations, vec!["Hacl.Impl.Curve25519.Field51"]);

        // All deps should include friend, open, and abbreviation
        let all = deps.all_deps();
        assert!(all.contains(&"Hacl.Meta.Curve25519"));
        assert!(all.contains(&"Hacl.Impl.Curve25519.Field51"));
    }
}
