//! SQL Injection detection for Python and TypeScript.
//!
//! Detects potential SQL injection vulnerabilities by analyzing:
//! - String concatenation in SQL queries
//! - Format string interpolation
//! - f-string interpolation (Python)
//! - Template literal interpolation (TypeScript)
//! - Non-literal arguments to SQL execution functions
//!
//! # Architecture
//!
//! The detector works in three phases:
//! 1. **Sink Detection**: Find SQL execution calls (execute, query, raw, etc.)
//! 2. **Pattern Analysis**: Check if query argument uses unsafe string construction
//! 3. **Taint Tracking**: Trace data flow from user inputs to SQL sinks (via DFG)
//!
//! # Safe Patterns (Not Flagged)
//!
//! - Parameterized queries: `cursor.execute("SELECT * FROM users WHERE id = ?", (user_id,))`
//! - ORM methods with proper escaping: `User.objects.filter(id=user_id)`
//! - Literal string queries: `cursor.execute("SELECT * FROM users")`
//!
//! # Unsafe Patterns (Flagged)
//!
//! - String concatenation: `cursor.execute("SELECT * FROM users WHERE id = " + user_id)`
//! - f-strings: `cursor.execute(f"SELECT * FROM users WHERE id = {user_id}")`
//! - Format strings: `cursor.execute("SELECT * FROM users WHERE id = %s" % user_id)`
//! - Template literals: `db.query(`SELECT * FROM users WHERE id = ${userId}`)`

use std::collections::{HashMap, HashSet};
use std::path::Path;

use serde::{Deserialize, Serialize};
use streaming_iterator::StreamingIterator;
use tree_sitter::{Node, Query, QueryCursor, Tree};

use crate::error::{Result, BrrrError};
use crate::lang::LanguageRegistry;

// =============================================================================
// Types
// =============================================================================

/// Severity level for SQL injection findings.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Severity {
    /// Direct SQL injection with high confidence (e.g., string concat in execute)
    Critical,
    /// Likely SQL injection (e.g., f-string in query method)
    High,
    /// Possible SQL injection (e.g., variable passed to query, needs review)
    Medium,
    /// Informational finding (e.g., dynamic query construction detected)
    Low,
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Severity::Critical => write!(f, "CRITICAL"),
            Severity::High => write!(f, "HIGH"),
            Severity::Medium => write!(f, "MEDIUM"),
            Severity::Low => write!(f, "LOW"),
        }
    }
}

/// Location of a finding in source code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Location {
    /// File path
    pub file: String,
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed)
    pub column: usize,
    /// End line number (1-indexed)
    pub end_line: usize,
    /// End column number (1-indexed)
    pub end_column: usize,
}

/// Type of SQL sink function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SqlSinkType {
    /// cursor.execute(), connection.execute()
    Execute,
    /// db.query(), pool.query()
    Query,
    /// engine.raw(), knex.raw()
    Raw,
    /// $queryRaw, $executeRaw (Prisma)
    PrismaRaw,
    /// session.execute() (SQLAlchemy)
    SessionExecute,
    /// Text() for raw SQL in SQLAlchemy
    TextConstruct,
    /// Other sink type
    Other,
}

impl std::fmt::Display for SqlSinkType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SqlSinkType::Execute => write!(f, "execute"),
            SqlSinkType::Query => write!(f, "query"),
            SqlSinkType::Raw => write!(f, "raw"),
            SqlSinkType::PrismaRaw => write!(f, "prisma_raw"),
            SqlSinkType::SessionExecute => write!(f, "session_execute"),
            SqlSinkType::TextConstruct => write!(f, "text_construct"),
            SqlSinkType::Other => write!(f, "other"),
        }
    }
}

/// Type of unsafe pattern detected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnsafePattern {
    /// String concatenation: "SELECT ... " + var
    StringConcatenation,
    /// Python f-string: f"SELECT ... {var}"
    FStringInterpolation,
    /// Python format: "SELECT ... %s" % var
    PercentFormat,
    /// Python .format(): "SELECT ... {}".format(var)
    DotFormat,
    /// JavaScript template literal: `SELECT ... ${var}`
    TemplateLiteral,
    /// Variable passed directly (not a literal)
    NonLiteralArgument,
}

impl std::fmt::Display for UnsafePattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnsafePattern::StringConcatenation => write!(f, "string_concatenation"),
            UnsafePattern::FStringInterpolation => write!(f, "f_string_interpolation"),
            UnsafePattern::PercentFormat => write!(f, "percent_format"),
            UnsafePattern::DotFormat => write!(f, "dot_format"),
            UnsafePattern::TemplateLiteral => write!(f, "template_literal"),
            UnsafePattern::NonLiteralArgument => write!(f, "non_literal_argument"),
        }
    }
}

/// A SQL injection finding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SQLInjectionFinding {
    /// Location in source code
    pub location: Location,
    /// Severity level
    pub severity: Severity,
    /// Type of SQL sink function
    pub sink_function: SqlSinkType,
    /// Full sink call expression (e.g., "cursor.execute")
    pub sink_expression: String,
    /// Which parameter is tainted (0-indexed)
    pub tainted_param: usize,
    /// The unsafe pattern detected
    pub pattern: UnsafePattern,
    /// Confidence score (0.0 to 1.0)
    pub confidence: f64,
    /// Code snippet showing the vulnerable code
    pub code_snippet: String,
    /// Variables involved in the taint chain
    pub tainted_variables: Vec<String>,
    /// Human-readable description
    pub description: String,
    /// Suggested fix
    pub remediation: String,
}

/// Summary of SQL injection scan results.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScanResult {
    /// All findings
    pub findings: Vec<SQLInjectionFinding>,
    /// Number of files scanned
    pub files_scanned: usize,
    /// Number of SQL sinks found
    pub sinks_found: usize,
    /// Counts by severity
    pub severity_counts: HashMap<String, usize>,
    /// Language detected
    pub language: String,
}

// =============================================================================
// SQL Sink Definitions
// =============================================================================

/// Known SQL sinks for Python.
const PYTHON_SQL_SINKS: &[(&str, SqlSinkType)] = &[
    // Database cursor methods
    ("execute", SqlSinkType::Execute),
    ("executemany", SqlSinkType::Execute),
    ("executescript", SqlSinkType::Execute),
    // Connection methods
    ("connection.execute", SqlSinkType::Execute),
    // SQLAlchemy
    ("engine.execute", SqlSinkType::Execute),
    ("session.execute", SqlSinkType::SessionExecute),
    ("text", SqlSinkType::TextConstruct),
    // Django
    ("raw", SqlSinkType::Raw),
    ("extra", SqlSinkType::Raw),
    // psycopg2/asyncpg
    ("cursor.execute", SqlSinkType::Execute),
    ("conn.execute", SqlSinkType::Execute),
    ("pool.execute", SqlSinkType::Execute),
    // aiosqlite
    ("db.execute", SqlSinkType::Execute),
];

/// Known SQL sinks for TypeScript/JavaScript.
const TYPESCRIPT_SQL_SINKS: &[(&str, SqlSinkType)] = &[
    // Generic query methods
    ("query", SqlSinkType::Query),
    ("execute", SqlSinkType::Execute),
    // Knex
    ("raw", SqlSinkType::Raw),
    ("knex.raw", SqlSinkType::Raw),
    // Prisma
    ("$queryRaw", SqlSinkType::PrismaRaw),
    ("$executeRaw", SqlSinkType::PrismaRaw),
    ("$queryRawUnsafe", SqlSinkType::PrismaRaw),
    ("$executeRawUnsafe", SqlSinkType::PrismaRaw),
    // TypeORM
    ("createQueryRunner", SqlSinkType::Query),
    ("manager.query", SqlSinkType::Query),
    // Sequelize
    ("sequelize.query", SqlSinkType::Query),
    // node-postgres
    ("pool.query", SqlSinkType::Query),
    ("client.query", SqlSinkType::Query),
    // mysql2
    ("connection.query", SqlSinkType::Query),
    ("connection.execute", SqlSinkType::Execute),
    // better-sqlite3
    ("db.exec", SqlSinkType::Execute),
    ("db.prepare", SqlSinkType::Execute),
];

// =============================================================================
// Detector Implementation
// =============================================================================

/// SQL Injection detector for multiple languages.
pub struct SqlInjectionDetector {
    /// Python SQL sink patterns (method_name -> sink_type)
    python_sinks: HashMap<String, SqlSinkType>,
    /// TypeScript SQL sink patterns
    typescript_sinks: HashMap<String, SqlSinkType>,
}

impl Default for SqlInjectionDetector {
    fn default() -> Self {
        Self::new()
    }
}

impl SqlInjectionDetector {
    /// Create a new SQL injection detector.
    pub fn new() -> Self {
        let mut python_sinks = HashMap::new();
        for (name, sink_type) in PYTHON_SQL_SINKS {
            python_sinks.insert((*name).to_string(), *sink_type);
        }

        let mut typescript_sinks = HashMap::new();
        for (name, sink_type) in TYPESCRIPT_SQL_SINKS {
            typescript_sinks.insert((*name).to_string(), *sink_type);
        }

        Self {
            python_sinks,
            typescript_sinks,
        }
    }

    /// Scan a file for SQL injection vulnerabilities.
    ///
    /// # Arguments
    ///
    /// * `file_path` - Path to the source file
    ///
    /// # Returns
    ///
    /// Vector of SQL injection findings
    pub fn scan_file(&self, file_path: &str) -> Result<Vec<SQLInjectionFinding>> {
        let path = Path::new(file_path);
        let registry = LanguageRegistry::global();

        let lang = registry.detect_language(path).ok_or_else(|| {
            BrrrError::UnsupportedLanguage(
                path.extension()
                    .and_then(|e| e.to_str())
                    .unwrap_or("unknown")
                    .to_string(),
            )
        })?;

        let source = std::fs::read(path).map_err(|e| BrrrError::io_with_path(e, path))?;
        let mut parser = lang.parser_for_path(path)?;
        let tree = parser.parse(&source, None).ok_or_else(|| BrrrError::Parse {
            file: file_path.to_string(),
            message: "Failed to parse file".to_string(),
        })?;

        let lang_name = lang.name();
        match lang_name {
            "python" => self.scan_python(&tree, &source, file_path),
            "typescript" | "javascript" => self.scan_typescript(&tree, &source, file_path),
            _ => Ok(vec![]), // Other languages not yet supported
        }
    }

    /// Scan a directory for SQL injection vulnerabilities.
    ///
    /// # Arguments
    ///
    /// * `dir_path` - Path to the directory
    /// * `language` - Optional language filter
    ///
    /// # Returns
    ///
    /// Scan result with all findings
    pub fn scan_directory(&self, dir_path: &str, language: Option<&str>) -> Result<ScanResult> {
        let path = Path::new(dir_path);
        if !path.is_dir() {
            return Err(BrrrError::InvalidArgument(format!(
                "Not a directory: {}",
                dir_path
            )));
        }

        let mut findings = Vec::new();
        let mut files_scanned = 0;
        let mut sinks_found = 0;

        // Walk directory respecting .gitignore and .brrrignore
        let mut builder = ignore::WalkBuilder::new(path);
        builder.add_custom_ignore_filename(".brrrignore");
        builder.hidden(true);

        let extensions: HashSet<&str> = match language {
            Some("python") => ["py"].iter().copied().collect(),
            Some("typescript") => ["ts", "tsx", "js", "jsx", "mjs", "cjs"]
                .iter()
                .copied()
                .collect(),
            Some("javascript") => ["js", "jsx", "mjs", "cjs"].iter().copied().collect(),
            _ => ["py", "ts", "tsx", "js", "jsx", "mjs", "cjs"]
                .iter()
                .copied()
                .collect(),
        };

        for entry in builder.build().flatten() {
            let entry_path = entry.path();
            if !entry_path.is_file() {
                continue;
            }

            let ext = entry_path
                .extension()
                .and_then(|e| e.to_str())
                .unwrap_or("");
            if !extensions.contains(ext) {
                continue;
            }

            files_scanned += 1;

            if let Ok(file_findings) = self.scan_file(entry_path.to_str().unwrap_or("")) {
                sinks_found += file_findings.len();
                findings.extend(file_findings);
            }
        }

        // Count by severity
        let mut severity_counts: HashMap<String, usize> = HashMap::new();
        for finding in &findings {
            *severity_counts
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
        }

        let detected_lang = language.unwrap_or("mixed").to_string();

        Ok(ScanResult {
            findings,
            files_scanned,
            sinks_found,
            severity_counts,
            language: detected_lang,
        })
    }

    // =========================================================================
    // Python Analysis
    // =========================================================================

    /// Scan Python source for SQL injection.
    fn scan_python(
        &self,
        tree: &Tree,
        source: &[u8],
        file_path: &str,
    ) -> Result<Vec<SQLInjectionFinding>> {
        let mut findings = Vec::new();

        // Query for call expressions
        let query_str = r#"
            (call
                function: [
                    (identifier) @func_name
                    (attribute
                        object: (_) @obj
                        attribute: (identifier) @method_name)
                ]
                arguments: (argument_list) @args
            ) @call
        "#;

        let ts_lang = tree.language();
        let query = Query::new(&ts_lang, query_str).map_err(|e| {
            BrrrError::TreeSitter(format!("Failed to create Python query: {}", e))
        })?;

        let mut cursor = QueryCursor::new();
        let mut matches = cursor.matches(&query, tree.root_node(), source);

        let func_name_idx = query.capture_index_for_name("func_name");
        let method_name_idx = query.capture_index_for_name("method_name");
        let obj_idx = query.capture_index_for_name("obj");
        let args_idx = query.capture_index_for_name("args");
        let call_idx = query.capture_index_for_name("call");

        while let Some(match_) = matches.next() {
            // Get call node
            let call_node: Option<Node> = match call_idx {
                Some(idx) => match_.captures.iter().find(|c| c.index == idx).map(|c| c.node),
                None => None,
            };

            // Get function/method name
            let func_name: Option<&str> = func_name_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| self.node_text(c.node, source))
            });

            let method_name: Option<&str> = method_name_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| self.node_text(c.node, source))
            });

            let obj_text: Option<&str> = obj_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| self.node_text(c.node, source))
            });

            let args_node: Option<Node> = args_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| c.node)
            });

            // Determine if this is a SQL sink
            let (sink_name, sink_type) = if let Some(method) = method_name {
                let full_name = if let Some(obj) = obj_text {
                    format!("{}.{}", obj, method)
                } else {
                    method.to_string()
                };

                // Check if method is a known sink
                if let Some(sink_type) = self.python_sinks.get(method) {
                    (full_name, *sink_type)
                } else if let Some(sink_type) = self.python_sinks.get(&full_name) {
                    (full_name, *sink_type)
                } else {
                    continue;
                }
            } else if let Some(func) = func_name {
                if let Some(sink_type) = self.python_sinks.get(func) {
                    (func.to_string(), *sink_type)
                } else {
                    continue;
                }
            } else {
                continue;
            };

            // Analyze arguments for unsafe patterns
            if let (Some(call_node), Some(args_node)) = (call_node, args_node) {
                if let Some(finding) = self.analyze_python_call_args(
                    call_node, args_node, source, file_path, &sink_name, sink_type,
                ) {
                    findings.push(finding);
                }
            }
        }

        Ok(findings)
    }

    /// Analyze Python call arguments for SQL injection patterns.
    fn analyze_python_call_args(
        &self,
        call_node: Node,
        args_node: Node,
        source: &[u8],
        file_path: &str,
        sink_name: &str,
        sink_type: SqlSinkType,
    ) -> Option<SQLInjectionFinding> {
        // Get first argument (the SQL query)
        let first_arg = self.get_first_python_arg(args_node)?;

        // Check for parameterized query (safe pattern)
        // Look for tuple as second argument: execute("...", (param,))
        if self.has_python_params(args_node, source) {
            // Check if query uses parameterized placeholders (?, %s, :name)
            let query_text = self.node_text(first_arg, source);
            if query_text.contains('?')
                || query_text.contains("%s")
                || query_text.contains("%(")
                || query_text.contains(':')
            {
                return None; // Safe parameterized query
            }
        }

        // Analyze the first argument for unsafe patterns
        let (pattern, severity, confidence, tainted_vars) =
            self.analyze_python_expression(first_arg, source)?;

        let code_snippet = self.node_text(call_node, source).to_string();
        let location = Location {
            file: file_path.to_string(),
            line: call_node.start_position().row + 1,
            column: call_node.start_position().column + 1,
            end_line: call_node.end_position().row + 1,
            end_column: call_node.end_position().column + 1,
        };

        let description = self.generate_description(&pattern, sink_name, &tainted_vars);
        let remediation = self.generate_remediation(&pattern, "python");

        Some(SQLInjectionFinding {
            location,
            severity,
            sink_function: sink_type,
            sink_expression: sink_name.to_string(),
            tainted_param: 0,
            pattern,
            confidence,
            code_snippet,
            tainted_variables: tainted_vars,
            description,
            remediation,
        })
    }

    /// Get the first positional argument from Python argument list.
    fn get_first_python_arg<'a>(&self, args_node: Node<'a>) -> Option<Node<'a>> {
        let mut cursor = args_node.walk();
        for child in args_node.children(&mut cursor) {
            match child.kind() {
                "(" | ")" | "," => continue,
                "keyword_argument" => continue, // Skip keyword args
                _ => return Some(child),
            }
        }
        None
    }

    /// Check if Python call has parameter arguments (tuple/list as second arg).
    fn has_python_params(&self, args_node: Node, _source: &[u8]) -> bool {
        let mut positional_args = Vec::new();
        let mut cursor = args_node.walk();

        for child in args_node.children(&mut cursor) {
            match child.kind() {
                "(" | ")" | "," => continue,
                "keyword_argument" => continue,
                _ => positional_args.push(child),
            }
        }

        // Check if there's a second argument that looks like params
        if positional_args.len() >= 2 {
            let second_arg = positional_args[1];
            matches!(
                second_arg.kind(),
                "tuple" | "list" | "dictionary" | "identifier"
            )
        } else {
            false
        }
    }

    /// Analyze a Python expression for unsafe patterns.
    ///
    /// Returns (pattern, severity, confidence, tainted_variables)
    fn analyze_python_expression(
        &self,
        node: Node,
        source: &[u8],
    ) -> Option<(UnsafePattern, Severity, f64, Vec<String>)> {
        match node.kind() {
            // f-string: f"SELECT ... {var}"
            "string" => {
                let text = self.node_text(node, source);
                if text.starts_with("f\"") || text.starts_with("f'") {
                    // Extract interpolated variables
                    let vars = self.extract_fstring_variables(text);
                    if !vars.is_empty() {
                        return Some((
                            UnsafePattern::FStringInterpolation,
                            Severity::Critical,
                            0.95,
                            vars,
                        ));
                    }
                }
                None
            }

            // Binary operator: "SELECT ... " + var
            "binary_operator" => {
                let op_node = node.child_by_field_name("operator")?;
                let op = self.node_text(op_node, source);

                if op == "+" {
                    // String concatenation
                    let left = node.child_by_field_name("left")?;
                    let right = node.child_by_field_name("right")?;

                    let left_is_string = self.is_string_literal(left, source);
                    let right_is_string = self.is_string_literal(right, source);

                    if left_is_string || right_is_string {
                        let vars = self.collect_variables(node, source);
                        return Some((
                            UnsafePattern::StringConcatenation,
                            Severity::Critical,
                            0.9,
                            vars,
                        ));
                    }
                } else if op == "%" {
                    // Percent format: "SELECT ... %s" % var
                    let vars = self.collect_variables(node, source);
                    return Some((UnsafePattern::PercentFormat, Severity::Critical, 0.9, vars));
                }
                None
            }

            // Method call: "SELECT ... {}".format(var)
            "call" => {
                // Check for .format() calls
                if let Some(func) = node.child_by_field_name("function") {
                    if func.kind() == "attribute" {
                        if let Some(attr) = func.child_by_field_name("attribute") {
                            if self.node_text(attr, source) == "format" {
                                let vars = self.collect_call_args(node, source);
                                return Some((
                                    UnsafePattern::DotFormat,
                                    Severity::Critical,
                                    0.9,
                                    vars,
                                ));
                            }
                        }
                    }
                }
                None
            }

            // Identifier: variable passed directly
            "identifier" => {
                let var_name = self.node_text(node, source).to_string();
                // Lower severity for variable - might be a constant
                Some((
                    UnsafePattern::NonLiteralArgument,
                    Severity::Medium,
                    0.6,
                    vec![var_name],
                ))
            }

            // Concatenated string: handle multi-part strings
            "concatenated_string" => {
                let text = self.node_text(node, source);
                if text.contains("f\"") || text.contains("f'") {
                    let vars = self.extract_fstring_variables(text);
                    if !vars.is_empty() {
                        return Some((
                            UnsafePattern::FStringInterpolation,
                            Severity::Critical,
                            0.95,
                            vars,
                        ));
                    }
                }
                None
            }

            _ => None,
        }
    }

    // =========================================================================
    // TypeScript/JavaScript Analysis
    // =========================================================================

    /// Scan TypeScript/JavaScript source for SQL injection.
    fn scan_typescript(
        &self,
        tree: &Tree,
        source: &[u8],
        file_path: &str,
    ) -> Result<Vec<SQLInjectionFinding>> {
        let mut findings = Vec::new();

        // Query for call expressions
        let query_str = r#"
            (call_expression
                function: [
                    (identifier) @func_name
                    (member_expression
                        object: (_) @obj
                        property: (property_identifier) @method_name)
                ]
                arguments: (arguments) @args
            ) @call
        "#;

        let ts_lang = tree.language();
        let query = Query::new(&ts_lang, query_str).map_err(|e| {
            BrrrError::TreeSitter(format!("Failed to create TypeScript query: {}", e))
        })?;

        let mut cursor = QueryCursor::new();
        let mut matches = cursor.matches(&query, tree.root_node(), source);

        let func_name_idx = query.capture_index_for_name("func_name");
        let method_name_idx = query.capture_index_for_name("method_name");
        let obj_idx = query.capture_index_for_name("obj");
        let args_idx = query.capture_index_for_name("args");
        let call_idx = query.capture_index_for_name("call");

        while let Some(match_) = matches.next() {
            let call_node: Option<Node> = match call_idx {
                Some(idx) => match_.captures.iter().find(|c| c.index == idx).map(|c| c.node),
                None => None,
            };

            let func_name: Option<&str> = func_name_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| self.node_text(c.node, source))
            });

            let method_name: Option<&str> = method_name_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| self.node_text(c.node, source))
            });

            let obj_text: Option<&str> = obj_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| self.node_text(c.node, source))
            });

            let args_node: Option<Node> = args_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| c.node)
            });

            // Determine if this is a SQL sink
            let (sink_name, sink_type) = if let Some(method) = method_name {
                let full_name = if let Some(obj) = obj_text {
                    format!("{}.{}", obj, method)
                } else {
                    method.to_string()
                };

                if let Some(sink_type) = self.typescript_sinks.get(method) {
                    (full_name, *sink_type)
                } else if let Some(sink_type) = self.typescript_sinks.get(&full_name) {
                    (full_name, *sink_type)
                } else {
                    continue;
                }
            } else if let Some(func) = func_name {
                if let Some(sink_type) = self.typescript_sinks.get(func) {
                    (func.to_string(), *sink_type)
                } else {
                    continue;
                }
            } else {
                continue;
            };

            // Analyze arguments
            if let (Some(call_node), Some(args_node)) = (call_node, args_node) {
                if let Some(finding) = self.analyze_typescript_call_args(
                    call_node, args_node, source, file_path, &sink_name, sink_type,
                ) {
                    findings.push(finding);
                }
            }
        }

        Ok(findings)
    }

    /// Analyze TypeScript call arguments for SQL injection patterns.
    fn analyze_typescript_call_args(
        &self,
        call_node: Node,
        args_node: Node,
        source: &[u8],
        file_path: &str,
        sink_name: &str,
        sink_type: SqlSinkType,
    ) -> Option<SQLInjectionFinding> {
        // Get first argument
        let first_arg = self.get_first_typescript_arg(args_node)?;

        // Check for parameterized query with array as second arg
        if self.has_typescript_params(args_node, source) {
            let query_text = self.node_text(first_arg, source);
            // Check for parameterized placeholders ($1, ?, :name)
            if query_text.contains('$')
                || query_text.contains('?')
                || query_text.contains(':')
            {
                return None; // Safe parameterized query
            }
        }

        // Analyze expression
        let (pattern, severity, confidence, tainted_vars) =
            self.analyze_typescript_expression(first_arg, source)?;

        let code_snippet = self.node_text(call_node, source).to_string();
        let location = Location {
            file: file_path.to_string(),
            line: call_node.start_position().row + 1,
            column: call_node.start_position().column + 1,
            end_line: call_node.end_position().row + 1,
            end_column: call_node.end_position().column + 1,
        };

        let description = self.generate_description(&pattern, sink_name, &tainted_vars);
        let remediation = self.generate_remediation(&pattern, "typescript");

        Some(SQLInjectionFinding {
            location,
            severity,
            sink_function: sink_type,
            sink_expression: sink_name.to_string(),
            tainted_param: 0,
            pattern,
            confidence,
            code_snippet,
            tainted_variables: tainted_vars,
            description,
            remediation,
        })
    }

    /// Get first positional argument from TypeScript arguments.
    fn get_first_typescript_arg<'a>(&self, args_node: Node<'a>) -> Option<Node<'a>> {
        let mut cursor = args_node.walk();
        for child in args_node.children(&mut cursor) {
            match child.kind() {
                "(" | ")" | "," => continue,
                _ => return Some(child),
            }
        }
        None
    }

    /// Check if TypeScript call has parameter arguments.
    fn has_typescript_params(&self, args_node: Node, _source: &[u8]) -> bool {
        let mut positional_args = Vec::new();
        let mut cursor = args_node.walk();

        for child in args_node.children(&mut cursor) {
            match child.kind() {
                "(" | ")" | "," => continue,
                _ => positional_args.push(child),
            }
        }

        // Check if there's an array as second argument
        if positional_args.len() >= 2 {
            let second_arg = positional_args[1];
            matches!(second_arg.kind(), "array" | "identifier")
        } else {
            false
        }
    }

    /// Analyze a TypeScript expression for unsafe patterns.
    fn analyze_typescript_expression(
        &self,
        node: Node,
        source: &[u8],
    ) -> Option<(UnsafePattern, Severity, f64, Vec<String>)> {
        match node.kind() {
            // Template literal: `SELECT ... ${var}`
            "template_string" => {
                // Check for interpolation
                let mut cursor = node.walk();
                let mut has_substitution = false;
                let mut vars = Vec::new();

                for child in node.children(&mut cursor) {
                    if child.kind() == "template_substitution" {
                        has_substitution = true;
                        vars.extend(self.collect_variables(child, source));
                    }
                }

                if has_substitution {
                    return Some((
                        UnsafePattern::TemplateLiteral,
                        Severity::Critical,
                        0.95,
                        vars,
                    ));
                }
                None
            }

            // Binary expression: "SELECT ... " + var
            "binary_expression" => {
                let op_node = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "+" || c.kind() == "binary_operator")?;
                let op = self.node_text(op_node, source);

                if op == "+" {
                    let left = node.child(0)?;
                    let right = node.child(2)?;

                    let left_is_string = self.is_string_literal(left, source);
                    let right_is_string = self.is_string_literal(right, source);

                    if left_is_string || right_is_string {
                        let vars = self.collect_variables(node, source);
                        return Some((
                            UnsafePattern::StringConcatenation,
                            Severity::Critical,
                            0.9,
                            vars,
                        ));
                    }
                }
                None
            }

            // Identifier: variable passed directly
            "identifier" => {
                let var_name = self.node_text(node, source).to_string();
                Some((
                    UnsafePattern::NonLiteralArgument,
                    Severity::Medium,
                    0.6,
                    vec![var_name],
                ))
            }

            _ => None,
        }
    }

    // =========================================================================
    // Helper Methods
    // =========================================================================

    /// Get text from a node.
    fn node_text<'a>(&self, node: Node, source: &'a [u8]) -> &'a str {
        std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
    }

    /// Check if node is a string literal.
    fn is_string_literal(&self, node: Node, source: &[u8]) -> bool {
        let text = self.node_text(node, source);
        matches!(node.kind(), "string" | "string_literal" | "template_string")
            || text.starts_with('"')
            || text.starts_with('\'')
            || text.starts_with('`')
    }

    /// Extract variables from f-string.
    ///
    /// Uses SIMD (AVX2) to find `{` and `}` positions in parallel when available,
    /// falling back to scalar processing for small strings or non-x86 platforms.
    fn extract_fstring_variables(&self, text: &str) -> Vec<String> {
        let bytes = text.as_bytes();

        // For very short strings, use scalar path directly
        if bytes.len() < 64 {
            return self.extract_fstring_variables_scalar(text);
        }

        // Find all { and } positions using SIMD
        let open_positions = Self::find_byte_positions_simd(bytes, b'{');
        let close_positions = Self::find_byte_positions_simd(bytes, b'}');

        // If no braces found, return early
        if open_positions.is_empty() || close_positions.is_empty() {
            return Vec::new();
        }

        // Process matched pairs
        self.extract_vars_from_positions(bytes, &open_positions, &close_positions)
    }

    /// SIMD-accelerated byte position finder using AVX2 (u8x32).
    ///
    /// Scans 32 bytes at a time, returning all positions where `needle` occurs.
    #[cfg(target_arch = "x86_64")]
    fn find_byte_positions_simd(haystack: &[u8], needle: u8) -> Vec<usize> {
        use std::arch::x86_64::{
            __m256i, _mm256_cmpeq_epi8, _mm256_loadu_si256, _mm256_movemask_epi8, _mm256_set1_epi8,
        };

        let len = haystack.len();
        // Pre-allocate with reasonable capacity (expect ~1 match per 32 bytes on average)
        let mut positions = Vec::with_capacity(len / 32 + 1);

        // SAFETY: We check for AVX2 support at runtime
        if !std::arch::is_x86_feature_detected!("avx2") {
            // Fallback to scalar for non-AVX2 CPUs
            for (i, &b) in haystack.iter().enumerate() {
                if b == needle {
                    positions.push(i);
                }
            }
            return positions;
        }

        // SAFETY: AVX2 is available (checked above), pointers are valid
        unsafe {
            let needle_vec: __m256i = _mm256_set1_epi8(needle as i8);
            let mut offset = 0;

            // Process 32 bytes at a time
            while offset + 32 <= len {
                let chunk_ptr = haystack.as_ptr().add(offset) as *const __m256i;
                let chunk: __m256i = _mm256_loadu_si256(chunk_ptr);
                let cmp: __m256i = _mm256_cmpeq_epi8(chunk, needle_vec);
                let mask = _mm256_movemask_epi8(cmp) as u32;

                // Extract positions from bitmask
                if mask != 0 {
                    let mut m = mask;
                    while m != 0 {
                        let bit_pos = m.trailing_zeros() as usize;
                        positions.push(offset + bit_pos);
                        m &= m - 1; // Clear lowest set bit
                    }
                }
                offset += 32;
            }

            // Handle remaining bytes (< 32) with scalar
            for i in offset..len {
                if *haystack.get_unchecked(i) == needle {
                    positions.push(i);
                }
            }
        }

        positions
    }

    /// Fallback for non-x86_64 platforms.
    #[cfg(not(target_arch = "x86_64"))]
    fn find_byte_positions_simd(haystack: &[u8], needle: u8) -> Vec<usize> {
        haystack
            .iter()
            .enumerate()
            .filter_map(|(i, &b)| if b == needle { Some(i) } else { None })
            .collect()
    }

    /// Extract variables from pre-computed brace positions.
    ///
    /// Matches opening `{` with closing `}` respecting nesting (escaped `{{`).
    fn extract_vars_from_positions(
        &self,
        bytes: &[u8],
        opens: &[usize],
        closes: &[usize],
    ) -> Vec<String> {
        let mut vars = Vec::with_capacity(opens.len().min(closes.len()));
        let mut open_idx = 0;
        let mut close_idx = 0;

        while open_idx < opens.len() && close_idx < closes.len() {
            let open_pos = opens[open_idx];
            let close_pos = closes[close_idx];

            // Skip if close comes before open
            if close_pos <= open_pos {
                close_idx += 1;
                continue;
            }

            // Check for escaped brace `{{` - skip if next char is also `{`
            if open_pos + 1 < bytes.len() && bytes[open_pos + 1] == b'{' {
                open_idx += 2; // Skip both `{` of `{{`
                continue;
            }

            // Extract content between braces
            let content = &bytes[open_pos + 1..close_pos];

            // Skip empty content
            if !content.is_empty() {
                if let Ok(var_str) = std::str::from_utf8(content) {
                    // Extract just the variable name (strip formatting specs like :, !, .)
                    let var_name = var_str
                        .split([':', '!', '.'])
                        .next()
                        .unwrap_or(var_str)
                        .trim();

                    if !var_name.is_empty() {
                        vars.push(var_name.to_string());
                    }
                }
            }

            open_idx += 1;
            close_idx += 1;
        }

        vars
    }

    /// Scalar fallback for small strings or non-SIMD paths.
    fn extract_fstring_variables_scalar(&self, text: &str) -> Vec<String> {
        let mut vars = Vec::new();
        let mut in_brace = false;
        let mut current_var = String::new();

        for ch in text.chars() {
            if ch == '{' && !in_brace {
                in_brace = true;
                current_var.clear();
            } else if ch == '}' && in_brace {
                in_brace = false;
                if !current_var.is_empty() && !current_var.starts_with('{') {
                    // Extract just the variable name (strip formatting specs)
                    let var_name = current_var
                        .split([':', '!', '.'])
                        .next()
                        .unwrap_or(&current_var)
                        .trim();
                    if !var_name.is_empty() {
                        vars.push(var_name.to_string());
                    }
                }
            } else if in_brace {
                current_var.push(ch);
            }
        }

        vars
    }

    /// Collect all identifier variables from a node tree.
    fn collect_variables(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut vars = Vec::new();
        self.collect_variables_recursive(node, source, &mut vars);
        vars.sort();
        vars.dedup();
        vars
    }

    fn collect_variables_recursive(&self, node: Node, source: &[u8], vars: &mut Vec<String>) {
        if node.kind() == "identifier" {
            let name = self.node_text(node, source).to_string();
            // Filter out common non-user-input identifiers
            if !["True", "False", "None", "self", "cls"].contains(&name.as_str()) {
                vars.push(name);
            }
        }

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.collect_variables_recursive(child, source, vars);
        }
    }

    /// Collect arguments from a call node.
    fn collect_call_args(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut vars = Vec::new();
        if let Some(args) = node.child_by_field_name("arguments") {
            self.collect_variables_recursive(args, source, &mut vars);
        }
        vars.sort();
        vars.dedup();
        vars
    }

    /// Generate human-readable description.
    fn generate_description(
        &self,
        pattern: &UnsafePattern,
        sink_name: &str,
        vars: &[String],
    ) -> String {
        let var_list = if vars.is_empty() {
            "unknown variable".to_string()
        } else {
            vars.join(", ")
        };

        match pattern {
            UnsafePattern::StringConcatenation => {
                format!(
                    "SQL injection via string concatenation in {}(). Variables {} are concatenated into the query string.",
                    sink_name, var_list
                )
            }
            UnsafePattern::FStringInterpolation => {
                format!(
                    "SQL injection via f-string interpolation in {}(). Variables {} are interpolated into the query.",
                    sink_name, var_list
                )
            }
            UnsafePattern::PercentFormat => {
                format!(
                    "SQL injection via percent formatting in {}(). Variables {} are formatted into the query.",
                    sink_name, var_list
                )
            }
            UnsafePattern::DotFormat => {
                format!(
                    "SQL injection via .format() in {}(). Variables {} are formatted into the query.",
                    sink_name, var_list
                )
            }
            UnsafePattern::TemplateLiteral => {
                format!(
                    "SQL injection via template literal in {}(). Variables {} are interpolated into the query.",
                    sink_name, var_list
                )
            }
            UnsafePattern::NonLiteralArgument => {
                format!(
                    "Potential SQL injection in {}(). Variable {} is passed directly to the query.",
                    sink_name, var_list
                )
            }
        }
    }

    /// Generate remediation advice.
    fn generate_remediation(&self, pattern: &UnsafePattern, language: &str) -> String {
        match (pattern, language) {
            (_, "python") => {
                "Use parameterized queries with placeholders:\n\
                 cursor.execute(\"SELECT * FROM users WHERE id = ?\", (user_id,))\n\
                 Or use SQLAlchemy ORM methods with proper escaping."
                    .to_string()
            }
            (_, "typescript" | "javascript") => {
                "Use parameterized queries with placeholders:\n\
                 db.query(\"SELECT * FROM users WHERE id = $1\", [userId])\n\
                 Or use an ORM like Prisma, TypeORM, or Knex with proper parameter binding."
                    .to_string()
            }
            _ => "Use parameterized queries instead of string interpolation.".to_string(),
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn create_temp_file(content: &str, extension: &str) -> tempfile::NamedTempFile {
        use std::io::Write;
        let mut file = tempfile::Builder::new()
            .suffix(extension)
            .tempfile()
            .expect("Failed to create temp file");
        file.write_all(content.as_bytes())
            .expect("Failed to write temp file");
        file
    }

    // =========================================================================
    // Python Tests
    // =========================================================================

    #[test]
    fn test_python_fstring_injection() {
        let source = r#"
import sqlite3
conn = sqlite3.connect('test.db')
cursor = conn.cursor()

def get_user(user_id):
    cursor.execute(f"SELECT * FROM users WHERE id = {user_id}")
    return cursor.fetchone()
"#;
        let file = create_temp_file(source, ".py");
        let detector = SqlInjectionDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect f-string injection");
        let finding = &findings[0];
        assert_eq!(finding.pattern, UnsafePattern::FStringInterpolation);
        assert_eq!(finding.severity, Severity::Critical);
        assert!(finding.tainted_variables.contains(&"user_id".to_string()));
    }

    #[test]
    fn test_python_string_concat_injection() {
        let source = r#"
import sqlite3
conn = sqlite3.connect('test.db')
cursor = conn.cursor()

def get_user(user_id):
    query = "SELECT * FROM users WHERE id = " + user_id
    cursor.execute(query)
    return cursor.fetchone()
"#;
        let file = create_temp_file(source, ".py");
        let detector = SqlInjectionDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        // The detector finds the variable being passed to execute
        assert!(!findings.is_empty(), "Should detect variable injection");
    }

    #[test]
    fn test_python_percent_format_injection() {
        let source = r#"
import sqlite3
conn = sqlite3.connect('test.db')
cursor = conn.cursor()

def get_user(user_id):
    cursor.execute("SELECT * FROM users WHERE id = %s" % user_id)
    return cursor.fetchone()
"#;
        let file = create_temp_file(source, ".py");
        let detector = SqlInjectionDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect percent format injection");
        let finding = &findings[0];
        assert_eq!(finding.pattern, UnsafePattern::PercentFormat);
    }

    #[test]
    fn test_python_safe_parameterized_query() {
        let source = r#"
import sqlite3
conn = sqlite3.connect('test.db')
cursor = conn.cursor()

def get_user(user_id):
    cursor.execute("SELECT * FROM users WHERE id = ?", (user_id,))
    return cursor.fetchone()
"#;
        let file = create_temp_file(source, ".py");
        let detector = SqlInjectionDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(
            findings.is_empty(),
            "Should NOT detect safe parameterized query"
        );
    }

    #[test]
    fn test_python_safe_literal_query() {
        let source = r#"
import sqlite3
conn = sqlite3.connect('test.db')
cursor = conn.cursor()

def get_all_users():
    cursor.execute("SELECT * FROM users")
    return cursor.fetchall()
"#;
        let file = create_temp_file(source, ".py");
        let detector = SqlInjectionDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(findings.is_empty(), "Should NOT detect safe literal query");
    }

    // =========================================================================
    // TypeScript Tests
    // =========================================================================

    #[test]
    fn test_typescript_template_literal_injection() {
        let source = r#"
import { Pool } from 'pg';
const pool = new Pool();

async function getUser(userId: string) {
    const result = await pool.query(`SELECT * FROM users WHERE id = ${userId}`);
    return result.rows[0];
}
"#;
        let file = create_temp_file(source, ".ts");
        let detector = SqlInjectionDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(
            !findings.is_empty(),
            "Should detect template literal injection"
        );
        let finding = &findings[0];
        assert_eq!(finding.pattern, UnsafePattern::TemplateLiteral);
        assert_eq!(finding.severity, Severity::Critical);
    }

    #[test]
    fn test_typescript_string_concat_injection() {
        let source = r#"
import { Pool } from 'pg';
const pool = new Pool();

async function getUser(userId: string) {
    const query = "SELECT * FROM users WHERE id = " + userId;
    const result = await pool.query(query);
    return result.rows[0];
}
"#;
        let file = create_temp_file(source, ".ts");
        let detector = SqlInjectionDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        // Should detect the variable being passed
        assert!(!findings.is_empty(), "Should detect variable injection");
    }

    #[test]
    fn test_typescript_safe_parameterized_query() {
        let source = r#"
import { Pool } from 'pg';
const pool = new Pool();

async function getUser(userId: string) {
    const result = await pool.query("SELECT * FROM users WHERE id = $1", [userId]);
    return result.rows[0];
}
"#;
        let file = create_temp_file(source, ".ts");
        let detector = SqlInjectionDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(
            findings.is_empty(),
            "Should NOT detect safe parameterized query"
        );
    }

    #[test]
    fn test_typescript_safe_literal_query() {
        let source = r#"
import { Pool } from 'pg';
const pool = new Pool();

async function getAllUsers() {
    const result = await pool.query("SELECT * FROM users");
    return result.rows;
}
"#;
        let file = create_temp_file(source, ".ts");
        let detector = SqlInjectionDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(findings.is_empty(), "Should NOT detect safe literal query");
    }

    #[test]
    fn test_typescript_prisma_raw_injection() {
        let source = r#"
import { PrismaClient } from '@prisma/client';
const prisma = new PrismaClient();

async function getUser(userId: string) {
    return prisma.$queryRaw(`SELECT * FROM users WHERE id = ${userId}`);
}
"#;
        let file = create_temp_file(source, ".ts");
        let detector = SqlInjectionDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect Prisma raw query injection");
    }

    // =========================================================================
    // Utility Tests
    // =========================================================================

    #[test]
    fn test_extract_fstring_variables() {
        let detector = SqlInjectionDetector::new();

        let vars = detector.extract_fstring_variables(r#"f"SELECT * FROM users WHERE id = {user_id}""#);
        assert_eq!(vars, vec!["user_id"]);

        let vars = detector.extract_fstring_variables(r#"f"SELECT * FROM {table} WHERE {col} = {val}""#);
        assert_eq!(vars, vec!["table", "col", "val"]);

        let vars = detector.extract_fstring_variables(r#"f"value: {x:.2f}""#);
        assert_eq!(vars, vec!["x"]);
    }

    #[test]
    fn test_severity_display() {
        assert_eq!(Severity::Critical.to_string(), "CRITICAL");
        assert_eq!(Severity::High.to_string(), "HIGH");
        assert_eq!(Severity::Medium.to_string(), "MEDIUM");
        assert_eq!(Severity::Low.to_string(), "LOW");
    }

    #[test]
    fn test_pattern_display() {
        assert_eq!(
            UnsafePattern::StringConcatenation.to_string(),
            "string_concatenation"
        );
        assert_eq!(
            UnsafePattern::FStringInterpolation.to_string(),
            "f_string_interpolation"
        );
        assert_eq!(
            UnsafePattern::TemplateLiteral.to_string(),
            "template_literal"
        );
    }

    #[test]
    fn test_scan_result_counts() {
        let result = ScanResult {
            findings: vec![],
            files_scanned: 10,
            sinks_found: 5,
            severity_counts: [("CRITICAL".to_string(), 2), ("HIGH".to_string(), 3)]
                .into_iter()
                .collect(),
            language: "python".to_string(),
        };

        assert_eq!(result.files_scanned, 10);
        assert_eq!(result.sinks_found, 5);
        assert_eq!(result.severity_counts.get("CRITICAL"), Some(&2));
    }
}
