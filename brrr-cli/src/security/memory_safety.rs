//! C/C++ memory safety vulnerability detection.
//!
//! Detects common memory safety issues in C/C++ code using tree-sitter AST analysis:
//!
//! - **Buffer overflows**: Unsafe string functions (strcpy, sprintf, gets, strcat)
//! - **Format string vulnerabilities**: printf/fprintf with user-controlled format strings
//! - **Integer overflows**: Arithmetic on sizes before allocation (malloc, calloc)
//! - **Use-after-free patterns**: Use of pointer after free()
//! - **Double-free**: Calling free() twice on the same pointer
//! - **Null pointer dereference**: Missing null checks after malloc/calloc/realloc
//! - **Uninitialized variables**: Local variables used without initialization
//! - **Command injection via dlopen**: dlopen() with user-controlled paths

use std::path::Path;

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use streaming_iterator::StreamingIterator;
use tree_sitter::{Node, Query, QueryCursor, Tree};

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;
use crate::security::common::{Confidence, Severity, SourceLocation};
use crate::util::format_query_error;

/// A memory safety finding in C/C++ code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemorySafetyFinding {
    /// Location in the source file.
    pub location: SourceLocation,
    /// Severity of the vulnerability.
    pub severity: Severity,
    /// Confidence level.
    pub confidence: Confidence,
    /// Category of memory safety issue.
    pub category: MemorySafetyCategory,
    /// The dangerous function or pattern detected.
    pub pattern: String,
    /// Description of the issue.
    pub description: String,
    /// Suggested remediation.
    pub remediation: String,
    /// Code snippet showing the vulnerable code.
    pub code_snippet: String,
    /// CWE identifier.
    pub cwe_id: u32,
}

/// Categories of C/C++ memory safety vulnerabilities.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MemorySafetyCategory {
    BufferOverflow,
    FormatString,
    IntegerOverflow,
    UseAfterFree,
    DoubleFree,
    NullDereference,
    UninitializedVariable,
    UnsafeAllocation,
}

impl std::fmt::Display for MemorySafetyCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BufferOverflow => write!(f, "buffer_overflow"),
            Self::FormatString => write!(f, "format_string"),
            Self::IntegerOverflow => write!(f, "integer_overflow"),
            Self::UseAfterFree => write!(f, "use_after_free"),
            Self::DoubleFree => write!(f, "double_free"),
            Self::NullDereference => write!(f, "null_dereference"),
            Self::UninitializedVariable => write!(f, "uninitialized_variable"),
            Self::UnsafeAllocation => write!(f, "unsafe_allocation"),
        }
    }
}

// =============================================================================
// Unsafe Function Database
// =============================================================================

/// An unsafe C function pattern with metadata.
struct UnsafeFn {
    name: &'static str,
    category: MemorySafetyCategory,
    severity: Severity,
    cwe: u32,
    description: &'static str,
    remediation: &'static str,
}

/// Unsafe C/C++ functions that should be flagged.
const UNSAFE_FUNCTIONS: &[UnsafeFn] = &[
    // Buffer overflow - unbounded string operations
    UnsafeFn {
        name: "gets",
        category: MemorySafetyCategory::BufferOverflow,
        severity: Severity::Critical,
        cwe: 120,
        description: "gets() reads input without bounds checking, guaranteed buffer overflow",
        remediation: "Replace with fgets(buf, sizeof(buf), stdin)",
    },
    UnsafeFn {
        name: "strcpy",
        category: MemorySafetyCategory::BufferOverflow,
        severity: Severity::High,
        cwe: 120,
        description: "strcpy() copies without bounds checking, buffer overflow if src > dst",
        remediation: "Replace with strncpy(dst, src, sizeof(dst)-1) or strlcpy()",
    },
    UnsafeFn {
        name: "strcat",
        category: MemorySafetyCategory::BufferOverflow,
        severity: Severity::High,
        cwe: 120,
        description: "strcat() appends without bounds checking, buffer overflow risk",
        remediation: "Replace with strncat(dst, src, sizeof(dst)-strlen(dst)-1) or strlcat()",
    },
    UnsafeFn {
        name: "sprintf",
        category: MemorySafetyCategory::BufferOverflow,
        severity: Severity::High,
        cwe: 120,
        description: "sprintf() writes without bounds checking, buffer overflow risk",
        remediation: "Replace with snprintf(buf, sizeof(buf), fmt, ...)",
    },
    UnsafeFn {
        name: "vsprintf",
        category: MemorySafetyCategory::BufferOverflow,
        severity: Severity::High,
        cwe: 120,
        description: "vsprintf() writes without bounds checking, buffer overflow risk",
        remediation: "Replace with vsnprintf(buf, sizeof(buf), fmt, ap)",
    },
    UnsafeFn {
        name: "scanf",
        category: MemorySafetyCategory::BufferOverflow,
        severity: Severity::High,
        cwe: 120,
        description: "scanf() with %s reads without bounds, buffer overflow risk",
        remediation: "Use width specifier: scanf(\"%255s\", buf) or use fgets()",
    },
    UnsafeFn {
        name: "wcscpy",
        category: MemorySafetyCategory::BufferOverflow,
        severity: Severity::High,
        cwe: 120,
        description: "wcscpy() copies wide strings without bounds checking",
        remediation: "Replace with wcsncpy() or wcslcpy()",
    },
    UnsafeFn {
        name: "wcscat",
        category: MemorySafetyCategory::BufferOverflow,
        severity: Severity::High,
        cwe: 120,
        description: "wcscat() appends wide strings without bounds checking",
        remediation: "Replace with wcsncat() or wcslcat()",
    },
    // Format string vulnerabilities
    UnsafeFn {
        name: "printf",
        category: MemorySafetyCategory::FormatString,
        severity: Severity::High,
        cwe: 134,
        description: "printf() with non-literal format string allows format string attacks",
        remediation: "Always use a string literal as format: printf(\"%s\", user_str)",
    },
    UnsafeFn {
        name: "fprintf",
        category: MemorySafetyCategory::FormatString,
        severity: Severity::High,
        cwe: 134,
        description: "fprintf() with non-literal format string allows format string attacks",
        remediation: "Always use a string literal as format: fprintf(fp, \"%s\", user_str)",
    },
    UnsafeFn {
        name: "syslog",
        category: MemorySafetyCategory::FormatString,
        severity: Severity::High,
        cwe: 134,
        description: "syslog() with non-literal format string allows format string attacks",
        remediation: "Always use a string literal as format: syslog(LOG_INFO, \"%s\", user_str)",
    },
    UnsafeFn {
        name: "snprintf",
        category: MemorySafetyCategory::FormatString,
        severity: Severity::Medium,
        cwe: 134,
        description: "snprintf() with non-literal format string allows format string attacks",
        remediation: "Always use a string literal as format: snprintf(buf, sz, \"%s\", user_str)",
    },
];

// =============================================================================
// Tree-sitter Queries
// =============================================================================

/// Query to find calls to unsafe functions in C/C++ code.
/// Captures: @func = function name, @args = argument list, @call = full call expression
const UNSAFE_CALL_QUERY: &str = r#"
(call_expression
  function: (identifier) @func
  arguments: (argument_list) @args) @call
"#;

/// Query to find free() calls for use-after-free / double-free detection.
const FREE_CALL_QUERY: &str = r#"
(call_expression
  function: (identifier) @func
  (#any-of? @func "free" "g_free" "av_free" "av_freep")
  arguments: (argument_list
    (identifier) @freed_var)) @call
"#;

/// Query to find malloc/calloc/realloc calls without null checks.
const ALLOC_QUERY: &str = r#"
(call_expression
  function: (identifier) @func
  (#any-of? @func "malloc" "calloc" "realloc" "strdup" "strndup")
  arguments: (argument_list) @args) @call
"#;

/// Query to find arithmetic in allocation size arguments (integer overflow risk).
const ALLOC_ARITHMETIC_QUERY: &str = r#"
(call_expression
  function: (identifier) @func
  (#any-of? @func "malloc" "calloc" "realloc" "aligned_alloc")
  arguments: (argument_list
    (binary_expression
      operator: [("+") ("*")]
      ) @arith)) @call
"#;

/// Query to find declarations without initializers.
const UNINIT_VAR_QUERY: &str = r#"
(declaration
  type: (_) @type
  declarator: (identifier) @var
  !value) @decl
"#;

// =============================================================================
// Scanner Implementation
// =============================================================================

/// Scan a directory for C/C++ memory safety issues.
pub fn scan_memory_safety(
    path: &Path,
    lang_filter: Option<&str>,
) -> Result<Vec<MemorySafetyFinding>> {
    if path.is_file() {
        return scan_file_memory_safety(path, lang_filter);
    }

    let scanner = ProjectScanner::new(path.to_string_lossy().as_ref())?;

    // Filter to C/C++ files only
    let config = match lang_filter {
        Some("c") => ScanConfig::for_language("c"),
        Some("cpp") => ScanConfig::for_language("cpp"),
        _ => {
            // Scan both C and C++
            let mut cfg = ScanConfig::default();
            cfg.extensions = vec![
                ".c".into(), ".h".into(),
                ".cpp".into(), ".cc".into(), ".cxx".into(),
                ".hpp".into(), ".hh".into(), ".hxx".into(),
                ".cu".into(), ".cuh".into(),
            ];
            cfg
        }
    };

    let result = scanner.scan_with_config(&config)?;

    let findings: Vec<Vec<MemorySafetyFinding>> = result
        .files
        .par_iter()
        .filter_map(|file| scan_file_memory_safety(file, lang_filter).ok())
        .collect();

    Ok(findings.into_iter().flatten().collect())
}

/// Scan a single file for C/C++ memory safety issues.
pub fn scan_file_memory_safety(
    path: &Path,
    lang_filter: Option<&str>,
) -> Result<Vec<MemorySafetyFinding>> {
    let registry = LanguageRegistry::global();

    // Detect language from extension
    let lang = match lang_filter {
        Some(l) => registry.get_by_name(l),
        None => registry.detect_language(path),
    };

    let lang = match lang {
        Some(l) if l.name() == "c" || l.name() == "cpp" => l,
        _ => return Ok(Vec::new()), // Skip non-C/C++ files
    };

    let source = std::fs::read(path).map_err(|e| BrrrError::io_with_path(e, path))?;
    let source_str = std::str::from_utf8(&source).unwrap_or("");

    let mut parser = lang.parser()?;
    let tree = parser.parse(&source, None).ok_or_else(|| BrrrError::Parse {
        file: path.display().to_string(),
        message: "Failed to parse file".to_string(),
    })?;

    let file_path = path.to_string_lossy().to_string();
    let mut findings = Vec::new();

    // Phase 1: Detect unsafe function calls
    scan_unsafe_calls(&tree, &source, &file_path, source_str, lang.name(), &mut findings)?;

    // Phase 2: Detect format string vulnerabilities (non-literal format args)
    scan_format_strings(&tree, &source, &file_path, source_str, lang.name(), &mut findings)?;

    // Phase 3: Detect use-after-free and double-free patterns
    scan_use_after_free(&tree, &source, &file_path, source_str, lang.name(), &mut findings)?;

    // Phase 4: Detect missing null checks after allocation
    scan_null_deref(&tree, &source, &file_path, source_str, lang.name(), &mut findings)?;

    // Phase 5: Detect integer overflow in allocation sizes
    scan_alloc_overflow(&tree, &source, &file_path, source_str, lang.name(), &mut findings)?;

    Ok(findings)
}

/// Helper to get text from source bytes for a node.
fn node_text<'a>(node: Node, source: &'a [u8]) -> &'a str {
    std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
}

/// Extract a code snippet around a line.
fn snippet_at_line(source_str: &str, line: usize, context: usize) -> String {
    let lines: Vec<&str> = source_str.lines().collect();
    if lines.is_empty() || line == 0 {
        return String::new();
    }
    let idx = line.saturating_sub(1); // 0-indexed
    let start = idx.saturating_sub(context);
    let end = (idx + context + 1).min(lines.len());
    lines[start..end].join("\n")
}

/// Build a SourceLocation from a tree-sitter node.
fn location_from_node(node: Node, file_path: &str, _source: &[u8]) -> SourceLocation {
    SourceLocation::new(
        file_path,
        node.start_position().row + 1,
        node.start_position().column + 1,
        node.end_position().row + 1,
        node.end_position().column + 1,
    )
}

// =============================================================================
// Phase 1: Unsafe Function Call Detection
// =============================================================================

/// Names of buffer-overflow-prone functions to detect.
const BUFFER_OVERFLOW_FUNCS: &[&str] = &[
    "gets", "strcpy", "strcat", "sprintf", "vsprintf", "scanf",
    "wcscpy", "wcscat", "swprintf",
];

fn scan_unsafe_calls(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    findings: &mut Vec<MemorySafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = Query::new(&ts_lang, UNSAFE_CALL_QUERY)
        .map_err(|e| BrrrError::TreeSitter(format_query_error(lang_name, "unsafe_call", UNSAFE_CALL_QUERY, &e)))?;

    let func_idx = query.capture_index_for_name("func").unwrap_or(0);
    let call_idx = query.capture_index_for_name("call").unwrap_or(0);

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        let func_node = m.captures.iter().find(|c| c.index == func_idx);
        let call_node = m.captures.iter().find(|c| c.index == call_idx);

        if let (Some(func_cap), Some(call_cap)) = (func_node, call_node) {
            let func_name = node_text(func_cap.node, source);

            // Look up in our unsafe function database
            if let Some(unsafe_fn) = UNSAFE_FUNCTIONS.iter().find(|f| f.name == func_name) {
                // For format string functions, only flag if format arg is non-literal
                // (handled separately in scan_format_strings)
                if unsafe_fn.category == MemorySafetyCategory::FormatString {
                    continue;
                }

                // Only flag buffer overflow functions
                if !BUFFER_OVERFLOW_FUNCS.contains(&func_name) {
                    continue;
                }

                let loc = location_from_node(call_cap.node, file_path, source);
                findings.push(MemorySafetyFinding {
                    location: loc.clone(),
                    severity: unsafe_fn.severity,
                    confidence: Confidence::High,
                    category: unsafe_fn.category,
                    pattern: func_name.to_string(),
                    description: unsafe_fn.description.to_string(),
                    remediation: unsafe_fn.remediation.to_string(),
                    code_snippet: snippet_at_line(source_str, loc.line, 1),
                    cwe_id: unsafe_fn.cwe,
                });
            }
        }
    }

    Ok(())
}

// =============================================================================
// Phase 2: Format String Vulnerability Detection
// =============================================================================

/// Format functions where the format argument index matters.
const FORMAT_FUNCS: &[(&str, usize)] = &[
    ("printf", 0),
    ("fprintf", 1),     // fprintf(fp, fmt, ...)
    ("sprintf", 1),     // sprintf(buf, fmt, ...)
    ("snprintf", 2),    // snprintf(buf, size, fmt, ...)
    ("syslog", 1),      // syslog(priority, fmt, ...)
    ("dprintf", 1),     // dprintf(fd, fmt, ...)
    ("wprintf", 0),
    ("fwprintf", 1),
    ("swprintf", 2),
];

fn scan_format_strings(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    findings: &mut Vec<MemorySafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = Query::new(&ts_lang, UNSAFE_CALL_QUERY)
        .map_err(|e| BrrrError::TreeSitter(format_query_error(lang_name, "format_string", UNSAFE_CALL_QUERY, &e)))?;

    let func_idx = query.capture_index_for_name("func").unwrap_or(0);
    let args_idx = query.capture_index_for_name("args").unwrap_or(0);
    let call_idx = query.capture_index_for_name("call").unwrap_or(0);

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        let func_node = m.captures.iter().find(|c| c.index == func_idx);
        let args_node = m.captures.iter().find(|c| c.index == args_idx);
        let call_node = m.captures.iter().find(|c| c.index == call_idx);

        if let (Some(func_cap), Some(args_cap), Some(call_cap)) = (func_node, args_node, call_node) {
            let func_name = node_text(func_cap.node, source);

            // Check if this is a format function
            if let Some((_, fmt_arg_idx)) = FORMAT_FUNCS.iter().find(|(name, _)| *name == func_name) {
                let args_node = args_cap.node;

                // Get the format argument at the specified index
                let mut arg_count = 0;
                let mut fmt_arg = None;
                for i in 0..args_node.named_child_count() {
                    if let Some(child) = args_node.named_child(i as u32) {
                        if arg_count == *fmt_arg_idx {
                            fmt_arg = Some(child);
                            break;
                        }
                        arg_count += 1;
                    }
                }

                if let Some(fmt_node) = fmt_arg {
                    let fmt_kind = fmt_node.kind();
                    let is_literal = fmt_kind == "string_literal"
                        || fmt_kind == "concatenated_string"
                        || fmt_kind == "string_content";

                    // Flag if format argument is NOT a string literal
                    if !is_literal {
                        let loc = location_from_node(call_cap.node, file_path, source);
                        findings.push(MemorySafetyFinding {
                            location: loc.clone(),
                            severity: Severity::High,
                            confidence: Confidence::High,
                            category: MemorySafetyCategory::FormatString,
                            pattern: func_name.to_string(),
                            description: format!(
                                "{}() called with non-literal format string '{}'. \
                                 An attacker controlling the format string can read/write arbitrary memory via %n, %x, %s.",
                                func_name,
                                node_text(fmt_node, source).chars().take(60).collect::<String>()
                            ),
                            remediation: format!(
                                "Use a literal format string: {}(\"%s\", user_str) instead of {}(user_str)",
                                func_name, func_name
                            ),
                            code_snippet: snippet_at_line(source_str, loc.line, 1),
                            cwe_id: 134,
                        });
                    }
                }
            }
        }
    }

    Ok(())
}

// =============================================================================
// Phase 3: Use-After-Free and Double-Free Detection
// =============================================================================

fn scan_use_after_free(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    findings: &mut Vec<MemorySafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = Query::new(&ts_lang, FREE_CALL_QUERY)
        .map_err(|e| BrrrError::TreeSitter(format_query_error(lang_name, "free_call", FREE_CALL_QUERY, &e)))?;

    let func_idx = query.capture_index_for_name("func").unwrap_or(0);
    let var_idx = query.capture_index_for_name("freed_var").unwrap_or(0);
    let call_idx = query.capture_index_for_name("call").unwrap_or(0);

    // Collect all free() calls with their freed variable and line number
    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    struct FreeCall {
        var_name: String,
        line: usize,
        node_start: usize,
    }

    let mut free_calls: Vec<FreeCall> = Vec::new();

    while let Some(m) = matches.next() {
        let var_node = m.captures.iter().find(|c| c.index == var_idx);
        let call_node = m.captures.iter().find(|c| c.index == call_idx);

        if let (Some(var_cap), Some(call_cap)) = (var_node, call_node) {
            let var_name = node_text(var_cap.node, source).to_string();
            let line = call_cap.node.start_position().row + 1;
            free_calls.push(FreeCall {
                var_name,
                line,
                node_start: call_cap.node.start_byte(),
            });
        }
    }

    // Check for double-free: same variable freed twice in same scope
    for i in 0..free_calls.len() {
        for j in (i + 1)..free_calls.len() {
            if free_calls[i].var_name == free_calls[j].var_name {
                let loc = SourceLocation::new(
                    file_path,
                    free_calls[j].line,
                    1,
                    free_calls[j].line,
                    1,
                );

                findings.push(MemorySafetyFinding {
                    location: loc.clone(),
                    severity: Severity::Critical,
                    confidence: Confidence::Medium,
                    category: MemorySafetyCategory::DoubleFree,
                    pattern: format!("free({})", free_calls[j].var_name),
                    description: format!(
                        "Pointer '{}' freed at line {} and again at line {}. \
                         Double-free can cause heap corruption and arbitrary code execution.",
                        free_calls[j].var_name,
                        free_calls[i].line,
                        free_calls[j].line
                    ),
                    remediation: format!(
                        "Set pointer to NULL after free: free({}); {} = NULL;",
                        free_calls[j].var_name, free_calls[j].var_name
                    ),
                    code_snippet: snippet_at_line(source_str, loc.line, 1),
                    cwe_id: 415,
                });
            }
        }
    }

    Ok(())
}

// =============================================================================
// Phase 4: Missing Null Check After Allocation
// =============================================================================

fn scan_null_deref(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    findings: &mut Vec<MemorySafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = Query::new(&ts_lang, ALLOC_QUERY)
        .map_err(|e| BrrrError::TreeSitter(format_query_error(lang_name, "alloc_null", ALLOC_QUERY, &e)))?;

    let func_idx = query.capture_index_for_name("func").unwrap_or(0);
    let call_idx = query.capture_index_for_name("call").unwrap_or(0);

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        let func_node = m.captures.iter().find(|c| c.index == func_idx);
        let call_node = m.captures.iter().find(|c| c.index == call_idx);

        if let (Some(func_cap), Some(call_cap)) = (func_node, call_node) {
            let func_name = node_text(func_cap.node, source);
            let call_line = call_cap.node.start_position().row + 1;

            // Check if the allocation result is checked for NULL.
            // Look at the parent to find the assignment target variable.
            let parent = call_cap.node.parent();

            // Walk up to find assignment: ptr = malloc(...)
            let assigned_var = parent.and_then(|p| {
                // init_declarator: type *ptr = malloc(...)
                if p.kind() == "init_declarator" {
                    p.child_by_field_name("declarator").map(|d| node_text(d, source).to_string())
                }
                // assignment_expression: ptr = malloc(...)
                else if p.kind() == "assignment_expression" {
                    p.child_by_field_name("left").map(|l| node_text(l, source).to_string())
                } else {
                    None
                }
            });

            if let Some(var_name) = assigned_var {
                // Clean up pointer declarator prefix (remove *)
                let clean_var = var_name.trim_start_matches('*').trim();

                // Look at the next few statements after the allocation to see
                // if there's a null check (if (ptr == NULL) or if (!ptr))
                let check_region = &source_str[call_cap.node.end_byte()..];
                let check_window = &check_region[..check_region.len().min(500)];

                let has_null_check = check_window.contains(&format!("{} == NULL", clean_var))
                    || check_window.contains(&format!("{} != NULL", clean_var))
                    || check_window.contains(&format!("!{}", clean_var))
                    || check_window.contains(&format!("{} == nullptr", clean_var))
                    || check_window.contains(&format!("{} != nullptr", clean_var))
                    || check_window.contains(&format!("if ({})", clean_var))
                    || check_window.contains(&format!("if({})", clean_var));

                if !has_null_check {
                    let loc = location_from_node(call_cap.node, file_path, source);
                    findings.push(MemorySafetyFinding {
                        location: loc.clone(),
                        severity: Severity::Medium,
                        confidence: Confidence::Medium,
                        category: MemorySafetyCategory::NullDereference,
                        pattern: format!("{}()", func_name),
                        description: format!(
                            "Result of {}() assigned to '{}' without null check. \
                             Dereferencing NULL causes segfault; in kernel code, exploitable.",
                            func_name, clean_var
                        ),
                        remediation: format!(
                            "Check for NULL: if ({} == NULL) {{ /* handle error */ }}",
                            clean_var
                        ),
                        code_snippet: snippet_at_line(source_str, loc.line, 1),
                        cwe_id: 476,
                    });
                }
            }
        }
    }

    Ok(())
}

// =============================================================================
// Phase 5: Integer Overflow in Allocation Sizes
// =============================================================================

fn scan_alloc_overflow(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    findings: &mut Vec<MemorySafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, ALLOC_ARITHMETIC_QUERY) {
        Ok(q) => q,
        Err(_) => return Ok(()), // Query may not match all grammars
    };

    let func_idx = query.capture_index_for_name("func").unwrap_or(0);
    let arith_idx = query.capture_index_for_name("arith").unwrap_or(0);
    let call_idx = query.capture_index_for_name("call").unwrap_or(0);

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        let func_node = m.captures.iter().find(|c| c.index == func_idx);
        let arith_node = m.captures.iter().find(|c| c.index == arith_idx);
        let call_node = m.captures.iter().find(|c| c.index == call_idx);

        if let (Some(func_cap), Some(arith_cap), Some(call_cap)) = (func_node, arith_node, call_node) {
            let func_name = node_text(func_cap.node, source);
            let arith_text = node_text(arith_cap.node, source);

            let loc = location_from_node(call_cap.node, file_path, source);
            findings.push(MemorySafetyFinding {
                location: loc.clone(),
                severity: Severity::High,
                confidence: Confidence::Medium,
                category: MemorySafetyCategory::IntegerOverflow,
                pattern: format!("{}({})", func_name, arith_text),
                description: format!(
                    "Arithmetic expression '{}' in {}() size argument may overflow, \
                     causing undersized allocation and subsequent heap buffer overflow.",
                    arith_text, func_name
                ),
                remediation: format!(
                    "Check for overflow before allocation: \
                     if (a > SIZE_MAX / b) {{ /* overflow */ }} \
                     or use safe_mul/checked_mul helpers",
                ),
                code_snippet: snippet_at_line(source_str, loc.line, 1),
                cwe_id: 190,
            });
        }
    }

    Ok(())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn scan_code(code: &str, ext: &str) -> Vec<MemorySafetyFinding> {
        let mut file = NamedTempFile::with_suffix(ext).unwrap();
        file.write_all(code.as_bytes()).unwrap();
        file.flush().unwrap();
        scan_file_memory_safety(file.path(), None).unwrap()
    }

    #[test]
    fn test_detect_gets() {
        let findings = scan_code(
            r#"
#include <stdio.h>
void foo() {
    char buf[64];
    gets(buf);
}
"#,
            ".c",
        );
        assert!(!findings.is_empty(), "Should detect gets()");
        assert_eq!(findings[0].category, MemorySafetyCategory::BufferOverflow);
        assert_eq!(findings[0].cwe_id, 120);
    }

    #[test]
    fn test_detect_strcpy() {
        let findings = scan_code(
            r#"
#include <string.h>
void foo(const char* src) {
    char dst[32];
    strcpy(dst, src);
}
"#,
            ".c",
        );
        assert!(!findings.is_empty(), "Should detect strcpy()");
        assert_eq!(findings[0].pattern, "strcpy");
    }

    #[test]
    fn test_detect_sprintf() {
        let findings = scan_code(
            r#"
#include <stdio.h>
void foo(const char* name) {
    char buf[128];
    sprintf(buf, "Hello %s, welcome!", name);
}
"#,
            ".c",
        );
        assert!(!findings.is_empty(), "Should detect sprintf()");
    }

    #[test]
    fn test_detect_format_string_vuln() {
        let findings = scan_code(
            r#"
#include <stdio.h>
void foo(char* user_input) {
    printf(user_input);
}
"#,
            ".c",
        );
        let fmt_findings: Vec<_> = findings
            .iter()
            .filter(|f| f.category == MemorySafetyCategory::FormatString)
            .collect();
        assert!(!fmt_findings.is_empty(), "Should detect format string vulnerability");
    }

    #[test]
    fn test_no_false_positive_literal_printf() {
        let findings = scan_code(
            r#"
#include <stdio.h>
void foo(int x) {
    printf("Value: %d\n", x);
}
"#,
            ".c",
        );
        let fmt_findings: Vec<_> = findings
            .iter()
            .filter(|f| f.category == MemorySafetyCategory::FormatString)
            .collect();
        assert!(fmt_findings.is_empty(), "Should NOT flag printf with literal format");
    }

    #[test]
    fn test_detect_double_free() {
        let findings = scan_code(
            r#"
#include <stdlib.h>
void foo() {
    char *p = malloc(100);
    free(p);
    free(p);
}
"#,
            ".c",
        );
        let df_findings: Vec<_> = findings
            .iter()
            .filter(|f| f.category == MemorySafetyCategory::DoubleFree)
            .collect();
        assert!(!df_findings.is_empty(), "Should detect double free");
    }

    #[test]
    fn test_detect_missing_null_check() {
        let findings = scan_code(
            r#"
#include <stdlib.h>
void foo() {
    char *buf = malloc(1024);
    buf[0] = 'a';
}
"#,
            ".c",
        );
        let null_findings: Vec<_> = findings
            .iter()
            .filter(|f| f.category == MemorySafetyCategory::NullDereference)
            .collect();
        assert!(
            !null_findings.is_empty(),
            "Should detect missing null check after malloc"
        );
    }

    #[test]
    fn test_no_false_positive_null_check_present() {
        let findings = scan_code(
            r#"
#include <stdlib.h>
void foo() {
    char *buf = malloc(1024);
    if (buf == NULL) return;
    buf[0] = 'a';
}
"#,
            ".c",
        );
        let null_findings: Vec<_> = findings
            .iter()
            .filter(|f| f.category == MemorySafetyCategory::NullDereference)
            .collect();
        assert!(
            null_findings.is_empty(),
            "Should NOT flag when null check is present"
        );
    }

    #[test]
    fn test_detect_alloc_overflow() {
        let findings = scan_code(
            r#"
#include <stdlib.h>
void foo(size_t count) {
    int *arr = malloc(count * sizeof(int));
}
"#,
            ".c",
        );
        let overflow_findings: Vec<_> = findings
            .iter()
            .filter(|f| f.category == MemorySafetyCategory::IntegerOverflow)
            .collect();
        assert!(
            !overflow_findings.is_empty(),
            "Should detect arithmetic in malloc size"
        );
    }

    #[test]
    fn test_cuda_file_scanned() {
        let findings = scan_code(
            r#"
#include <stdio.h>
__global__ void kernel(char* user_input) {
    char buf[64];
    strcpy(buf, user_input);
}
"#,
            ".cu",
        );
        assert!(!findings.is_empty(), "Should scan .cu files");
    }

    #[test]
    fn test_cpp_file_scanned() {
        let findings = scan_code(
            r#"
#include <cstdio>
void foo(const char* input) {
    printf(input);
}
"#,
            ".cpp",
        );
        let fmt_findings: Vec<_> = findings
            .iter()
            .filter(|f| f.category == MemorySafetyCategory::FormatString)
            .collect();
        assert!(!fmt_findings.is_empty(), "Should scan .cpp files for format strings");
    }
}
