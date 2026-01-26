//! Shared utility functions for injection detection.
//!
//! This module provides common functionality used across multiple
//! injection scanners, reducing code duplication.
//!
//! # Utilities Provided
//!
//! - **Language Detection**: Determine programming language from file paths
//! - **Template Variable Extraction**: Extract interpolation variables from strings
//! - **Code Snippet Extraction**: Get context around findings for display
//! - **File Extension Mapping**: Convert extensions to language identifiers

use std::path::Path;

use once_cell::sync::Lazy;
use regex::Regex;
use rustc_hash::FxHashSet;

// =============================================================================
// Language Detection
// =============================================================================

/// File extension to language mapping.
static EXTENSION_TO_LANGUAGE: Lazy<Vec<(&'static str, &'static str)>> = Lazy::new(|| {
    vec![
        // Python
        ("py", "python"),
        ("pyw", "python"),
        ("pyi", "python"),
        // JavaScript/TypeScript
        ("js", "javascript"),
        ("jsx", "javascript"),
        ("mjs", "javascript"),
        ("cjs", "javascript"),
        ("ts", "typescript"),
        ("tsx", "typescript"),
        ("mts", "typescript"),
        // Ruby
        ("rb", "ruby"),
        ("erb", "ruby"),
        ("rake", "ruby"),
        // Go
        ("go", "go"),
        // Rust
        ("rs", "rust"),
        // Java
        ("java", "java"),
        // C/C++
        ("c", "c"),
        ("h", "c"),
        ("cpp", "cpp"),
        ("cc", "cpp"),
        ("cxx", "cpp"),
        ("hpp", "cpp"),
        ("hxx", "cpp"),
        // C#
        ("cs", "csharp"),
        // PHP
        ("php", "php"),
        // Shell
        ("sh", "bash"),
        ("bash", "bash"),
        ("zsh", "bash"),
        // SQL
        ("sql", "sql"),
        // HTML/Templates
        ("html", "html"),
        ("htm", "html"),
        ("vue", "vue"),
        ("svelte", "svelte"),
    ]
});

/// Detect programming language from a file path.
///
/// Uses the file extension to determine the language. Returns `None`
/// if the extension is not recognized.
///
/// # Arguments
///
/// * `path` - Path to the source file (can be string or Path)
///
/// # Returns
///
/// Language identifier string if recognized, None otherwise.
///
/// # Examples
///
/// ```ignore
/// assert_eq!(detect_language_from_path("src/main.rs"), Some("rust"));
/// assert_eq!(detect_language_from_path("app.py"), Some("python"));
/// assert_eq!(detect_language_from_path("script.js"), Some("javascript"));
/// assert_eq!(detect_language_from_path("unknown.xyz"), None);
/// ```
#[must_use]
pub fn detect_language_from_path(path: impl AsRef<Path>) -> Option<&'static str> {
    let ext = path.as_ref().extension()?.to_str()?;
    let ext_lower = ext.to_lowercase();

    EXTENSION_TO_LANGUAGE
        .iter()
        .find(|(e, _)| *e == ext_lower)
        .map(|(_, lang)| *lang)
}

/// Get all file extensions for a given language.
///
/// # Arguments
///
/// * `language` - Language identifier (e.g., "python", "javascript")
///
/// # Returns
///
/// Set of extensions associated with the language.
#[must_use]
pub fn extensions_for_language(language: &str) -> FxHashSet<&'static str> {
    EXTENSION_TO_LANGUAGE
        .iter()
        .filter(|(_, lang)| *lang == language)
        .map(|(ext, _)| *ext)
        .collect()
}

/// Check if a file path is a web template file.
///
/// Template files often have special injection considerations.
#[must_use]
pub fn is_template_file(path: impl AsRef<Path>) -> bool {
    let path = path.as_ref();

    if let Some(ext) = path.extension().and_then(|e| e.to_str()) {
        let ext_lower = ext.to_lowercase();
        return matches!(
            ext_lower.as_str(),
            "erb"
                | "ejs"
                | "jinja"
                | "jinja2"
                | "j2"
                | "hbs"
                | "handlebars"
                | "pug"
                | "jade"
                | "njk"
                | "twig"
                | "liquid"
                | "mustache"
        );
    }

    // Check for double extensions like .html.erb
    if let Some(stem) = path.file_stem().and_then(|s| s.to_str()) {
        if stem.ends_with(".html") || stem.ends_with(".htm") {
            return true;
        }
    }

    false
}

// =============================================================================
// Template Variable Extraction
// =============================================================================

/// Regex for Python f-string interpolation: {variable} or {expression}
static PYTHON_FSTRING_REGEX: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"\{([^{}]+)\}").expect("Invalid regex"));

/// Regex for JavaScript template literal: ${expression}
static JS_TEMPLATE_REGEX: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"\$\{([^}]+)\}").expect("Invalid regex"));

/// Regex for Jinja2/Django template variables: {{ variable }}
static JINJA2_VAR_REGEX: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"\{\{\s*([^}]+?)\s*\}\}").expect("Invalid regex"));

/// Regex for Jinja2/Django template tags: {% tag %}
static JINJA2_TAG_REGEX: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"\{%\s*([^%]+?)\s*%\}").expect("Invalid regex"));

/// Regex for Ruby string interpolation: #{expression}
static RUBY_INTERPOLATION_REGEX: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"#\{([^}]+)\}").expect("Invalid regex"));

/// Regex for PHP variable interpolation: $variable or {$variable}
static PHP_VAR_REGEX: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"(?:\$([a-zA-Z_][a-zA-Z0-9_]*)|\{\$([^}]+)\})").expect("Invalid regex"));

/// Extract template variables from a string.
///
/// Detects interpolation patterns from multiple languages:
/// - Python f-strings: `{name}`, `{user.id}`
/// - JavaScript template literals: `${name}`, `${user.id}`
/// - Jinja2/Django: `{{ name }}`, `{% for item in items %}`
/// - Ruby: `#{name}`, `#{user.id}`
/// - PHP: `$name`, `{$user->id}`
///
/// # Arguments
///
/// * `template` - The template string to analyze
///
/// # Returns
///
/// Vector of extracted variable/expression strings (deduplicated).
///
/// # Examples
///
/// ```ignore
/// let vars = extract_template_variables("Hello {name}, your id is {user.id}");
/// assert!(vars.contains(&"name".to_string()));
/// assert!(vars.contains(&"user.id".to_string()));
///
/// let js_vars = extract_template_variables("Hello ${name}!");
/// assert!(js_vars.contains(&"name".to_string()));
/// ```
#[must_use]
pub fn extract_template_variables(template: &str) -> Vec<String> {
    let mut vars = FxHashSet::default();

    // Python f-string pattern
    for cap in PYTHON_FSTRING_REGEX.captures_iter(template) {
        if let Some(m) = cap.get(1) {
            let var = m.as_str().trim();
            // Filter out format specifiers
            if let Some(idx) = var.find(':') {
                vars.insert(var[..idx].trim().to_string());
            } else {
                vars.insert(var.to_string());
            }
        }
    }

    // JavaScript template literal pattern
    for cap in JS_TEMPLATE_REGEX.captures_iter(template) {
        if let Some(m) = cap.get(1) {
            vars.insert(m.as_str().trim().to_string());
        }
    }

    // Jinja2/Django variable pattern
    for cap in JINJA2_VAR_REGEX.captures_iter(template) {
        if let Some(m) = cap.get(1) {
            let var = m.as_str().trim();
            // Extract the base variable (before any filters)
            if let Some(idx) = var.find('|') {
                vars.insert(var[..idx].trim().to_string());
            } else {
                vars.insert(var.to_string());
            }
        }
    }

    // Jinja2/Django tag pattern (for completeness)
    for cap in JINJA2_TAG_REGEX.captures_iter(template) {
        if let Some(m) = cap.get(1) {
            let tag_content = m.as_str().trim();
            // Extract variables from common tags like 'for item in items'
            if tag_content.starts_with("for ") {
                let parts: Vec<&str> = tag_content.split_whitespace().collect();
                if parts.len() >= 4 && parts[2] == "in" {
                    vars.insert(parts[3].to_string());
                }
            }
        }
    }

    // Ruby interpolation pattern
    for cap in RUBY_INTERPOLATION_REGEX.captures_iter(template) {
        if let Some(m) = cap.get(1) {
            vars.insert(m.as_str().trim().to_string());
        }
    }

    // PHP variable pattern
    for cap in PHP_VAR_REGEX.captures_iter(template) {
        if let Some(m) = cap.get(1) {
            vars.insert(m.as_str().to_string());
        } else if let Some(m) = cap.get(2) {
            vars.insert(m.as_str().to_string());
        }
    }

    vars.into_iter().collect()
}

/// Extract variables specifically from Python f-string syntax.
///
/// More precise than `extract_template_variables` for Python-specific use cases.
///
/// # Arguments
///
/// * `fstring` - The f-string content (without the f" prefix)
///
/// # Returns
///
/// Vector of variable names found in interpolation expressions.
#[must_use]
pub fn extract_fstring_variables(fstring: &str) -> Vec<String> {
    let mut vars = Vec::new();

    for cap in PYTHON_FSTRING_REGEX.captures_iter(fstring) {
        if let Some(m) = cap.get(1) {
            let expr = m.as_str().trim();

            // Skip format specifiers
            let expr = if let Some(idx) = expr.find(':') {
                &expr[..idx]
            } else {
                expr
            };

            // Extract the base identifier from expressions like 'user.name' or 'items[0]'
            let base = extract_base_identifier(expr);
            if !base.is_empty() {
                vars.push(base.to_string());
            }
        }
    }

    vars
}

/// Extract variables from JavaScript template literal.
///
/// # Arguments
///
/// * `template` - The template literal content (without backticks)
///
/// # Returns
///
/// Vector of variable names/expressions found in ${...} interpolations.
#[must_use]
pub fn extract_template_literal_variables(template: &str) -> Vec<String> {
    let mut vars = Vec::new();

    for cap in JS_TEMPLATE_REGEX.captures_iter(template) {
        if let Some(m) = cap.get(1) {
            vars.push(m.as_str().trim().to_string());
        }
    }

    vars
}

/// Extract the base identifier from an expression.
///
/// Handles common patterns:
/// - `user.name` -> `user`
/// - `items[0]` -> `items`
/// - `get_user()` -> `get_user`
/// - `data.users[i].name` -> `data`
fn extract_base_identifier(expr: &str) -> &str {
    let expr = expr.trim();

    // Find first non-identifier character
    let end = expr
        .find(|c: char| !c.is_alphanumeric() && c != '_')
        .unwrap_or(expr.len());

    &expr[..end]
}

// =============================================================================
// Code Snippet Extraction
// =============================================================================

/// Extract a code snippet around a specific line.
///
/// Returns context lines before and after the target line.
///
/// # Arguments
///
/// * `source` - The full source code bytes
/// * `line` - The 0-indexed line number to center on
/// * `context_lines` - Number of lines to include before and after
///
/// # Returns
///
/// String containing the code snippet with context.
#[must_use]
pub fn extract_code_snippet(source: &[u8], line: usize, context_lines: usize) -> String {
    let source_str = std::str::from_utf8(source).unwrap_or("");
    let lines: Vec<&str> = source_str.lines().collect();

    if lines.is_empty() {
        return String::new();
    }

    let start = line.saturating_sub(context_lines);
    let end = (line + context_lines + 1).min(lines.len());

    lines[start..end].join("\n")
}

/// Extract a code snippet with line numbers.
///
/// Formats the snippet with line numbers for display.
///
/// # Arguments
///
/// * `source` - The full source code bytes
/// * `line` - The 0-indexed line number to center on
/// * `context_lines` - Number of lines to include before and after
///
/// # Returns
///
/// String containing the numbered code snippet.
#[must_use]
pub fn extract_code_snippet_numbered(source: &[u8], line: usize, context_lines: usize) -> String {
    let source_str = std::str::from_utf8(source).unwrap_or("");
    let lines: Vec<&str> = source_str.lines().collect();

    if lines.is_empty() {
        return String::new();
    }

    let start = line.saturating_sub(context_lines);
    let end = (line + context_lines + 1).min(lines.len());

    let line_width = end.to_string().len();

    lines[start..end]
        .iter()
        .enumerate()
        .map(|(i, line_content)| {
            let line_num = start + i + 1; // 1-indexed display
            let marker = if start + i == line { ">" } else { " " };
            format!("{} {:>width$} | {}", marker, line_num, line_content, width = line_width)
        })
        .collect::<Vec<_>>()
        .join("\n")
}

// =============================================================================
// String Analysis Utilities
// =============================================================================

/// Check if a string appears to contain user input references.
///
/// Looks for common patterns indicating user-controlled data.
///
/// # Arguments
///
/// * `text` - The text to analyze
/// * `language` - The programming language context
///
/// # Returns
///
/// True if the text likely references user input.
#[must_use]
pub fn contains_user_input_reference(text: &str, language: &str) -> bool {
    let patterns: &[&str] = match language {
        "python" => &[
            "request.",
            "input(",
            "sys.argv",
            "os.environ",
            "Query(",
            "Body(",
            "Form(",
        ],
        "javascript" | "typescript" => &[
            "req.body",
            "req.query",
            "req.params",
            "req.cookies",
            "req.headers",
            "ctx.request",
            "ctx.query",
            "process.argv",
            "process.env",
        ],
        "ruby" => &["params[", "request.", "cookies[", "session[", "ARGV", "ENV["],
        "go" => &[
            "r.URL.Query",
            "r.Form",
            "r.PostForm",
            "r.Body",
            "os.Args",
            "os.Getenv",
        ],
        "php" => &[
            "$_GET",
            "$_POST",
            "$_REQUEST",
            "$_COOKIE",
            "$_SERVER",
            "$_FILES",
            "$argv",
        ],
        _ => &["input", "request", "argv", "env"],
    };

    patterns.iter().any(|p| text.contains(p))
}

/// Check if a string is a safe constant name.
///
/// Constants (typically UPPER_CASE) are generally considered safe
/// as they are not user-controlled.
///
/// # Arguments
///
/// * `name` - The identifier name to check
///
/// # Returns
///
/// True if the name appears to be a constant.
#[must_use]
pub fn is_constant_name(name: &str) -> bool {
    // All uppercase with underscores is typically a constant
    !name.is_empty()
        && name
            .chars()
            .all(|c| c.is_uppercase() || c.is_ascii_digit() || c == '_')
}

/// Check if a string literal is a plain static string.
///
/// Static strings without interpolation are generally safe.
///
/// # Arguments
///
/// * `text` - The string literal text (including quotes)
///
/// # Returns
///
/// True if the string is a plain literal without interpolation.
#[must_use]
pub fn is_static_string(text: &str) -> bool {
    // Check for interpolation markers
    let has_interpolation = text.contains("${")    // JS template
        || text.contains("{")                       // Python f-string (need to check prefix)
        || text.contains("#{")                      // Ruby
        || text.contains("{{")                      // Jinja2
        || text.starts_with("f\"")                  // Python f-string
        || text.starts_with("f'")                   // Python f-string
        || text.starts_with("`");                   // JS template literal

    !has_interpolation
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detect_language_from_path() {
        assert_eq!(detect_language_from_path("src/main.rs"), Some("rust"));
        assert_eq!(detect_language_from_path("app.py"), Some("python"));
        assert_eq!(detect_language_from_path("script.js"), Some("javascript"));
        assert_eq!(detect_language_from_path("component.tsx"), Some("typescript"));
        assert_eq!(detect_language_from_path("main.go"), Some("go"));
        assert_eq!(detect_language_from_path("unknown.xyz"), None);
    }

    #[test]
    fn test_detect_language_case_insensitive() {
        assert_eq!(detect_language_from_path("file.PY"), Some("python"));
        assert_eq!(detect_language_from_path("file.Js"), Some("javascript"));
    }

    #[test]
    fn test_extensions_for_language() {
        let py_exts = extensions_for_language("python");
        assert!(py_exts.contains("py"));
        assert!(py_exts.contains("pyw"));

        let js_exts = extensions_for_language("javascript");
        assert!(js_exts.contains("js"));
        assert!(js_exts.contains("jsx"));
    }

    #[test]
    fn test_is_template_file() {
        assert!(is_template_file("template.erb"));
        assert!(is_template_file("view.ejs"));
        assert!(is_template_file("page.jinja2"));
        assert!(is_template_file("component.hbs"));
        assert!(!is_template_file("main.py"));
        assert!(!is_template_file("app.js"));
    }

    #[test]
    fn test_extract_python_fstring_variables() {
        let vars = extract_template_variables("Hello {name}, your id is {user.id}");
        assert!(vars.contains(&"name".to_string()));
        assert!(vars.contains(&"user.id".to_string()));
    }

    #[test]
    fn test_extract_js_template_variables() {
        let vars = extract_template_variables("Hello ${name}, count: ${items.length}");
        assert!(vars.contains(&"name".to_string()));
        assert!(vars.contains(&"items.length".to_string()));
    }

    #[test]
    fn test_extract_jinja2_variables() {
        let vars = extract_template_variables("Hello {{ name }}, items: {{ items|length }}");
        assert!(vars.contains(&"name".to_string()));
        assert!(vars.contains(&"items".to_string()));
    }

    #[test]
    fn test_extract_ruby_interpolation() {
        let vars = extract_template_variables("Hello #{name}, id: #{user.id}");
        assert!(vars.contains(&"name".to_string()));
        assert!(vars.contains(&"user.id".to_string()));
    }

    #[test]
    fn test_extract_fstring_variables() {
        let vars = extract_fstring_variables("Hello {name}, age: {user.age:d}");
        assert!(vars.contains(&"name".to_string()));
        assert!(vars.contains(&"user".to_string()));
    }

    #[test]
    fn test_extract_code_snippet() {
        let source = b"line 0\nline 1\nline 2\nline 3\nline 4";
        let snippet = extract_code_snippet(source, 2, 1);
        assert!(snippet.contains("line 1"));
        assert!(snippet.contains("line 2"));
        assert!(snippet.contains("line 3"));
    }

    #[test]
    fn test_extract_code_snippet_numbered() {
        let source = b"first\nsecond\nthird\nfourth\nfifth";
        let snippet = extract_code_snippet_numbered(source, 2, 1);
        assert!(snippet.contains("2 |"));
        assert!(snippet.contains("3 |"));
        assert!(snippet.contains("4 |"));
        assert!(snippet.contains(">"));  // marker for target line
    }

    #[test]
    fn test_contains_user_input_reference() {
        assert!(contains_user_input_reference("request.args.get('x')", "python"));
        assert!(contains_user_input_reference("req.body.name", "javascript"));
        assert!(contains_user_input_reference("params[:id]", "ruby"));
        assert!(!contains_user_input_reference("constant_value", "python"));
    }

    #[test]
    fn test_is_constant_name() {
        assert!(is_constant_name("MAX_SIZE"));
        assert!(is_constant_name("API_KEY"));
        assert!(is_constant_name("VERSION_2"));
        assert!(!is_constant_name("userName"));
        assert!(!is_constant_name("user_name"));
    }

    #[test]
    fn test_is_static_string() {
        assert!(is_static_string("\"hello world\""));
        assert!(is_static_string("'simple string'"));
        assert!(!is_static_string("f\"hello {name}\""));
        assert!(!is_static_string("`hello ${name}`"));
        assert!(!is_static_string("\"hello #{name}\""));
    }

    #[test]
    fn test_extract_base_identifier() {
        assert_eq!(extract_base_identifier("user"), "user");
        assert_eq!(extract_base_identifier("user.name"), "user");
        assert_eq!(extract_base_identifier("items[0]"), "items");
        assert_eq!(extract_base_identifier("get_user()"), "get_user");
    }
}
