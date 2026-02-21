//! D3390 lifetime safety checks: view dangling, iterator invalidation,
//! initializer_list dangling, return-ref-to-local, lambda escape.

use crate::security::common::SourceLocation;

use super::helpers::*;
use super::types::CppSafetyFinding;

// =============================================================================
// Lifetime Safety Checker (§1.5.1 D3390)
// =============================================================================

/// Non-owning view types that create dangling references when bound to temporaries.
const VIEW_TYPES: &[&str] = &[
    "string_view", "std::string_view",
    "span", "std::span", "gsl::span",
    "QStringView",
];

pub(super) fn check_lifetime_safety(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    check_view_from_temporary(source_str, file_path, findings);
    check_view_as_member(source_str, file_path, findings);
    check_return_view_to_local(source_str, file_path, findings);
}

/// LIFE-001 / LIFE-002: string_view or span initialized from a temporary.
fn check_view_from_temporary(
    source_str: &str,
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let string_temp_patterns = [
        "std::string(", "std::string{",
        "std::to_string(", "to_string(",
        ".str()", ".string()",
        "substr(", ".c_str()",
    ];

    let container_temp_patterns = [
        "std::vector<", "std::vector{",
        "std::array<", "std::array{",
        "std::initializer_list",
    ];

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }

        // Check for string_view bound to string temporary
        let has_sv = trimmed.contains("string_view")
            && (trimmed.contains('=') || trimmed.contains("string_view("));

        if has_sv {
            let rhs = if let Some(eq_pos) = trimmed.find('=') {
                &trimmed[eq_pos + 1..]
            } else {
                trimmed
            };

            for pat in &string_temp_patterns {
                if rhs.contains(pat) {
                    let loc = SourceLocation::new(
                        file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                    );
                    findings.push(make_finding("LIFE-001", loc, trimmed.to_string()));
                    break;
                }
            }

            // Also catch string concatenation (a + b where result is temp string)
            if rhs.contains(" + ") && (rhs.contains("\"") || rhs.contains("str")) {
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("LIFE-001", loc, trimmed.to_string()));
            }
        }

        // Check for span bound to container temporary
        let has_span = (trimmed.contains("span<") || trimmed.contains("span "))
            && (trimmed.contains('=') || trimmed.contains("span(") || trimmed.contains("span{"));

        if has_span {
            let rhs = if let Some(eq_pos) = trimmed.find('=') {
                &trimmed[eq_pos + 1..]
            } else {
                trimmed
            };

            for pat in &container_temp_patterns {
                if rhs.contains(pat) {
                    let loc = SourceLocation::new(
                        file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                    );
                    findings.push(make_finding("LIFE-002", loc, trimmed.to_string()));
                    break;
                }
            }

            // Brace-enclosed initializer list: span<int> s = {1, 2, 3};
            if rhs.trim_start().starts_with('{') {
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("LIFE-002", loc, trimmed.to_string()));
            }
        }
    }
}

/// LIFE-003: string_view or span stored as struct/class member field.
fn check_view_as_member(
    source_str: &str,
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let mut in_struct = false;
    let mut brace_depth = 0i32;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        if (trimmed.starts_with("struct ") || trimmed.starts_with("class "))
            && (trimmed.contains('{') || !trimmed.contains(';'))
        {
            in_struct = true;
            brace_depth = 0;
        }

        if in_struct {
            brace_depth += trimmed.matches('{').count() as i32;
            brace_depth -= trimmed.matches('}').count() as i32;

            if brace_depth <= 0 && trimmed.contains('}') {
                in_struct = false;
                continue;
            }

            // Only look at brace_depth == 1 (direct members, not nested structs)
            if brace_depth != 1 {
                continue;
            }

            if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
                continue;
            }

            // Skip methods, access specifiers
            if trimmed.contains('(') || trimmed.starts_with("public")
                || trimmed.starts_with("private") || trimmed.starts_with("protected")
                || trimmed.starts_with("friend") || trimmed.starts_with("using")
                || trimmed.starts_with("static ") || trimmed.starts_with("constexpr ")
            {
                continue;
            }

            for vt in VIEW_TYPES {
                if trimmed.contains(vt) {
                    let col = trimmed.find(vt).unwrap_or(0);
                    let loc = SourceLocation::new(
                        file_path, line_idx + 1, col + 1, line_idx + 1, col + vt.len() + 1,
                    );
                    findings.push(make_finding("LIFE-003", loc, trimmed.to_string()));
                    break;
                }
            }
        }
    }
}

/// LIFE-004: Function returning string_view/span constructed from local data.
fn check_return_view_to_local(
    source_str: &str,
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let lines: Vec<&str> = source_str.lines().collect();
    let mut func_returns_view = false;
    let mut func_brace_depth = 0i32;
    let mut in_func_body = false;
    let mut local_vars: Vec<String> = Vec::new();

    for (line_idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        if !in_func_body {
            let returns_view = VIEW_TYPES.iter().any(|vt| {
                (trimmed.contains(vt) && trimmed.contains('(')
                    && trimmed.find(vt).unwrap_or(usize::MAX) < trimmed.find('(').unwrap_or(0))
                || (trimmed.contains("->") && trimmed.contains(vt)
                    && trimmed.find("->").unwrap_or(0) < trimmed.find(vt).unwrap_or(usize::MAX))
            });

            if returns_view && (trimmed.contains('{') || trimmed.ends_with('{')) {
                func_returns_view = true;
                in_func_body = true;
                func_brace_depth = 0;
                local_vars.clear();
            }
        }

        if in_func_body {
            func_brace_depth += trimmed.matches('{').count() as i32;
            func_brace_depth -= trimmed.matches('}').count() as i32;

            // Track local variable declarations
            if trimmed.contains('=') && !trimmed.starts_with("return")
                && !trimmed.starts_with("if") && !trimmed.starts_with("for")
            {
                if let Some(eq_pos) = trimmed.find('=') {
                    let before_eq = trimmed[..eq_pos].trim();
                    if let Some(var) = before_eq.split_whitespace().last() {
                        let clean = var.trim_start_matches('*').trim_start_matches('&');
                        if !clean.is_empty() && clean.chars().all(|c| c.is_alphanumeric() || c == '_') {
                            local_vars.push(clean.to_string());
                        }
                    }
                }
            }

            if func_returns_view && trimmed.starts_with("return ") {
                let return_expr = &trimmed["return ".len()..].trim_end_matches(';').trim();

                let is_local_var = local_vars.iter().any(|v| v == return_expr);
                let constructs_view = VIEW_TYPES.iter().any(|vt| return_expr.contains(vt));

                if is_local_var || constructs_view {
                    let loc = SourceLocation::new(
                        file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                    );
                    findings.push(make_finding("LIFE-004", loc, trimmed.to_string()));
                }
            }

            if func_brace_depth <= 0 {
                in_func_body = false;
                func_returns_view = false;
            }
        }
    }
}

// =============================================================================
// Iterator Invalidation Checker (§2.2.2 D3390)
// =============================================================================

/// Methods that invalidate iterators/references on sequence containers.
const INVALIDATING_METHODS: &[&str] = &[
    "push_back", "emplace_back", "push_front", "emplace_front",
    "insert", "emplace", "erase", "clear", "resize", "reserve",
    "assign", "pop_back", "pop_front",
];

pub(super) fn check_iterator_invalidation(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    check_range_for_invalidation(source_str, file_path, findings);
    check_iterator_loop_invalidation(source_str, file_path, findings);
}

/// LIFE-005: Range-for loop body mutates the iterated container.
fn check_range_for_invalidation(
    source_str: &str,
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let lines: Vec<&str> = source_str.lines().collect();

    for (line_idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        if !trimmed.starts_with("for ") && !trimmed.starts_with("for(") {
            continue;
        }

        let Some(colon_pos) = trimmed.find(':') else { continue };
        let after_colon = &trimmed[colon_pos + 1..];
        let Some(paren_pos) = after_colon.find(')') else { continue };
        let container = after_colon[..paren_pos].trim();

        if container.is_empty()
            || container.contains('(')
            || container.contains('<')
            || container.contains('"')
            || !container.chars().all(|c| c.is_alphanumeric() || c == '_')
        {
            continue;
        }

        let mut brace_depth = 0i32;
        let mut started = false;

        for body_line_idx in line_idx..lines.len() {
            let body_trimmed = lines[body_line_idx].trim();
            brace_depth += body_trimmed.matches('{').count() as i32;
            brace_depth -= body_trimmed.matches('}').count() as i32;

            if body_trimmed.contains('{') {
                started = true;
            }

            if started && brace_depth <= 0 {
                break;
            }

            if !started {
                continue;
            }

            for method in INVALIDATING_METHODS {
                let pattern = format!("{container}.{method}(");
                if body_trimmed.contains(&pattern) {
                    let loc = SourceLocation::new(
                        file_path,
                        body_line_idx + 1,
                        1,
                        body_line_idx + 1,
                        body_trimmed.len(),
                    );
                    let mut finding = make_finding("LIFE-005", loc, body_trimmed.to_string());
                    finding.metadata.insert("container".to_string(), container.to_string());
                    finding.metadata.insert("method".to_string(), method.to_string());
                    findings.push(finding);
                }
            }
        }
    }
}

/// LIFE-006: Iterator loop body mutates the container the iterator came from.
fn check_iterator_loop_invalidation(
    source_str: &str,
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let lines: Vec<&str> = source_str.lines().collect();

    for (line_idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        if !trimmed.starts_with("for ") && !trimmed.starts_with("for(") {
            continue;
        }

        let container = extract_iterator_container(trimmed);
        let Some(container) = container else { continue };

        let mut brace_depth = 0i32;
        let mut started = false;

        for body_line_idx in line_idx..lines.len() {
            let body_trimmed = lines[body_line_idx].trim();
            brace_depth += body_trimmed.matches('{').count() as i32;
            brace_depth -= body_trimmed.matches('}').count() as i32;

            if body_trimmed.contains('{') {
                started = true;
            }

            if started && brace_depth <= 0 {
                break;
            }

            if !started || body_line_idx == line_idx {
                continue;
            }

            for method in INVALIDATING_METHODS {
                let pattern = format!("{container}.{method}(");
                if body_trimmed.contains(&pattern) {
                    let loc = SourceLocation::new(
                        file_path,
                        body_line_idx + 1,
                        1,
                        body_line_idx + 1,
                        body_trimmed.len(),
                    );
                    let mut finding = make_finding("LIFE-006", loc, body_trimmed.to_string());
                    finding.metadata.insert("container".to_string(), container.to_string());
                    finding.metadata.insert("method".to_string(), method.to_string());
                    findings.push(finding);
                }
            }
        }
    }
}

/// Extract container name from iterator-based for loop init.
fn extract_iterator_container(for_line: &str) -> Option<String> {
    for begin_fn in &[".begin()", ".cbegin()", ".rbegin()"] {
        if let Some(pos) = for_line.find(begin_fn) {
            let before_dot = &for_line[..pos];
            let container = before_dot.split(|c: char| !c.is_alphanumeric() && c != '_')
                .filter(|s| !s.is_empty())
                .last()?;
            if container.chars().all(|c| c.is_alphanumeric() || c == '_') {
                return Some(container.to_string());
            }
        }
    }
    None
}

// =============================================================================
// Initializer List Dangling Checker (§2.2.3 D3390)
// =============================================================================

pub(super) fn check_initializer_list_dangling(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    let mut in_struct = false;
    let mut brace_depth = 0i32;
    let mut in_function = false;
    let mut func_brace_depth = 0i32;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }

        // Track struct scope for LIFE-010
        if (trimmed.starts_with("struct ") || trimmed.starts_with("class "))
            && (trimmed.contains('{') || !trimmed.contains(';'))
        {
            in_struct = true;
            brace_depth = 0;
        }

        if in_struct {
            brace_depth += trimmed.matches('{').count() as i32;
            brace_depth -= trimmed.matches('}').count() as i32;

            if brace_depth <= 0 && trimmed.contains('}') {
                in_struct = false;
            }

            // LIFE-010: initializer_list as class member
            if brace_depth == 1 && trimmed.contains("initializer_list")
                && !trimmed.contains('(')
                && !trimmed.starts_with("friend")
                && !trimmed.starts_with("using")
            {
                let col = trimmed.find("initializer_list").unwrap_or(0);
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, col + 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("LIFE-010", loc, trimmed.to_string()));
            }
        }

        // Track function scope for LIFE-008
        if !in_function && trimmed.contains('(') && trimmed.contains('{')
            && !trimmed.starts_with("struct") && !trimmed.starts_with("class")
            && !trimmed.starts_with("enum") && !trimmed.starts_with("namespace")
        {
            in_function = true;
            func_brace_depth = 0;
        }

        if in_function {
            func_brace_depth += trimmed.matches('{').count() as i32;
            func_brace_depth -= trimmed.matches('}').count() as i32;

            // LIFE-008: Local variable of type initializer_list
            if trimmed.contains("initializer_list") && trimmed.contains('=') {
                let col = trimmed.find("initializer_list").unwrap_or(0);
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, col + 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("LIFE-008", loc, trimmed.to_string()));
            }

            if func_brace_depth <= 0 {
                in_function = false;
            }
        }
    }
}

// =============================================================================
// Return Reference/Pointer to Local Checker (§2.2 D3390)
// =============================================================================

/// LIFE-011: Function returning reference or pointer to a local variable.
pub(super) fn check_return_ref_to_local(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    let lines: Vec<&str> = source_str.lines().collect();
    let mut func_returns_ref = false;
    let mut func_returns_ptr = false;
    let mut in_func_body = false;
    let mut func_brace_depth = 0i32;
    let mut local_vars: Vec<String> = Vec::new();

    for (line_idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        if !in_func_body {
            let is_lambda = trimmed.contains("[&]") || trimmed.contains("[=]")
                || trimmed.contains("[this]") || trimmed.contains("[&,")
                || trimmed.contains(", &]") || trimmed.contains("[=,");

            if !is_lambda {
                let returns_ref = (trimmed.contains("& ") || trimmed.contains("&\t"))
                    && trimmed.contains('(')
                    && !trimmed.starts_with("//")
                    && !trimmed.contains("operator")
                    && trimmed.find('&').unwrap_or(usize::MAX)
                        < trimmed.find('(').unwrap_or(0);

                let returns_ptr = trimmed.contains("* ")
                    && trimmed.contains('(')
                    && !trimmed.starts_with("//")
                    && !trimmed.contains("operator")
                    && trimmed.find('*').unwrap_or(usize::MAX)
                        < trimmed.find('(').unwrap_or(0);

                if (returns_ref || returns_ptr)
                    && (trimmed.contains('{') || trimmed.ends_with('{'))
                {
                    func_returns_ref = returns_ref;
                    func_returns_ptr = returns_ptr;
                    in_func_body = true;
                    func_brace_depth = 0;
                    local_vars.clear();
                }
            }
        }

        if in_func_body {
            func_brace_depth += trimmed.matches('{').count() as i32;
            func_brace_depth -= trimmed.matches('}').count() as i32;

            // Track local variable declarations
            if trimmed.contains('=') && !trimmed.starts_with("return")
                && !trimmed.starts_with("if") && !trimmed.starts_with("for")
            {
                if let Some(eq_pos) = trimmed.find('=') {
                    let before_eq = trimmed[..eq_pos].trim();
                    if let Some(var) = before_eq.split_whitespace().last() {
                        let clean = var.trim_start_matches('*').trim_start_matches('&');
                        if !clean.is_empty() && clean.chars().all(|c| c.is_alphanumeric() || c == '_') {
                            local_vars.push(clean.to_string());
                        }
                    }
                }
            }

            if trimmed.starts_with("return ") && (func_returns_ref || func_returns_ptr) {
                let return_expr = trimmed["return ".len()..].trim_end_matches(';').trim();

                let returned_var = if return_expr.starts_with('&') {
                    return_expr[1..].trim()
                } else {
                    return_expr
                };

                if local_vars.iter().any(|v| v == returned_var) {
                    let loc = SourceLocation::new(
                        file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                    );
                    findings.push(make_finding("LIFE-011", loc, trimmed.to_string()));
                }
            }

            if func_brace_depth <= 0 {
                in_func_body = false;
                func_returns_ref = false;
                func_returns_ptr = false;
            }
        }
    }
}

/// LIFE-013: Lambda with [&] capture escaping scope.
/// LIFE-014: std::ref/std::cref usage (potential dangling wrapper).
pub(super) fn check_lambda_ref_escape(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }

        // LIFE-013
        if trimmed.contains("[&]") || trimmed.contains("[&,") || trimmed.contains(", &]") {
            let lambda_pos = trimmed.find("[&]")
                .or_else(|| trimmed.find("[&,"))
                .or_else(|| trimmed.find(", &]"))
                .unwrap_or(0);

            let has_escape_mechanism = trimmed.contains("std::function")
                || trimmed.contains("std::thread")
                || trimmed.contains("std::async")
                || trimmed.contains("std::jthread")
                || trimmed.contains("detach");

            let lambda_returned_directly = trimmed.starts_with("return ")
                && trimmed[7..].trim().starts_with("[&");

            let return_before_lambda = trimmed.starts_with("return ")
                && lambda_pos > 7;
            let is_inline_use = return_before_lambda && !has_escape_mechanism;

            if !is_inline_use && (has_escape_mechanism || lambda_returned_directly) {
                let col = lambda_pos;
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, col + 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("LIFE-013", loc, trimmed.to_string()));
            }
        }

        // LIFE-014: std::ref / std::cref
        for ref_fn in &["std::ref(", "std::cref("] {
            if trimmed.contains(ref_fn) {
                let is_risky = trimmed.contains("thread")
                    || trimmed.contains("async")
                    || trimmed.contains("bind")
                    || trimmed.contains("function");

                if is_risky {
                    let col = trimmed.find(ref_fn).unwrap_or(0);
                    let loc = SourceLocation::new(
                        file_path, line_idx + 1, col + 1, line_idx + 1, trimmed.len(),
                    );
                    findings.push(make_finding("LIFE-014", loc, trimmed.to_string()));
                }
            }
        }
    }
}
