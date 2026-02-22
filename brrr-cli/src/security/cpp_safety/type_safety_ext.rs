//! Extended type safety checks (D3390 §1.5.2 + §2.5).
//!
//! Detects unchecked access to discriminated types:
//! - TSAF-001: std::optional accessed without has_value() guard
//! - TSAF-002: std::expected accessed without has_value() guard
//! - TSAF-003: std::variant accessed via std::get without holds_alternative
//! - TSAF-004: Smart pointer dereferenced without null check
//! - TSAF-005: std::any accessed via any_cast without type check

use crate::security::common::SourceLocation;

use super::helpers::make_finding;
use super::types::CppSafetyFinding;

/// D3390 §1.5.2 + §2.5: Unchecked discriminated type access.
pub(super) fn check_type_safety_ext(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    let lines: Vec<&str> = source_str.lines().collect();

    for (line_idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }

        // TSAF-001: std::optional unchecked access
        check_optional_access(trimmed, line_idx, &lines, file_path, findings);

        // TSAF-002: std::expected unchecked access
        check_expected_access(trimmed, line_idx, &lines, file_path, findings);

        // TSAF-003: std::variant via std::get without holds_alternative
        check_variant_get(trimmed, line_idx, &lines, file_path, findings);

        // TSAF-004: Smart pointer deref without null check
        check_smart_ptr_deref(trimmed, line_idx, &lines, file_path, findings);

        // TSAF-005: std::any_cast without type check
        check_any_cast(trimmed, line_idx, &lines, file_path, findings);
    }
}

/// Extract variable name from access pattern like `varname.value()`, `*varname`, `varname->`.
/// Returns None if no recognizable variable.
fn extract_var_before_dot(s: &str, dot_pos: usize) -> Option<&str> {
    let before = s[..dot_pos].trim_end();
    // Walk back to find the start of the identifier
    let start = before
        .rfind(|c: char| !c.is_alphanumeric() && c != '_')
        .map(|i| i + 1)
        .unwrap_or(0);
    let var = &before[start..];
    if var.is_empty() || var.starts_with(|c: char| c.is_ascii_digit()) {
        return None;
    }
    Some(var)
}

/// Check if `var_name` has a guard (has_value, boolean test, etc.) in preceding lines.
fn has_guard_in_lookback(
    var_name: &str,
    line_idx: usize,
    lines: &[&str],
    lookback: usize,
    guards: &[&str],
) -> bool {
    let start = line_idx.saturating_sub(lookback);
    for i in start..=line_idx {
        let l = lines[i].trim();
        // Check for guard patterns containing the variable name
        for guard in guards {
            if l.contains(var_name) && l.contains(guard) {
                return true;
            }
        }
        // Check for boolean test: `if (var)`, `if (!var)`, `if (var !=`, `if (var ==`
        if (l.contains("if") || l.contains("while") || l.contains("&&") || l.contains("||"))
            && l.contains(var_name)
        {
            // Heuristic: if the variable appears in a conditional context, it's likely guarded
            return true;
        }
    }
    false
}

/// TSAF-001: `opt.value()`, `*opt`, `opt->member` on optional without guard.
fn check_optional_access(
    trimmed: &str,
    line_idx: usize,
    lines: &[&str],
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    // Look for `.value()` calls — common for optional
    if let Some(pos) = trimmed.find(".value()") {
        // Exclude `.has_value()` and `value_or`
        if trimmed.contains(".has_value()") || trimmed.contains(".value_or(") {
            return;
        }
        // Exclude std::expected error side: `.error().value()` or similar
        if trimmed.contains(".error()") {
            return;
        }
        if let Some(var) = extract_var_before_dot(trimmed, pos) {
            // Must look like an optional variable — heuristic: skip if it looks like
            // a container (map, vector, string) or well-known non-optional types
            if is_likely_non_optional(var, trimmed, lines, line_idx) {
                return;
            }
            let guards = &["has_value", ".value_or(", "nullopt", "emplace"];
            if !has_guard_in_lookback(var, line_idx, lines, 10, guards) {
                let loc = SourceLocation::new(
                    file_path,
                    line_idx + 1,
                    pos + 1,
                    line_idx + 1,
                    pos + ".value()".len(),
                );
                findings.push(make_finding("TSAF-001", loc, trimmed.to_string()));
            }
        }
    }
}

/// TSAF-002: `ex.value()` on expected without guard.
fn check_expected_access(
    trimmed: &str,
    line_idx: usize,
    lines: &[&str],
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    // Look for `.value()` on expected — we need context to distinguish from optional
    // Heuristic: check if variable was declared as expected in lookback
    if let Some(pos) = trimmed.find(".value()") {
        if trimmed.contains(".has_value()") || trimmed.contains(".value_or(") {
            return;
        }
        if let Some(var) = extract_var_before_dot(trimmed, pos) {
            let start = line_idx.saturating_sub(20);
            let mut is_expected = false;
            for i in start..=line_idx {
                let l = lines[i];
                if l.contains("expected") && l.contains(var) {
                    is_expected = true;
                    break;
                }
            }
            if !is_expected {
                return;
            }
            let guards = &["has_value", ".value_or(", "unexpected"];
            if !has_guard_in_lookback(var, line_idx, lines, 10, guards) {
                let loc = SourceLocation::new(
                    file_path,
                    line_idx + 1,
                    pos + 1,
                    line_idx + 1,
                    pos + ".value()".len(),
                );
                findings.push(make_finding("TSAF-002", loc, trimmed.to_string()));
            }
        }
    }
}

/// TSAF-003: `std::get<T>(v)` without `holds_alternative<T>(v)`.
fn check_variant_get(
    trimmed: &str,
    line_idx: usize,
    lines: &[&str],
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    // Find `std::get<` pattern
    let search = "std::get<";
    let mut search_start = 0;
    while let Some(rel_pos) = trimmed[search_start..].find(search) {
        let pos = search_start + rel_pos;
        search_start = pos + search.len();

        // Extract the variant variable from the call args: std::get<T>(var)
        let after_get = &trimmed[pos + search.len()..];
        // Find the closing > then the opening (
        if let Some(gt_pos) = after_get.find(">(") {
            let args_start = gt_pos + 2;
            let args = &after_get[args_start..];
            let var_end = args.find(')').unwrap_or(args.len());
            let var_name = args[..var_end].trim();
            if var_name.is_empty() {
                continue;
            }
            // Extract just the identifier (strip &, *, etc.)
            let var_clean = var_name
                .trim_start_matches('&')
                .trim_start_matches('*')
                .trim();

            // Check for holds_alternative guard
            let guards = &["holds_alternative", "std::visit", "get_if"];
            if !has_guard_in_lookback(var_clean, line_idx, lines, 10, guards) {
                let loc = SourceLocation::new(
                    file_path,
                    line_idx + 1,
                    pos + 1,
                    line_idx + 1,
                    pos + search.len() + gt_pos + 2,
                );
                findings.push(make_finding("TSAF-003", loc, trimmed.to_string()));
            }
        }
    }
}

/// TSAF-004: `*ptr` or `ptr->` on unique_ptr/shared_ptr without null check.
fn check_smart_ptr_deref(
    trimmed: &str,
    line_idx: usize,
    lines: &[&str],
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    // Look for `->` on smart pointer variables
    // Heuristic: check if variable was declared as unique_ptr/shared_ptr in lookback
    if let Some(arrow_pos) = trimmed.find("->") {
        // Extract var before ->
        let before = trimmed[..arrow_pos].trim_end();
        let start = before
            .rfind(|c: char| !c.is_alphanumeric() && c != '_')
            .map(|i| i + 1)
            .unwrap_or(0);
        let var = &before[start..];
        if var.is_empty() || var.starts_with(|c: char| c.is_ascii_digit()) {
            return;
        }

        // Check if this variable is a smart pointer (declared in lookback)
        let lookback_start = line_idx.saturating_sub(30);
        let mut is_smart_ptr = false;
        for i in lookback_start..=line_idx {
            let l = lines[i];
            if (l.contains("unique_ptr") || l.contains("shared_ptr")) && l.contains(var) {
                is_smart_ptr = true;
                break;
            }
        }
        if !is_smart_ptr {
            return;
        }

        // Check for null guard
        let guards = &["nullptr", "!= null", "== null", "!= 0", ".get()", ".reset("];
        if !has_guard_in_lookback(var, line_idx, lines, 10, guards) {
            let loc = SourceLocation::new(
                file_path,
                line_idx + 1,
                arrow_pos + 1,
                line_idx + 1,
                arrow_pos + 3,
            );
            findings.push(make_finding("TSAF-004", loc, trimmed.to_string()));
        }
    }
}

/// TSAF-005: `std::any_cast<T>(a)` without prior `a.type() == typeid(T)`.
fn check_any_cast(
    trimmed: &str,
    line_idx: usize,
    lines: &[&str],
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let search = "any_cast<";
    let mut search_start = 0;
    while let Some(rel_pos) = trimmed[search_start..].find(search) {
        let pos = search_start + rel_pos;
        search_start = pos + search.len();

        // Skip pointer form: `any_cast<T*>` or `any_cast<T>(&a)` (returns nullptr on failure)
        let after = &trimmed[pos + search.len()..];
        if let Some(gt_pos) = after.find('>') {
            let type_arg = &after[..gt_pos];
            // Pointer form returns nullptr — safe
            if type_arg.ends_with('*') {
                continue;
            }
            // Check if argument is passed by pointer (address-of)
            let after_gt = &after[gt_pos + 1..];
            if after_gt.starts_with('(') {
                let args = &after_gt[1..];
                if args.starts_with('&') {
                    continue; // Pointer overload — returns nullptr on mismatch
                }
            }
        }

        // Check for type() == typeid() guard
        let guards = &["type()", "typeid", "any_cast"];
        if !has_guard_in_lookback("type()", line_idx, lines, 10, guards) {
            let loc = SourceLocation::new(
                file_path,
                line_idx + 1,
                pos + 1,
                line_idx + 1,
                pos + search.len(),
            );
            findings.push(make_finding("TSAF-005", loc, trimmed.to_string()));
        }
    }
}

/// Heuristic: skip `.value()` findings on variables that are clearly not optional/expected.
fn is_likely_non_optional(var: &str, _trimmed: &str, lines: &[&str], line_idx: usize) -> bool {
    // Check lookback for the variable's type declaration
    let start = line_idx.saturating_sub(30);
    for i in start..line_idx {
        let l = lines[i];
        if l.contains(var) {
            // If declared as map, vector, string, etc. — not optional
            for non_opt in &[
                "std::map", "std::unordered_map", "std::vector", "std::string",
                "std::set", "std::unordered_set", "std::deque", "std::list",
                "std::array", "std::pair", "std::tuple", "json", "Json",
                "nlohmann", "proto", "Proto",
            ] {
                if l.contains(non_opt) && l.contains(var) {
                    return true;
                }
            }
            // If declared as optional or expected — definitely not non-optional
            if l.contains("optional") || l.contains("expected") {
                return false;
            }
        }
    }
    false
}
