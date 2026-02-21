//! Original 9-axiom checkers: InitSafe, TypeSafe, NullSafe, MemSafe,
//! RaceFree, LeakFree, DetDrop, Performance, AntiPattern.

use streaming_iterator::StreamingIterator;
use tree_sitter::{Query, QueryCursor, Tree};

use crate::error::Result;
use crate::security::common::SourceLocation;

use super::helpers::*;
use super::types::CppSafetyFinding;

// =============================================================================
// InitSafe Checker
// =============================================================================

pub(super) fn check_init_safe(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    // INIT-001 / INIT-002: Struct/class fields without NSDMI
    check_field_nsdmi(tree, source, file_path, source_str, findings);

    // INIT-004: Uninitialized local variables
    check_uninit_locals(tree, source, file_path, source_str, lang_name, findings)?;

    Ok(())
}

/// INIT-001 / INIT-002: Walk struct/class field declarations, flag those without default values.
fn check_field_nsdmi(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let field_list_nodes = collect_nodes(tree.root_node(), &["field_declaration_list"]);

    for field_list in field_list_nodes {
        for i in 0..field_list.named_child_count() {
            let Some(child) = field_list.named_child(i as u32) else { continue };
            if child.kind() != "field_declaration" {
                continue;
            }

            let field_text = node_text(child, source);

            // Skip access specifiers, friend declarations, using declarations, type aliases
            if field_text.starts_with("public")
                || field_text.starts_with("private")
                || field_text.starts_with("protected")
                || field_text.starts_with("friend")
                || field_text.starts_with("using")
                || field_text.starts_with("typedef")
            {
                continue;
            }

            // Skip static fields, constexpr, and function declarations (methods)
            if field_text.contains("static ")
                || field_text.contains("constexpr ")
                || field_text.contains('(')
            {
                continue;
            }

            // Check if field has a default value (NSDMI)
            let has_default = child.child_by_field_name("default_value").is_some();
            // Also check text for `= ...` or `{...}` initializers
            let has_text_init = field_text.contains(" = ")
                || field_text.contains("= ")
                || (field_text.contains('{') && !field_text.starts_with('{'));

            if !has_default && !has_text_init {
                let loc = location_from_node(child, file_path);

                // INIT-002: Check if it's a padding/reserved array
                let is_padding_array = (field_text.contains("pad")
                    || field_text.contains("reserved")
                    || field_text.contains("unused"))
                    && field_text.contains('[');

                let rule_id = if is_padding_array { "INIT-002" } else { "INIT-001" };
                let snippet = snippet_at_line(source_str, loc.line, 0);
                let mut finding = make_finding(rule_id, loc, snippet);
                finding.metadata.insert("field".to_string(), field_text.trim().to_string());
                findings.push(finding);
            }
        }
    }
}

/// INIT-004: Uninitialized local variables via tree-sitter query.
fn check_uninit_locals(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, UNINIT_VAR_QUERY) {
        Ok(q) => q,
        Err(_) => return Ok(()),
    };

    let var_idx = query.capture_index_for_name("var").unwrap_or(0);
    let decl_idx = query.capture_index_for_name("decl").unwrap_or(0);

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        let var_node = m.captures.iter().find(|c| c.index == var_idx);
        let decl_node = m.captures.iter().find(|c| c.index == decl_idx);

        if let (Some(var_cap), Some(decl_cap)) = (var_node, decl_node) {
            // Only flag variables inside function bodies
            let in_function = is_inside_function(decl_cap.node);
            if !in_function {
                continue;
            }

            let var_name = node_text(var_cap.node, source);
            // Skip loop variables, catch parameters, etc.
            if var_name.starts_with('_') || var_name == "i" || var_name == "j" || var_name == "k" {
                continue;
            }

            let loc = location_from_node(decl_cap.node, file_path);
            let snippet = snippet_at_line(source_str, loc.line, 0);
            let mut finding = make_finding("INIT-004", loc, snippet);
            finding.metadata.insert("variable".to_string(), var_name.to_string());
            findings.push(finding);
        }
    }

    Ok(())
}

// =============================================================================
// TypeSafe Checker
// =============================================================================

pub(super) fn check_type_safe(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    // TYPE-001: Plain enum (not enum class)
    if is_cpp {
        check_plain_enum(tree, source, file_path, source_str, lang_name, findings)?;
    }

    // TYPE-003: Single-arg constructor without explicit (C++ only)
    if is_cpp {
        check_missing_explicit(source_str, file_path, findings);
    }

    // TYPE-004: reinterpret_cast
    if is_cpp {
        for m in find_pattern(source_str, "reinterpret_cast<") {
            findings.push(make_finding_from_text("TYPE-004", file_path, &m));
        }
    }

    // TYPE-005: static_cast from enum
    if is_cpp {
        check_static_cast_enum(source_str, file_path, findings);
    }

    // TYPE-006: C-style cast in C++ code
    if is_cpp {
        check_c_style_cast(source_str, file_path, findings);
    }

    Ok(())
}

/// TYPE-001: Detect plain `enum` (not `enum class` / `enum struct`) using tree-sitter.
fn check_plain_enum(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, ENUM_QUERY) {
        Ok(q) => q,
        Err(_) => return Ok(()),
    };

    let enum_idx = query.capture_index_for_name("enum_spec").unwrap_or(0);

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        let enum_node = m.captures.iter().find(|c| c.index == enum_idx);
        if let Some(enum_cap) = enum_node {
            let text = node_text(enum_cap.node, source);
            // Check if it has `class` or `struct` keyword after `enum`
            let is_scoped = text.starts_with("enum class") || text.starts_with("enum struct");
            if !is_scoped {
                // Skip forward declarations without body
                if !text.contains('{') {
                    continue;
                }
                let loc = location_from_node(enum_cap.node, file_path);
                let snippet = snippet_at_line(source_str, loc.line, 0);
                findings.push(make_finding("TYPE-001", loc, snippet));
            }
        }
    }

    Ok(())
}

/// TYPE-003: Find single-argument constructors without `explicit`.
fn check_missing_explicit(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();
        // Skip comments
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }
        // Skip lines with `explicit`
        if trimmed.contains("explicit") {
            continue;
        }
        // Skip destructors, operators, and templates
        if trimmed.contains('~') || trimmed.contains("operator") || trimmed.starts_with("template") {
            continue;
        }
        // Skip lines that are clearly not constructors
        if trimmed.starts_with("return")
            || trimmed.starts_with("if")
            || trimmed.starts_with("for")
            || trimmed.starts_with("while")
            || trimmed.starts_with("switch")
            || trimmed.starts_with('#')
        {
            continue;
        }

        if let Some(paren_start) = trimmed.find('(') {
            if let Some(paren_end) = trimmed.rfind(')') {
                if paren_start < paren_end {
                    let before_paren = trimmed[..paren_start].trim();
                    let inside_parens = trimmed[paren_start + 1..paren_end].trim();

                    // Must look like a constructor: single capitalized identifier before paren
                    if before_paren.is_empty()
                        || before_paren.contains(' ')
                        || before_paren.contains('<')
                        || before_paren.contains('>')
                        || !before_paren.chars().next().map_or(false, |c| c.is_uppercase())
                    {
                        continue;
                    }

                    // Must have exactly one parameter (no commas, not empty, not void)
                    if inside_parens.is_empty()
                        || inside_parens == "void"
                        || inside_parens.contains(',')
                    {
                        continue;
                    }

                    // Must end with constructor-like suffix
                    let after_paren = trimmed[paren_end + 1..].trim();
                    if !(after_paren.starts_with('{')
                        || after_paren.starts_with(':')
                        || after_paren.starts_with(';')
                        || after_paren.is_empty())
                    {
                        continue;
                    }

                    let loc = SourceLocation::new(
                        file_path,
                        line_idx + 1,
                        1,
                        line_idx + 1,
                        trimmed.len(),
                    );
                    let finding = make_finding("TYPE-003", loc, trimmed.to_string());
                    findings.push(finding);
                }
            }
        }
    }
}

/// TYPE-005: static_cast from enum values.
fn check_static_cast_enum(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    for m in find_pattern(source_str, "static_cast<int>") {
        let after = &source_str.lines().nth(m.line - 1).unwrap_or("")[m.column..];
        if after.contains("::") {
            findings.push(make_finding_from_text("TYPE-005", file_path, &m));
        }
    }
    for m in find_pattern(source_str, "static_cast<unsigned") {
        let after = &source_str.lines().nth(m.line - 1).unwrap_or("")[m.column..];
        if after.contains("::") {
            findings.push(make_finding_from_text("TYPE-005", file_path, &m));
        }
    }
}

/// TYPE-006: C-style casts in C++ code.
fn check_c_style_cast(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let cast_types = [
        "(int)", "(unsigned)", "(char)", "(long)", "(double)", "(float)",
        "(void*)", "(void *)", "(char*)", "(char *)",
        "(uint8_t)", "(uint16_t)", "(uint32_t)", "(uint64_t)",
        "(int8_t)", "(int16_t)", "(int32_t)", "(int64_t)",
        "(size_t)", "(uintptr_t)", "(intptr_t)",
    ];

    for cast_type in &cast_types {
        for m in find_pattern(source_str, cast_type) {
            let line = source_str.lines().nth(m.line - 1).unwrap_or("");
            let before = &line[..m.column.saturating_sub(1)];
            if before.trim_end().ends_with(',') || before.trim_end().ends_with('(') {
                continue;
            }
            if before.contains("sizeof") {
                continue;
            }
            findings.push(make_finding_from_text("TYPE-006", file_path, &m));
        }
    }
}

// =============================================================================
// NullSafe Checker
// =============================================================================

pub(super) fn check_null_safe(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    // NULL-002: Allocation without null check
    check_alloc_null(tree, source, file_path, source_str, lang_name, findings)?;

    // NULL-003: Adjacent pointer + count fields
    check_ptr_count_pair(tree, source, file_path, source_str, findings);

    Ok(())
}

/// NULL-002: malloc/calloc/realloc without null check.
fn check_alloc_null(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, CALL_QUERY) {
        Ok(q) => q,
        Err(_) => return Ok(()),
    };

    let func_idx = query.capture_index_for_name("func").unwrap_or(0);
    let call_idx = query.capture_index_for_name("call").unwrap_or(0);

    let alloc_fns = ["malloc", "calloc", "realloc", "strdup", "strndup"];

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        let func_node = m.captures.iter().find(|c| c.index == func_idx);
        let call_node = m.captures.iter().find(|c| c.index == call_idx);

        if let (Some(func_cap), Some(call_cap)) = (func_node, call_node) {
            let func_name = node_text(func_cap.node, source);
            if !alloc_fns.contains(&func_name) {
                continue;
            }

            // Check if result is assigned and tested for NULL
            let parent = call_cap.node.parent();
            let assigned_var = parent.and_then(|p| {
                if p.kind() == "init_declarator" {
                    p.child_by_field_name("declarator").map(|d| node_text(d, source).to_string())
                } else if p.kind() == "assignment_expression" {
                    p.child_by_field_name("left").map(|l| node_text(l, source).to_string())
                } else {
                    None
                }
            });

            if let Some(var_name) = assigned_var {
                let clean_var = var_name.trim_start_matches('*').trim();
                let check_region = &source_str[call_cap.node.end_byte()..];
                let check_window = &check_region[..check_region.len().min(500)];

                let has_null_check = check_window.contains(&format!("{clean_var} == NULL"))
                    || check_window.contains(&format!("{clean_var} != NULL"))
                    || check_window.contains(&format!("!{clean_var}"))
                    || check_window.contains(&format!("{clean_var} == nullptr"))
                    || check_window.contains(&format!("{clean_var} != nullptr"))
                    || check_window.contains(&format!("if ({clean_var})"))
                    || check_window.contains(&format!("if({clean_var})"));

                if !has_null_check {
                    let loc = location_from_node(call_cap.node, file_path);
                    let snippet = snippet_at_line(source_str, loc.line, 1);
                    let mut finding = make_finding("NULL-002", loc, snippet);
                    finding.metadata.insert("function".to_string(), func_name.to_string());
                    finding.metadata.insert("variable".to_string(), clean_var.to_string());
                    findings.push(finding);
                }
            }
        }
    }

    Ok(())
}

/// NULL-003: Adjacent pointer + count/size fields in structs.
fn check_ptr_count_pair(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let field_list_nodes = collect_nodes(tree.root_node(), &["field_declaration_list"]);

    for field_list in field_list_nodes {
        let mut prev_was_pointer = false;
        let mut pointer_line = 0usize;

        for i in 0..field_list.named_child_count() {
            let Some(child) = field_list.named_child(i as u32) else { continue };
            if child.kind() != "field_declaration" {
                prev_was_pointer = false;
                continue;
            }

            let text = node_text(child, source);
            let is_pointer = text.contains('*');
            let is_count = text.contains("size")
                || text.contains("count")
                || text.contains("length")
                || text.contains("len")
                || text.contains("num_")
                || text.contains("n_");

            if prev_was_pointer && is_count && !is_pointer {
                let loc = SourceLocation::new(
                    file_path,
                    pointer_line,
                    1,
                    child.end_position().row + 1,
                    child.end_position().column + 1,
                );
                let snippet = snippet_at_line(source_str, pointer_line, 1);
                findings.push(make_finding("NULL-003", loc, snippet));
            }

            prev_was_pointer = is_pointer && !is_count;
            if is_pointer {
                pointer_line = child.start_position().row + 1;
            }
        }
    }
}

// =============================================================================
// MemSafe Checker
// =============================================================================

pub(super) fn check_mem_safe(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    if is_cpp {
        // MEM-001: Raw new
        check_new_delete(tree, source, file_path, source_str, lang_name, "MEM-001", NEW_EXPR_QUERY, findings)?;

        // MEM-002: Raw delete
        check_new_delete(tree, source, file_path, source_str, lang_name, "MEM-002", DELETE_EXPR_QUERY, findings)?;

        // MEM-003: = delete without reason
        check_delete_reason(source_str, file_path, findings);

        // MEM-005: std::string field
        check_std_type_field(source_str, file_path, "std::string", "MEM-005", findings);

        // MEM-006: std::shared_ptr
        for m in find_pattern(source_str, "std::shared_ptr") {
            findings.push(make_finding_from_text("MEM-006", file_path, &m));
        }
        for m in find_pattern(source_str, "shared_ptr<") {
            if !m.snippet.contains("std::shared_ptr") && !m.snippet.contains("make_shared") {
                findings.push(make_finding_from_text("MEM-006", file_path, &m));
            }
        }
    }

    // MEM-004: Missing static_assert on aligned struct
    if is_cpp {
        check_missing_sizeof_assert(source_str, file_path, findings);
    }

    // MEM-008: Raw multiplication before allocation
    check_alloc_multiply(tree, source, file_path, source_str, lang_name, findings)?;

    Ok(())
}

/// MEM-001 / MEM-002: Detect new/delete expressions via tree-sitter query.
fn check_new_delete(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    rule_id: &str,
    query_str: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, query_str) {
        Ok(q) => q,
        Err(_) => return Ok(()),
    };

    let expr_idx = query.capture_index_for_name("expr").unwrap_or(0);
    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        if let Some(cap) = m.captures.iter().find(|c| c.index == expr_idx) {
            let text = node_text(cap.node, source);
            // Skip placement new
            if rule_id == "MEM-001" && text.contains("placement") {
                continue;
            }
            let loc = location_from_node(cap.node, file_path);
            let snippet = snippet_at_line(source_str, loc.line, 0);
            let mut finding = make_finding(rule_id, loc, snippet);
            finding.metadata.insert("expression".to_string(), text.to_string());
            findings.push(finding);
        }
    }

    Ok(())
}

/// MEM-003: `= delete` without C++26 reason string.
fn check_delete_reason(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    for m in find_pattern(source_str, "= delete;") {
        if !m.snippet.contains("= delete(") {
            findings.push(make_finding_from_text("MEM-003", file_path, &m));
        }
    }
}

/// MEM-004: struct with alignas but no static_assert(sizeof).
fn check_missing_sizeof_assert(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let mut in_aligned_struct = false;
    let mut aligned_struct_line = 0usize;
    let mut brace_depth = 0i32;
    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        if trimmed.contains("alignas(") && (trimmed.contains("struct") || trimmed.contains("class")) {
            in_aligned_struct = true;
            aligned_struct_line = line_idx + 1;
            brace_depth = 0;
        }

        if in_aligned_struct {
            brace_depth += line.matches('{').count() as i32;
            brace_depth -= line.matches('}').count() as i32;

            if brace_depth <= 0 && line.contains('}') {
                let remaining_lines: Vec<&str> = source_str.lines()
                    .skip(line_idx + 1)
                    .take(5)
                    .collect();
                let nearby = remaining_lines.join("\n");
                if !nearby.contains("static_assert(sizeof") && !nearby.contains("static_assert (sizeof") {
                    let loc = SourceLocation::new(
                        file_path,
                        aligned_struct_line,
                        1,
                        line_idx + 1,
                        1,
                    );
                    let snippet = snippet_at_line(source_str, aligned_struct_line, 0);
                    findings.push(make_finding("MEM-004", loc, snippet));
                }
                in_aligned_struct = false;
            }
        }
    }
}

/// Check for std:: type usage in struct fields (for MEM-005, PERF-001, etc.).
pub(super) fn check_std_type_field(
    source_str: &str,
    file_path: &str,
    type_name: &str,
    rule_id: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let mut in_struct = false;
    let mut brace_depth = 0i32;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        if (trimmed.starts_with("struct ") || trimmed.starts_with("class "))
            && trimmed.contains('{')
        {
            in_struct = true;
            brace_depth = 0;
        }

        if in_struct {
            brace_depth += trimmed.matches('{').count() as i32;
            brace_depth -= trimmed.matches('}').count() as i32;

            if brace_depth <= 0 {
                in_struct = false;
                continue;
            }

            if trimmed.contains(type_name) && !trimmed.starts_with("//") && !trimmed.starts_with("/*") {
                if trimmed.contains('(') && !trimmed.contains("std::function") {
                    continue;
                }
                let col = trimmed.find(type_name).unwrap_or(0);
                let loc = SourceLocation::new(
                    file_path,
                    line_idx + 1,
                    col + 1,
                    line_idx + 1,
                    col + type_name.len() + 1,
                );
                findings.push(make_finding(rule_id, loc, trimmed.to_string()));
            }
        }
    }
}

/// MEM-008: Raw multiplication in allocation size arguments.
fn check_alloc_multiply(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    let alloc_arith_query = r#"
(call_expression
  function: (identifier) @func
  (#any-of? @func "malloc" "calloc" "realloc" "aligned_alloc")
  arguments: (argument_list
    (binary_expression
      operator: [("+") ("*")]
      ) @arith)) @call
"#;

    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, alloc_arith_query) {
        Ok(q) => q,
        Err(_) => return Ok(()),
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

            let loc = location_from_node(call_cap.node, file_path);
            let snippet = snippet_at_line(source_str, loc.line, 0);
            let mut finding = make_finding("MEM-008", loc, snippet);
            finding.metadata.insert("function".to_string(), func_name.to_string());
            finding.metadata.insert("expression".to_string(), arith_text.to_string());
            findings.push(finding);
        }
    }

    Ok(())
}

// =============================================================================
// RaceFree Checker
// =============================================================================

pub(super) fn check_race_free(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    // RACE-001: mutable fields without atomic/mutex
    check_mutable_fields(source_str, file_path, findings);

    // RACE-002: .detach() on threads
    for m in find_pattern(source_str, ".detach()") {
        findings.push(make_finding_from_text("RACE-002", file_path, &m));
    }

    // RACE-003: std::mutex without lock_guard usage nearby
    check_mutex_without_lock(source_str, file_path, findings);
}

/// RACE-001: `mutable` fields that aren't std::mutex or std::atomic.
fn check_mutable_fields(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let mut in_struct = false;
    let mut brace_depth = 0i32;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        if (trimmed.starts_with("struct ") || trimmed.starts_with("class "))
            && trimmed.contains('{')
        {
            in_struct = true;
            brace_depth = 0;
        }

        if in_struct {
            brace_depth += trimmed.matches('{').count() as i32;
            brace_depth -= trimmed.matches('}').count() as i32;

            if brace_depth <= 0 {
                in_struct = false;
                continue;
            }

            if trimmed.starts_with("mutable ") || trimmed.contains(" mutable ") {
                if trimmed.contains("mutex")
                    || trimmed.contains("atomic")
                    || trimmed.contains("lock")
                    || trimmed.contains("condition_variable")
                {
                    continue;
                }
                let loc = SourceLocation::new(file_path, line_idx + 1, 1, line_idx + 1, trimmed.len());
                findings.push(make_finding("RACE-001", loc, trimmed.to_string()));
            }
        }
    }
}

/// RACE-003: Class has std::mutex member but methods don't use lock_guard/unique_lock.
fn check_mutex_without_lock(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let has_mutex = source_str.contains("std::mutex") || source_str.contains("std::shared_mutex");
    if !has_mutex {
        return;
    }

    let has_lock = source_str.contains("lock_guard")
        || source_str.contains("unique_lock")
        || source_str.contains("shared_lock")
        || source_str.contains("scoped_lock");

    if !has_lock {
        for m in find_pattern(source_str, "std::mutex") {
            findings.push(make_finding_from_text("RACE-003", file_path, &m));
        }
        for m in find_pattern(source_str, "std::shared_mutex") {
            findings.push(make_finding_from_text("RACE-003", file_path, &m));
        }
    }
}

// =============================================================================
// LeakFree Checker
// =============================================================================

pub(super) fn check_leak_free(
    _tree: &Tree,
    _source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    // LEAK-001: fopen without RAII wrapper
    check_fopen_leak(source_str, file_path, findings);

    // LEAK-002: Missing virtual destructor in class with virtual methods
    if is_cpp {
        check_missing_virtual_dtor(source_str, file_path, findings);
    }

    // LEAK-003: Socket/handle patterns without RAII
    check_handle_leak(source_str, file_path, findings);

    Ok(())
}

/// LEAK-001: fopen/open calls in C++ code (should use RAII fstream).
fn check_fopen_leak(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    for m in find_pattern(source_str, "fopen(") {
        findings.push(make_finding_from_text("LEAK-001", file_path, &m));
    }
    for m in find_pattern(source_str, "fopen_s(") {
        findings.push(make_finding_from_text("LEAK-001", file_path, &m));
    }
}

/// LEAK-002: Class with virtual methods but non-virtual destructor.
fn check_missing_virtual_dtor(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let mut in_class = false;
    let mut class_start_line = 0usize;
    let mut class_name = String::new();
    let mut brace_depth = 0i32;
    let mut has_virtual_method = false;
    let mut has_virtual_dtor = false;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        if !in_class {
            let is_class_def = (trimmed.starts_with("class ") || trimmed.starts_with("struct "))
                && (trimmed.contains('{') || !trimmed.contains(';'));

            if is_class_def {
                in_class = true;
                class_start_line = line_idx + 1;
                brace_depth = 0;
                has_virtual_method = false;
                has_virtual_dtor = false;

                let parts: Vec<&str> = trimmed.split_whitespace().collect();
                class_name = parts.get(1).unwrap_or(&"").trim_end_matches(':').to_string();
                class_name = class_name.trim_end_matches('{').trim().to_string();
            }
        }

        if in_class {
            brace_depth += trimmed.matches('{').count() as i32;
            brace_depth -= trimmed.matches('}').count() as i32;

            if trimmed.contains("virtual ") && !trimmed.contains('~') {
                has_virtual_method = true;
            }

            if trimmed.contains("virtual") && trimmed.contains('~') {
                has_virtual_dtor = true;
            }

            if brace_depth <= 0 && trimmed.contains('}') {
                if has_virtual_method && !has_virtual_dtor && !class_name.is_empty() {
                    let loc = SourceLocation::new(
                        file_path,
                        class_start_line,
                        1,
                        line_idx + 1,
                        1,
                    );
                    let snippet = snippet_at_line(source_str, class_start_line, 0);
                    let mut finding = make_finding("LEAK-002", loc, snippet);
                    finding.metadata.insert("class".to_string(), class_name.clone());
                    findings.push(finding);
                }
                in_class = false;
            }
        }
    }
}

/// LEAK-003: socket/handle patterns without RAII.
fn check_handle_leak(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let handle_funcs = ["socket(", "accept(", "open(", "creat(", "dup(", "pipe("];
    for func in &handle_funcs {
        for m in find_pattern(source_str, func) {
            if m.snippet.contains('.') && m.snippet.find('.').unwrap_or(usize::MAX) < m.snippet.find(func).unwrap_or(0) {
                continue;
            }
            if m.snippet.contains("unique_fd")
                || m.snippet.contains("ScopedFd")
                || m.snippet.contains("FileDescriptor")
            {
                continue;
            }
            if *func == "open(" || *func == "socket(" || *func == "accept(" {
                findings.push(make_finding_from_text("LEAK-003", file_path, &m));
            }
        }
    }
}

// =============================================================================
// DetDrop Checker
// =============================================================================

pub(super) fn check_det_drop(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    check_global_statics(source_str, file_path, findings);
}

/// DETD-001: Static/global objects with non-trivial destructors.
fn check_global_statics(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let nontrivial_types = [
        "std::string", "std::vector", "std::map", "std::unordered_map",
        "std::set", "std::unordered_set", "std::list", "std::deque",
        "std::shared_ptr", "std::unique_ptr",
    ];

    let mut brace_depth = 0i32;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }

        brace_depth += trimmed.matches('{').count() as i32;
        brace_depth -= trimmed.matches('}').count() as i32;

        if brace_depth > 1 {
            continue;
        }

        let is_static = trimmed.starts_with("static ") || trimmed.starts_with("thread_local ");
        let is_global = brace_depth == 0 && !trimmed.starts_with("static ")
            && !trimmed.starts_with('#')
            && !trimmed.starts_with("//")
            && !trimmed.starts_with("namespace")
            && !trimmed.starts_with("class")
            && !trimmed.starts_with("struct")
            && !trimmed.starts_with("enum")
            && !trimmed.starts_with("typedef")
            && !trimmed.starts_with("using")
            && !trimmed.starts_with("template")
            && !trimmed.starts_with("extern")
            && !trimmed.starts_with("inline")
            && !trimmed.starts_with("constexpr")
            && !trimmed.starts_with("void")
            && !trimmed.starts_with("int ")
            && !trimmed.starts_with("auto ")
            && !trimmed.starts_with('{')
            && !trimmed.starts_with('}')
            && !trimmed.is_empty();

        if is_static || is_global {
            for nt in &nontrivial_types {
                if trimmed.contains(nt) {
                    let loc = SourceLocation::new(file_path, line_idx + 1, 1, line_idx + 1, trimmed.len());
                    let mut finding = make_finding("DETD-001", loc, trimmed.to_string());
                    finding.metadata.insert("type".to_string(), (*nt).to_string());
                    findings.push(finding);
                    break;
                }
            }
        }
    }
}

// =============================================================================
// Performance Checker
// =============================================================================

pub(super) fn check_performance(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    // PERF-001: std::unordered_map fields
    check_std_type_field(source_str, file_path, "std::unordered_map", "PERF-001", findings);

    // PERF-002: std::atomic without alignas(64)
    check_atomic_alignment(source_str, file_path, findings);

    // PERF-005: std::function fields
    check_std_type_field(source_str, file_path, "std::function", "PERF-005", findings);
}

/// PERF-002: std::atomic field without alignas for false sharing prevention.
fn check_atomic_alignment(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let mut in_struct = false;
    let mut brace_depth = 0i32;
    let mut struct_has_alignas = false;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        if (trimmed.starts_with("struct ") || trimmed.starts_with("class "))
            && trimmed.contains('{')
        {
            in_struct = true;
            brace_depth = 0;
            struct_has_alignas = trimmed.contains("alignas(");
        }

        if in_struct {
            brace_depth += trimmed.matches('{').count() as i32;
            brace_depth -= trimmed.matches('}').count() as i32;

            if brace_depth <= 0 {
                in_struct = false;
                continue;
            }

            if trimmed.contains("std::atomic") || trimmed.contains("atomic<") {
                if !trimmed.contains("alignas(") && !struct_has_alignas {
                    let loc = SourceLocation::new(
                        file_path,
                        line_idx + 1,
                        1,
                        line_idx + 1,
                        trimmed.len(),
                    );
                    findings.push(make_finding("PERF-002", loc, trimmed.to_string()));
                }
            }
        }
    }
}

// =============================================================================
// AntiPattern Checker
// =============================================================================

pub(super) fn check_anti_patterns(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    if !is_cpp {
        return Ok(());
    }

    // ANTI-001: RTTI usage (dynamic_cast, typeid)
    for m in find_pattern(source_str, "dynamic_cast<") {
        findings.push(make_finding_from_text("ANTI-001", file_path, &m));
    }
    for m in find_pattern(source_str, "typeid(") {
        findings.push(make_finding_from_text("ANTI-001", file_path, &m));
    }

    // ANTI-002: std::variant fields
    check_std_type_field(source_str, file_path, "std::variant", "ANTI-002", findings);

    // ANTI-003: throw statements
    check_throw_statements(tree, source, file_path, source_str, lang_name, findings)?;

    Ok(())
}

/// ANTI-003: Detect throw statements via tree-sitter.
fn check_throw_statements(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, THROW_QUERY) {
        Ok(q) => q,
        Err(_) => {
            // Fallback to text search if grammar doesn't have throw_statement
            for m in find_pattern(source_str, "throw ") {
                if m.snippet.trim() == "throw;" {
                    continue;
                }
                findings.push(make_finding_from_text("ANTI-003", file_path, &m));
            }
            return Ok(());
        }
    };

    let expr_idx = query.capture_index_for_name("expr").unwrap_or(0);
    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        if let Some(cap) = m.captures.iter().find(|c| c.index == expr_idx) {
            let loc = location_from_node(cap.node, file_path);
            let snippet = snippet_at_line(source_str, loc.line, 0);
            findings.push(make_finding("ANTI-003", loc, snippet));
        }
    }

    Ok(())
}
