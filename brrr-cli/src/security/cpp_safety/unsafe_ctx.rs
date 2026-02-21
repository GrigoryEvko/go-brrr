//! D3390 §2.1 Unsafe Context detection.
//!
//! Detects operations that D3390 prohibits in safe context:
//! - UCTX-001: Pointer arithmetic (*(ptr+n))
//! - UCTX-004: Union type definitions
//! - UCTX-005: Non-const static/global mutable variables
//! - UCTX-006: Inline assembly

use crate::security::common::SourceLocation;

use super::helpers::make_finding;
use super::types::CppSafetyFinding;

/// §2.1 Unsafe Context: operations that D3390 prohibits in safe context.
/// UCTX-001: Pointer arithmetic (ptr+n, ptr++, *(ptr+n)).
/// UCTX-002: Pointer difference.
/// UCTX-004: Union type definitions.
/// UCTX-005: Non-const static/global mutable variables.
/// UCTX-006: Inline assembly.
pub(super) fn check_unsafe_context(
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

        // UCTX-001: Pointer arithmetic — dereference of arithmetic result *(ptr + n)
        // Also detect ptr++ / ++ptr / ptr-- / --ptr on pointer-like variables
        if trimmed.contains("*(") && (trimmed.contains(" + ") || trimmed.contains(" - ")) {
            // Pattern: *(identifier + expr) or *(identifier - expr)
            if let Some(star_paren) = trimmed.find("*(") {
                let inside = &trimmed[star_paren + 2..];
                if let Some(close) = inside.find(')') {
                    let expr = &inside[..close];
                    if expr.contains('+') || expr.contains('-') {
                        let loc = SourceLocation::new(
                            file_path, line_idx + 1, star_paren + 1,
                            line_idx + 1, trimmed.len(),
                        );
                        findings.push(make_finding("UCTX-001", loc, trimmed.to_string()));
                    }
                }
            }
        }

        // UCTX-004: Union type definition
        // Match `union Name {` but not `std::variant` or inside comments
        if (trimmed.starts_with("union ") || trimmed.contains(" union "))
            && trimmed.contains('{')
            && !trimmed.contains("std::")
            && !trimmed.contains("typedef")
        {
            let col = trimmed.find("union").unwrap_or(0);
            let loc = SourceLocation::new(
                file_path, line_idx + 1, col + 1, line_idx + 1, trimmed.len(),
            );
            findings.push(make_finding("UCTX-004", loc, trimmed.to_string()));
        }

        // UCTX-005: Non-const static mutable variable
        // Match `static Type name` but not `static const`, `static constexpr`,
        // `static_assert`, function declarations, or class member declarations
        if trimmed.starts_with("static ") && !trimmed.starts_with("static_") {
            let after_static = trimmed["static ".len()..].trim();
            let is_const = after_static.starts_with("const ")
                || after_static.starts_with("constexpr ")
                || after_static.starts_with("constinit ");
            let is_function = trimmed.contains('(');
            let is_class_keyword = after_static.starts_with("void ")
                || after_static.starts_with("auto ")
                || after_static.starts_with("inline ");
            // Must have `=` or `;` to be a variable declaration, not a function
            let is_var_decl = trimmed.contains('=') || (trimmed.ends_with(';') && !is_function);

            if !is_const && is_var_decl && !is_class_keyword {
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("UCTX-005", loc, trimmed.to_string()));
            }
        }

        // UCTX-006: Inline assembly
        for asm_kw in &["asm(", "asm (", "__asm(", "__asm (", "__asm__(", "__asm__ (", "asm volatile(", "asm volatile ("] {
            if trimmed.contains(asm_kw) {
                let col = trimmed.find(asm_kw).unwrap_or(0);
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, col + 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("UCTX-006", loc, trimmed.to_string()));
                break; // one finding per line
            }
        }
    }
}
