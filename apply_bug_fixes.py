#!/usr/bin/env python3
"""Apply BUG #13 and BUG #14 fixes to rust_lang.rs"""

import re

# Read the file
with open('src/lang/rust_lang.rs', 'r') as f:
    content = f.read()

# BUG #13 fix: Add extract_distinct_type_params after extract_type_params
bug13_fix = '''
    /// Extract lifetime and type parameters separately (BUG #13 fix).
    ///
    /// Distinguishes lifetime parameters ('a, 'b) from type parameters (T, U).
    /// This is critical for accurate generic analysis in Rust code.
    ///
    /// # Returns
    /// A tuple of (lifetime_params, type_params) where each is a Vec of param strings.
    #[allow(dead_code)] // Available for future use in enhanced generic analysis
    fn extract_distinct_type_params(
        &self,
        node: Node,
        source: &[u8],
    ) -> (Vec<String>, Vec<String>) {
        let mut lifetimes = Vec::new();
        let mut type_params = Vec::new();

        for child in node.children(&mut node.walk()) {
            if child.kind() == "type_parameters" {
                for param in child.children(&mut child.walk()) {
                    match param.kind() {
                        // Lifetime parameters: 'a, 'b, 'static
                        "lifetime" => {
                            let lifetime = self.node_text(param, source).to_string();
                            lifetimes.push(lifetime);
                        }
                        // Type parameters: T, U, N (including const generics)
                        "type_identifier" => {
                            let type_param = self.node_text(param, source).to_string();
                            type_params.push(type_param);
                        }
                        // Constrained type parameter: T: Clone + Send or 'a: 'b
                        "constrained_type_parameter" => {
                            let text = self.node_text(param, source);
                            // Check if it starts with a lifetime
                            if text.starts_with('\\\'') {
                                lifetimes.push(text.to_string());
                            } else {
                                type_params.push(text.to_string());
                            }
                        }
                        // Const generic: const N: usize
                        "const_parameter" => {
                            let const_param = self.node_text(param, source).to_string();
                            type_params.push(const_param);
                        }
                        _ => {}
                    }
                }
            }
        }

        (lifetimes, type_params)
    }

    /// Extract where clause.'''

# Check if BUG #13 is already applied
if 'extract_distinct_type_params' not in content:
    # Find the pattern to replace
    pattern = r'(        None\n    \}\n\n    /// Extract where clause\.)'
    replacement = r'''        None
    }
''' + bug13_fix[1:]  # Remove leading newline

    content = re.sub(pattern, replacement, content, count=1)
    print("Applied BUG #13 fix: extract_distinct_type_params")
else:
    print("BUG #13 already applied")

# BUG #14 fix: Add if_let_expression and while_let_expression handling in process_dfg_node
bug14_pattern_bindings = '''
    /// Extract pattern bindings from if-let or while-let expressions (BUG #14 fix).
    ///
    /// Handles patterns like:
    /// - `Some(x)` - extracts `x`
    /// - `(a, b)` - extracts `a` and `b`
    /// - `Struct { field: x, .. }` - extracts `x`
    fn extract_pattern_bindings_from_node(
        &self,
        node: Node,
        source: &[u8],
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut HashMap<String, Vec<usize>>,
        line: usize,
    ) {
        // Find pattern node in children
        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "tuple_struct_pattern" | "tuple_pattern" | "struct_pattern" => {
                    self.extract_identifiers_from_pattern(child, source, edges, definitions, line);
                }
                "identifier" => {
                    // Check if this is the pattern identifier (after "let" keyword)
                    let prev = child.prev_sibling();
                    if prev.map(|p| p.kind()) == Some("let") {
                        let var_name = self.node_text(child, source).to_string();
                        if !var_name.is_empty() {
                            definitions.entry(var_name.clone()).or_default().push(line);
                            edges.push(DataflowEdge {
                                variable: var_name,
                                from_line: line,
                                to_line: line,
                                kind: DataflowKind::Definition,
                            });
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Recursively extract identifier bindings from a pattern.
    fn extract_identifiers_from_pattern(
        &self,
        pattern: Node,
        source: &[u8],
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut HashMap<String, Vec<usize>>,
        line: usize,
    ) {
        for child in pattern.children(&mut pattern.walk()) {
            match child.kind() {
                "identifier" => {
                    let var_name = self.node_text(child, source).to_string();
                    // Skip variant names (e.g., "Some" in Some(x))
                    // They typically start with uppercase
                    if !var_name.is_empty() && !var_name.chars().next().unwrap().is_uppercase() {
                        definitions.entry(var_name.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: var_name,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Definition,
                        });
                    }
                }
                "tuple_struct_pattern" | "tuple_pattern" | "struct_pattern" => {
                    // Recurse into nested patterns
                    self.extract_identifiers_from_pattern(child, source, edges, definitions, line);
                }
                _ => {}
            }
        }
    }

    /// Extract variable uses from an expression.'''

bug14_match_cases = '''            }
            // BUG #14 fix: Handle if_let_expression pattern bindings
            // `if let Some(x) = opt { }` creates a definition of `x`
            "if_let_expression" => {
                let line = node.start_position().row + 1;

                // Extract pattern bindings from the if-let pattern
                self.extract_pattern_bindings_from_node(node, source, edges, definitions, line);

                // Process children (value expression and body block) for uses
                for child in node.children(&mut node.walk()) {
                    self.process_dfg_node(child, source, edges, definitions, uses);
                }
            }
            // BUG #14 fix: Handle while_let_expression pattern bindings
            // `while let Some(x) = iter.next() { }` creates a definition of `x`
            "while_let_expression" => {
                let line = node.start_position().row + 1;

                // Extract pattern bindings from the while-let pattern
                self.extract_pattern_bindings_from_node(node, source, edges, definitions, line);

                // Process children for uses
                for child in node.children(&mut node.walk()) {
                    self.process_dfg_node(child, source, edges, definitions, uses);
                }
            }
            _ => {'''

# Check if BUG #14 is already applied
if 'if_let_expression' not in content or 'extract_pattern_bindings_from_node' not in content:
    # Add the match cases before the _ => branch
    old_default = '''            }
            _ => {
                // Recurse into children
                for child in node.children(&mut node.walk()) {
                    self.process_dfg_node(child, source, edges, definitions, uses);
                }
            }
        }
    }

    /// Extract variable uses from an expression.'''

    new_default = bug14_match_cases + '''
                // Recurse into children
                for child in node.children(&mut node.walk()) {
                    self.process_dfg_node(child, source, edges, definitions, uses);
                }
            }
        }
    }
''' + bug14_pattern_bindings

    if old_default in content:
        content = content.replace(old_default, new_default)
        print("Applied BUG #14 fix: if_let_expression and while_let_expression handling")
    else:
        print("Could not find exact pattern for BUG #14, trying alternative...")
        # Try a different approach - find the _ => line
        lines = content.split('\n')
        new_lines = []
        in_process_dfg_node = False
        added_bug14 = False

        for i, line in enumerate(lines):
            if 'fn process_dfg_node(' in line:
                in_process_dfg_node = True

            if in_process_dfg_node and not added_bug14:
                # Look for the _ => pattern in the match
                if '            _ => {' in line and i > 0 and '}' in lines[i-1]:
                    # Insert the if_let and while_let cases before _ =>
                    new_lines.append('            }')
                    new_lines.append('            // BUG #14 fix: Handle if_let_expression pattern bindings')
                    new_lines.append('            // `if let Some(x) = opt { }` creates a definition of `x`')
                    new_lines.append('            "if_let_expression" => {')
                    new_lines.append('                let line = node.start_position().row + 1;')
                    new_lines.append('')
                    new_lines.append('                // Extract pattern bindings from the if-let pattern')
                    new_lines.append('                self.extract_pattern_bindings_from_node(node, source, edges, definitions, line);')
                    new_lines.append('')
                    new_lines.append('                // Process children (value expression and body block) for uses')
                    new_lines.append('                for child in node.children(&mut node.walk()) {')
                    new_lines.append('                    self.process_dfg_node(child, source, edges, definitions, uses);')
                    new_lines.append('                }')
                    new_lines.append('            }')
                    new_lines.append('            // BUG #14 fix: Handle while_let_expression pattern bindings')
                    new_lines.append('            // `while let Some(x) = iter.next() { }` creates a definition of `x`')
                    new_lines.append('            "while_let_expression" => {')
                    new_lines.append('                let line = node.start_position().row + 1;')
                    new_lines.append('')
                    new_lines.append('                // Extract pattern bindings from the while-let pattern')
                    new_lines.append('                self.extract_pattern_bindings_from_node(node, source, edges, definitions, line);')
                    new_lines.append('')
                    new_lines.append('                // Process children for uses')
                    new_lines.append('                for child in node.children(&mut node.walk()) {')
                    new_lines.append('                    self.process_dfg_node(child, source, edges, definitions, uses);')
                    new_lines.append('                }')
                    # Don't add the closing brace here, continue with _ => {
                    new_lines.append(line)
                    added_bug14 = True
                    continue

            new_lines.append(line)

        if added_bug14:
            content = '\n'.join(new_lines)
            print("Applied BUG #14 (alternative method)")
else:
    print("BUG #14 already applied")

# Now add the helper functions if not present
if 'extract_pattern_bindings_from_node' not in content:
    # Find where to insert - before extract_uses_from_expr
    pattern = r'(\n    /// Extract variable uses from an expression\.)'
    helper_funcs = '''
    /// Extract pattern bindings from if-let or while-let expressions (BUG #14 fix).
    ///
    /// Handles patterns like:
    /// - `Some(x)` - extracts `x`
    /// - `(a, b)` - extracts `a` and `b`
    /// - `Struct { field: x, .. }` - extracts `x`
    fn extract_pattern_bindings_from_node(
        &self,
        node: Node,
        source: &[u8],
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut HashMap<String, Vec<usize>>,
        line: usize,
    ) {
        // Find pattern node in children
        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "tuple_struct_pattern" | "tuple_pattern" | "struct_pattern" => {
                    self.extract_identifiers_from_pattern(child, source, edges, definitions, line);
                }
                "identifier" => {
                    // Check if this is the pattern identifier (after "let" keyword)
                    let prev = child.prev_sibling();
                    if prev.map(|p| p.kind()) == Some("let") {
                        let var_name = self.node_text(child, source).to_string();
                        if !var_name.is_empty() {
                            definitions.entry(var_name.clone()).or_default().push(line);
                            edges.push(DataflowEdge {
                                variable: var_name,
                                from_line: line,
                                to_line: line,
                                kind: DataflowKind::Definition,
                            });
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Recursively extract identifier bindings from a pattern.
    fn extract_identifiers_from_pattern(
        &self,
        pattern: Node,
        source: &[u8],
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut HashMap<String, Vec<usize>>,
        line: usize,
    ) {
        for child in pattern.children(&mut pattern.walk()) {
            match child.kind() {
                "identifier" => {
                    let var_name = self.node_text(child, source).to_string();
                    // Skip variant names (e.g., "Some" in Some(x))
                    // They typically start with uppercase
                    if !var_name.is_empty() && !var_name.chars().next().unwrap().is_uppercase() {
                        definitions.entry(var_name.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: var_name,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Definition,
                        });
                    }
                }
                "tuple_struct_pattern" | "tuple_pattern" | "struct_pattern" => {
                    // Recurse into nested patterns
                    self.extract_identifiers_from_pattern(child, source, edges, definitions, line);
                }
                _ => {}
            }
        }
    }

    /// Extract variable uses from an expression.'''

    content = re.sub(pattern, helper_funcs, content, count=1)
    print("Added helper functions for BUG #14")

# Write the file
with open('src/lang/rust_lang.rs', 'w') as f:
    f.write(content)

print("Done!")
