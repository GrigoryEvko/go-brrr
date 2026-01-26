//! CFG rendering utilities.
//!
//! Provides multiple output formats for control flow graphs:
//! - Mermaid: Interactive flowcharts for documentation
//! - DOT (Graphviz): Publication-quality graphs
//! - ASCII: Terminal-friendly text representation
//! - JSON: Machine-readable via serde

use crate::cfg::types::{BlockId, CFGInfo};

/// Escape special characters for Mermaid labels.
///
/// Mermaid uses quotes for node labels and has many special characters
/// that can break rendering or be misinterpreted. We handle:
///
/// - `\` -> `\\` (must be first to avoid double escaping)
/// - `"` -> `'` (Mermaid doesn't support backslash escaping in quotes)
/// - `\n` -> ` ` (newlines break label parsing)
/// - `\r` -> removed (carriage returns break parsing)
/// - `|` -> `\|` (vertical bar used for edge labels in Mermaid)
/// - `<` -> `&lt;` (HTML entity to prevent tag interpretation)
/// - `>` -> `&gt;` (HTML entity to prevent tag interpretation)
/// - `{` -> `#123;` (Mermaid shape syntax - use HTML entity)
/// - `}` -> `#125;` (Mermaid shape syntax - use HTML entity)
/// - `[` -> `#91;` (Mermaid shape syntax - use HTML entity)
/// - `]` -> `#93;` (Mermaid shape syntax - use HTML entity)
/// - `` ` `` -> `'` (backticks can break parsing)
/// - `;` -> `,` (statement separator)
/// - `#` -> `#35;` (use HTML entity to prevent interpretation)
/// - `&` -> `&amp;` (HTML entity prefix - must escape to prevent confusion)
fn escape_mermaid_label(s: &str) -> String {
    // Process & first since we're adding HTML entities that contain &
    // But we need to be careful not to double-escape
    let mut result = String::with_capacity(s.len() * 2);

    for c in s.chars() {
        match c {
            '\\' => result.push_str("\\\\"),
            '"' => result.push('\''),
            '\n' => result.push(' '),
            '\r' => {}
            '|' => result.push_str("\\|"),
            '&' => result.push_str("&amp;"),
            '<' => result.push_str("&lt;"),
            '>' => result.push_str("&gt;"),
            '{' => result.push_str("#123;"),
            '}' => result.push_str("#125;"),
            '[' => result.push_str("#91;"),
            ']' => result.push_str("#93;"),
            '`' => result.push('\''),
            ';' => result.push(','),
            '#' => result.push_str("#35;"),
            _ => result.push(c),
        }
    }

    result
}

/// Escape special characters for DOT labels.
///
/// DOT uses backslash escaping for special characters:
/// - `\` -> `\\` (must be first to avoid double escaping)
/// - `"` -> `\"` (quotes delimit labels)
/// - `\n` -> `\\n` (literal string for label line breaks)
/// - `\r` -> removed (carriage returns break parsing)
/// - `<` -> `\\<` (HTML-like label delimiter)
/// - `>` -> `\\>` (HTML-like label delimiter)
/// - `{` -> `\\{` (record shape syntax)
/// - `}` -> `\\}` (record shape syntax)
/// - `|` -> `\\|` (record field separator)
fn escape_dot_label(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "")
        .replace('<', "\\<")
        .replace('>', "\\>")
        .replace('{', "\\{")
        .replace('}', "\\}")
        .replace('|', "\\|")
}

/// Escape special characters for DOT HTML-like labels.
///
/// When using HTML-like labels (delimited by `<` `>` instead of quotes),
/// standard HTML entities must be used for escaping.
///
/// # Example
/// ```ignore
/// let label = escape_dot_html_label("x < y && z > 0");
/// // Use in DOT: node [label=<{label}>];
/// ```
#[allow(dead_code)]
fn escape_dot_html_label(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// Sanitize a string for use as a DOT identifier.
///
/// DOT identifiers must be alphanumeric (with underscores).
/// Invalid characters are replaced with underscores.
fn sanitize_dot_id(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        if c.is_alphanumeric() || c == '_' {
            result.push(c);
        } else {
            result.push('_');
        }
    }
    // DOT identifiers cannot start with a digit
    if result.starts_with(|c: char| c.is_ascii_digit()) {
        result.insert(0, '_');
    }
    if result.is_empty() {
        result.push_str("_anonymous");
    }
    result
}

/// Get sorted block IDs for deterministic output.
fn sorted_block_ids(cfg: &CFGInfo) -> Vec<BlockId> {
    let mut ids: Vec<_> = cfg.blocks.keys().copied().collect();
    ids.sort_by_key(|id| id.0);
    ids
}

/// Get edges sorted by (from, to) for deterministic output.
///
/// Edge ordering in `CFGInfo::edges` depends on the order of AST traversal,
/// which may vary across runs or when the builder visits nodes differently.
/// Sorting ensures consistent output regardless of insertion order.
fn sorted_edges(cfg: &CFGInfo) -> Vec<&crate::cfg::types::CFGEdge> {
    let mut edges: Vec<_> = cfg.edges.iter().collect();
    edges.sort_by_key(|e| (e.from.0, e.to.0));
    edges
}

/// Render CFG to Mermaid flowchart format.
///
/// Mermaid is a JavaScript-based diagramming tool that renders
/// text definitions into diagrams. Output can be embedded in
/// Markdown files or rendered via mermaid.live.
///
/// # Format
/// ```text
/// flowchart TD
///     B0["entry"]
///     B1["if condition"]
///     B0 --> B1
///     B1 -->|true| B2
/// ```
///
/// # Example
/// ```ignore
/// let mermaid = to_mermaid(&cfg);
/// println!("{}", mermaid);
/// ```
pub fn to_mermaid(cfg: &CFGInfo) -> String {
    let mut out = String::from("flowchart TD\n");

    // Render blocks in sorted order for deterministic output
    for id in sorted_block_ids(cfg) {
        let block = &cfg.blocks[&id];
        let label = escape_mermaid_label(&block.label);
        out.push_str(&format!("    B{}[\"{}\"]\n", id.0, label));
    }

    // Render edges in sorted order for deterministic output
    for edge in sorted_edges(cfg) {
        let label = edge.label();
        let arrow = if label.is_empty() {
            "-->".to_string()
        } else {
            format!("-->|{}|", escape_mermaid_label(&label))
        };
        out.push_str(&format!("    B{} {} B{}\n", edge.from.0, arrow, edge.to.0));
    }

    out
}

/// Render CFG to DOT (Graphviz) format.
///
/// DOT is the graph description language used by Graphviz.
/// The output can be rendered using `dot`, `neato`, or other
/// Graphviz layout engines.
///
/// # Format
/// ```text
/// digraph func_name {
///     rankdir=TB;
///     node [shape=box];
///     B0 [label="entry"];
///     B0 -> B1;
///     B1 -> B2 [label="true"];
/// }
/// ```
///
/// # Rendering
/// ```bash
/// dot -Tpng cfg.dot -o cfg.png
/// dot -Tsvg cfg.dot -o cfg.svg
/// ```
pub fn to_dot(cfg: &CFGInfo) -> String {
    let graph_name = sanitize_dot_id(&cfg.function_name);
    let mut out = format!("digraph {} {{\n", graph_name);
    out.push_str("    rankdir=TB;\n");
    out.push_str("    node [shape=box, fontname=\"monospace\"];\n");

    // Mark entry and exit nodes with special styling
    out.push_str(&format!(
        "    B{} [style=filled, fillcolor=lightgreen];\n",
        cfg.entry.0
    ));
    for exit in &cfg.exits {
        out.push_str(&format!(
            "    B{} [style=filled, fillcolor=lightcoral];\n",
            exit.0
        ));
    }
    out.push('\n');

    // Render blocks in sorted order for deterministic output
    for id in sorted_block_ids(cfg) {
        let block = &cfg.blocks[&id];
        let label = escape_dot_label(&block.label);
        out.push_str(&format!("    B{} [label=\"{}\"];\n", id.0, label));
    }

    out.push('\n');

    // Render edges in sorted order for deterministic output
    for edge in sorted_edges(cfg) {
        let label = edge.label();
        let label_attr = if label.is_empty() {
            String::new()
        } else {
            format!(" [label=\"{}\"]", escape_dot_label(&label))
        };
        out.push_str(&format!(
            "    B{} -> B{}{};\n",
            edge.from.0, edge.to.0, label_attr
        ));
    }

    out.push_str("}\n");
    out
}

/// Render CFG as ASCII art (simple text representation).
///
/// Provides a terminal-friendly, human-readable view of the CFG
/// structure including block details and edge connections.
///
/// # Format
/// ```text
/// CFG: process_data
/// Blocks: 5
/// Edges: 6
/// Complexity: 3
///
/// [B0] entry (lines 10-12)
///     x = get_data()
///     validate(x)
///
/// Edges:
///     B0 -> B1
///     B1 -> B2 [true]
/// ```
#[allow(dead_code)]
pub fn to_ascii(cfg: &CFGInfo) -> String {
    let mut out = format!("CFG: {}\n", cfg.function_name);
    out.push_str(&"=".repeat(40));
    out.push('\n');
    out.push_str(&format!("Blocks: {}\n", cfg.blocks.len()));
    out.push_str(&format!("Edges: {}\n", cfg.edges.len()));
    out.push_str(&format!("Complexity: {}\n", cfg.cyclomatic_complexity()));
    out.push_str(&format!("Entry: B{}\n", cfg.entry.0));
    out.push_str(&format!(
        "Exits: {}\n",
        cfg.exits
            .iter()
            .map(|id| format!("B{}", id.0))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    out.push('\n');

    // Render blocks in sorted order
    for id in sorted_block_ids(cfg) {
        let block = &cfg.blocks[&id];
        out.push_str(&format!(
            "[B{}] {} (lines {}-{})\n",
            id.0, block.label, block.start_line, block.end_line
        ));
        for stmt in &block.statements {
            out.push_str(&format!("    {}\n", stmt));
        }
        if !block.statements.is_empty() {
            out.push('\n');
        }
    }

    out.push_str("\nEdges:\n");
    // Render edges in sorted order for deterministic output
    for edge in sorted_edges(cfg) {
        let label = edge.label();
        let label_str = if label.is_empty() {
            String::new()
        } else {
            format!(" [{}]", label)
        };
        out.push_str(&format!(
            "    B{} -> B{}{}\n",
            edge.from.0, edge.to.0, label_str
        ));
    }

    out
}

/// Render CFG to JSON format.
///
/// This is a convenience wrapper around serde serialization.
/// The output follows the structure defined by the CFGInfo type.
///
/// # Format
/// ```json
/// {
///   "function_name": "process_data",
///   "blocks": {...},
///   "edges": [...],
///   "entry": 0,
///   "exits": [4]
/// }
/// ```
#[allow(dead_code)]
pub fn to_json(cfg: &CFGInfo) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(cfg)
}

/// Render CFG to compact JSON (single line).
#[allow(dead_code)]
pub fn to_json_compact(cfg: &CFGInfo) -> Result<String, serde_json::Error> {
    serde_json::to_string(cfg)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::types::{BlockType, CFGBlock, CFGEdge, EdgeType};
    use rustc_hash::FxHashMap;

    fn sample_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();
        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["x = 1".to_string()],
                func_calls: Vec::new(),
                start_line: 1,
                end_line: 1,
            },
        );
        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "if x > 0".to_string(),
                block_type: BlockType::Branch,
                statements: vec![],
                func_calls: Vec::new(),
                start_line: 2,
                end_line: 2,
            },
        );
        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "exit".to_string(),
                block_type: BlockType::Exit,
                statements: vec!["return x".to_string()],
                func_calls: Vec::new(),
                start_line: 3,
                end_line: 3,
            },
        );

        CFGInfo {
            function_name: "test_func".to_string(),
            blocks,
            edges: vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::new(BlockId(1), BlockId(2), EdgeType::True),
            ],
            entry: BlockId(0),
            exits: vec![BlockId(2)],
            decision_points: 1, // One decision point for the if condition
            comprehension_decision_points: 0,
            nested_cfgs: FxHashMap::default(),
            is_async: false,
            await_points: 0,
            blocking_calls: Vec::new(),
            ..Default::default()
        }
    }

    #[test]
    fn test_mermaid_output() {
        let cfg = sample_cfg();
        let mermaid = to_mermaid(&cfg);

        assert!(mermaid.starts_with("flowchart TD"));
        assert!(mermaid.contains("B0[\"entry\"]"));
        // Note: > is escaped to &gt; in Mermaid labels
        assert!(mermaid.contains("B1[\"if x &gt; 0\"]"));
        assert!(mermaid.contains("B0 --> B1"));
        assert!(mermaid.contains("-->|true|"));
    }

    #[test]
    fn test_mermaid_escaping() {
        // Test basic escaping from original implementation
        let label = "test \"quoted\" label\nwith newline|and pipe";
        let escaped = escape_mermaid_label(label);
        assert!(!escaped.contains('"'));
        assert!(!escaped.contains('\n'));
        assert!(!escaped.contains('|') || escaped.contains("\\|"));
        assert!(escaped.contains("\\|")); // Pipe should be escaped

        // Test HTML angle brackets
        let html_label = "x < y && y > z";
        let escaped_html = escape_mermaid_label(html_label);
        assert!(escaped_html.contains("&lt;"));
        assert!(escaped_html.contains("&gt;"));
        assert!(escaped_html.contains("&amp;"));
        assert!(!escaped_html.contains(" < "));
        assert!(!escaped_html.contains(" > "));

        // Test Mermaid shape syntax characters
        let shape_label = "dict{key} and list[0]";
        let escaped_shape = escape_mermaid_label(shape_label);
        assert!(!escaped_shape.contains('{'));
        assert!(!escaped_shape.contains('}'));
        assert!(!escaped_shape.contains('['));
        assert!(!escaped_shape.contains(']'));
        assert!(escaped_shape.contains("#123;")); // {
        assert!(escaped_shape.contains("#125;")); // }
        assert!(escaped_shape.contains("#91;")); // [
        assert!(escaped_shape.contains("#93;")); // ]

        // Test backticks and semicolons
        let code_label = "func(`arg`); next";
        let escaped_code = escape_mermaid_label(code_label);
        assert!(!escaped_code.contains('`'));
        // Semicolons in source become commas (but HTML entities still have ;)
        assert!(escaped_code.contains(", next")); // ; became ,
        assert!(!escaped_code.contains("); ")); // Original semicolon pattern gone

        // Test hash/pound sign
        let hash_label = "comment # here";
        let escaped_hash = escape_mermaid_label(hash_label);
        assert!(!escaped_hash.contains(" # "));
        assert!(escaped_hash.contains("#35;"));

        // Test backslash escaping
        let backslash_label = "path\\to\\file";
        let escaped_backslash = escape_mermaid_label(backslash_label);
        assert!(escaped_backslash.contains("\\\\"));

        // Test carriage return removal
        let cr_label = "line1\r\nline2";
        let escaped_cr = escape_mermaid_label(cr_label);
        assert!(!escaped_cr.contains('\r'));
        assert!(!escaped_cr.contains('\n'));

        // Comprehensive test: all special chars in one string
        let all_special = "\"<>{}`[];#&|\\test\n\r";
        let escaped_all = escape_mermaid_label(all_special);
        // Verify none of the raw special chars remain (except escaped forms)
        assert!(!escaped_all.contains('"'));
        assert!(!escaped_all.contains('<'));
        assert!(!escaped_all.contains('>'));
        assert!(!escaped_all.contains('{'));
        assert!(!escaped_all.contains('}'));
        assert!(!escaped_all.contains('`'));
        assert!(!escaped_all.contains('['));
        assert!(!escaped_all.contains(']'));
        // Note: ; still appears in HTML entities like &lt; &gt; #123; etc.
        // Check the original semicolon was converted to comma
        assert!(escaped_all.contains(",#35;")); // ; became , followed by # escape
        assert!(!escaped_all.contains('\n'));
        assert!(!escaped_all.contains('\r'));
        // Verify HTML entities are present
        assert!(escaped_all.contains("&lt;"));
        assert!(escaped_all.contains("&gt;"));
        assert!(escaped_all.contains("&amp;"));
        // Verify pipe is escaped
        assert!(escaped_all.contains("\\|"));
        // Verify backslash is escaped
        assert!(escaped_all.contains("\\\\"));
    }

    #[test]
    fn test_dot_output() {
        let cfg = sample_cfg();
        let dot = to_dot(&cfg);

        assert!(dot.starts_with("digraph test_func"));
        assert!(dot.contains("rankdir=TB"));
        assert!(dot.contains("B0 [label=\"entry\"]"));
        assert!(dot.contains("B0 -> B1"));
        assert!(dot.contains("[label=\"true\"]"));
    }

    #[test]
    fn test_dot_escaping() {
        // Test basic escaping (original test)
        let label = "test \"quoted\"\nwith newline";
        let escaped = escape_dot_label(label);
        assert_eq!(escaped, "test \\\"quoted\\\"\\nwith newline");

        // Test HTML-like label delimiters
        let html_label = "x < y && y > z";
        let escaped_html = escape_dot_label(html_label);
        assert!(escaped_html.contains("\\<"));
        assert!(escaped_html.contains("\\>"));
        assert!(!escaped_html.contains(" < "));
        assert!(!escaped_html.contains(" > "));

        // Test record shape syntax
        let record_label = "dict{key} = value";
        let escaped_record = escape_dot_label(record_label);
        assert!(escaped_record.contains("\\{"));
        assert!(escaped_record.contains("\\}"));
        assert!(!escaped_record.contains("dict{"));

        // Test record field separator
        let pipe_label = "field1 | field2";
        let escaped_pipe = escape_dot_label(pipe_label);
        assert!(escaped_pipe.contains("\\|"));
        assert!(!escaped_pipe.contains(" | "));

        // Test backslash escaping (must be first to avoid double escaping)
        let backslash_label = "path\\to\\file";
        let escaped_backslash = escape_dot_label(backslash_label);
        assert_eq!(escaped_backslash, "path\\\\to\\\\file");

        // Test carriage return removal
        let cr_label = "line1\r\nline2";
        let escaped_cr = escape_dot_label(cr_label);
        assert!(!escaped_cr.contains('\r'));
        assert!(escaped_cr.contains("\\n"));

        // Comprehensive test: all special chars in one string
        let all_special = "\"<>{}`|\\test\n\r";
        let escaped_all = escape_dot_label(all_special);
        // Verify all special chars are escaped
        assert!(escaped_all.contains("\\\""));
        assert!(escaped_all.contains("\\<"));
        assert!(escaped_all.contains("\\>"));
        assert!(escaped_all.contains("\\{"));
        assert!(escaped_all.contains("\\}"));
        assert!(escaped_all.contains("\\|"));
        assert!(escaped_all.contains("\\\\"));
        assert!(escaped_all.contains("\\n"));
        assert!(!escaped_all.contains('\r'));
    }

    #[test]
    fn test_dot_html_label_escaping() {
        // Test HTML entity escaping for HTML-like labels
        let label = "x < y && z > 0";
        let escaped = escape_dot_html_label(label);
        assert!(escaped.contains("&lt;"));
        assert!(escaped.contains("&gt;"));
        assert!(escaped.contains("&amp;"));
        assert!(!escaped.contains(" < "));
        assert!(!escaped.contains(" > "));
        assert!(!escaped.contains(" && "));

        // Test quote escaping
        let quote_label = "attr=\"value\"";
        let escaped_quote = escape_dot_html_label(quote_label);
        assert!(escaped_quote.contains("&quot;"));
        assert!(!escaped_quote.contains("=\""));

        // Test ampersand must be escaped first
        let amp_label = "a & b < c";
        let escaped_amp = escape_dot_html_label(amp_label);
        // Should be "a &amp; b &lt; c", not "a &amp;amp; ..."
        assert_eq!(escaped_amp, "a &amp; b &lt; c");
    }

    #[test]
    fn test_dot_id_sanitization() {
        assert_eq!(sanitize_dot_id("simple"), "simple");
        assert_eq!(sanitize_dot_id("with spaces"), "with_spaces");
        assert_eq!(sanitize_dot_id("123start"), "_123start");
        assert_eq!(sanitize_dot_id(""), "_anonymous");
        assert_eq!(sanitize_dot_id("a::b"), "a__b");
    }

    #[test]
    fn test_ascii_output() {
        let cfg = sample_cfg();
        let ascii = to_ascii(&cfg);

        assert!(ascii.contains("CFG: test_func"));
        assert!(ascii.contains("Blocks: 3"));
        assert!(ascii.contains("Edges: 2"));
        assert!(ascii.contains("[B0] entry"));
        assert!(ascii.contains("B0 -> B1"));
        assert!(ascii.contains("[true]"));
    }

    #[test]
    fn test_json_output() {
        let cfg = sample_cfg();
        let json = to_json(&cfg).unwrap();

        assert!(json.contains("\"function_name\": \"test_func\""));
        assert!(json.contains("\"entry\""));
        assert!(json.contains("\"exits\""));
    }

    #[test]
    fn test_deterministic_output() {
        // Verify output is consistent across multiple calls
        let cfg = sample_cfg();
        let mermaid1 = to_mermaid(&cfg);
        let mermaid2 = to_mermaid(&cfg);
        assert_eq!(mermaid1, mermaid2);

        let dot1 = to_dot(&cfg);
        let dot2 = to_dot(&cfg);
        assert_eq!(dot1, dot2);
    }

    #[test]
    fn test_edge_ordering_deterministic() {
        // Create CFG with edges in non-sorted order to verify sorting works
        let mut blocks = FxHashMap::default();
        for i in 0..4 {
            blocks.insert(
                BlockId(i),
                CFGBlock {
                    id: BlockId(i),
                    label: format!("block_{}", i),
                    block_type: BlockType::Body,
                    statements: vec![],
                    func_calls: Vec::new(),
                    start_line: i as usize + 1,
                    end_line: i as usize + 1,
                },
            );
        }

        // Insert edges in reverse/unsorted order
        let unsorted_edges = vec![
            CFGEdge::unconditional(BlockId(2), BlockId(3)),
            CFGEdge::with_condition(
                BlockId(0),
                BlockId(2),
                EdgeType::True,
                "branch_a".to_string(),
            ),
            CFGEdge::unconditional(BlockId(1), BlockId(3)),
            CFGEdge::with_condition(
                BlockId(0),
                BlockId(1),
                EdgeType::False,
                "branch_b".to_string(),
            ),
        ];

        let cfg = CFGInfo {
            function_name: "test_edge_order".to_string(),
            blocks,
            edges: unsorted_edges,
            entry: BlockId(0),
            exits: vec![BlockId(3)],
            decision_points: 1,
            comprehension_decision_points: 0,
            nested_cfgs: FxHashMap::default(),
            is_async: false,
            await_points: 0,
            blocking_calls: Vec::new(),
            ..Default::default()
        };

        // Verify Mermaid output has edges in sorted order
        let mermaid = to_mermaid(&cfg);
        let edge_lines: Vec<&str> = mermaid.lines().filter(|l| l.contains("-->")).collect();

        // Expected order: (0,1), (0,2), (1,3), (2,3)
        assert!(edge_lines[0].contains("B0") && edge_lines[0].contains("B1"));
        assert!(edge_lines[1].contains("B0") && edge_lines[1].contains("B2"));
        assert!(edge_lines[2].contains("B1") && edge_lines[2].contains("B3"));
        assert!(edge_lines[3].contains("B2") && edge_lines[3].contains("B3"));

        // Verify DOT output has edges in sorted order
        let dot = to_dot(&cfg);
        let dot_edge_lines: Vec<&str> = dot
            .lines()
            .filter(|l| l.contains("->") && !l.contains("rankdir"))
            .collect();

        assert!(dot_edge_lines[0].contains("B0 -> B1"));
        assert!(dot_edge_lines[1].contains("B0 -> B2"));
        assert!(dot_edge_lines[2].contains("B1 -> B3"));
        assert!(dot_edge_lines[3].contains("B2 -> B3"));

        // Verify ASCII output has edges in sorted order
        let ascii = to_ascii(&cfg);
        let ascii_edge_section: &str = ascii.split("Edges:\n").nth(1).unwrap();
        let ascii_edge_lines: Vec<&str> = ascii_edge_section
            .lines()
            .filter(|l| l.contains("->"))
            .collect();

        assert!(ascii_edge_lines[0].contains("B0 -> B1"));
        assert!(ascii_edge_lines[1].contains("B0 -> B2"));
        assert!(ascii_edge_lines[2].contains("B1 -> B3"));
        assert!(ascii_edge_lines[3].contains("B2 -> B3"));
    }
}
