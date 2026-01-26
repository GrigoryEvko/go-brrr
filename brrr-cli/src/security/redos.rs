//! ReDoS (Regular Expression Denial of Service) detection.
//!
//! Detects regex patterns vulnerable to catastrophic backtracking, which can
//! cause exponential or polynomial time complexity when matching malicious inputs.
//!
//! # Architecture
//!
//! The detector works in two phases:
//! 1. **Regex Extraction**: Find regex patterns in source code using language-specific patterns
//! 2. **Vulnerability Analysis**: Parse regex AST to detect dangerous constructs
//!
//! # Vulnerable Patterns Detected
//!
//! ## Exponential (Catastrophic) Backtracking
//! - Nested quantifiers: `(a+)+`, `(a*)*`, `(a+)*`, `(a*)+`
//! - Quantified groups with internal quantifiers: `(.*)+`
//! - Overlapping alternations with quantifiers: `(a|a)+`, `(a|ab)+`
//!
//! ## Polynomial Backtracking
//! - Overlapping adjacent quantifiers: `.*.*`, `a+a+`
//! - Alternations with shared prefixes: `(abc|abd)+`
//!
//! # Safe Patterns (Not Flagged)
//!
//! - Possessive quantifiers: `a++`, `(a+)++` (if supported by regex engine)
//! - Atomic groups: `(?>a+)` (if supported by regex engine)
//! - Non-backtracking engines (Rust regex crate uses DFA, inherently safe)
//!
//! # Language Support
//!
//! - **Python**: `re.compile(pattern)`, `re.match(pattern, ...)`, `re.search(...)`
//! - **TypeScript/JavaScript**: `new RegExp(pattern)`, `/pattern/`, `.match()`, `.replace()`
//! - **Rust**: `Regex::new(pattern)` (note: Rust regex crate is safe by design)
//! - **Go**: `regexp.Compile(pattern)`, `regexp.MustCompile(pattern)`
//!
//! # Attack String Generation
//!
//! For confirmed vulnerabilities, the detector generates attack strings that
//! demonstrate the exponential blowup. These strings typically consist of:
//! - A prefix matching the vulnerable part
//! - A suffix that forces maximum backtracking

// Allow dead code - types are used from main.rs binary crate
#![allow(dead_code)]
#![allow(unused_variables)]

use std::collections::{HashMap, HashSet};
use std::path::Path;

use serde::{Deserialize, Serialize};
use streaming_iterator::StreamingIterator;
use tree_sitter::{Node, Query, QueryCursor};
use wide::{u8x32, CmpEq};

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;

// =============================================================================
// SIMD Metacharacter Position Finding
// =============================================================================

/// Metacharacter positions found via SIMD pre-pass.
/// Each vector contains byte offsets where that metacharacter appears.
#[derive(Debug, Default)]
struct MetacharPositions {
    /// Positions of `\` (backslash) - escape marker
    backslash: Vec<usize>,
    /// Positions of `(` - group start
    open_paren: Vec<usize>,
    /// Positions of `)` - group end
    close_paren: Vec<usize>,
    /// Positions of `+` - plus quantifier
    plus: Vec<usize>,
    /// Positions of `*` - star quantifier
    star: Vec<usize>,
    /// Positions of `{` - brace quantifier start
    open_brace: Vec<usize>,
}

impl MetacharPositions {
    /// Find all metacharacter positions using SIMD.
    /// Processes 32 bytes at a time for maximum throughput.
    fn find_all(bytes: &[u8]) -> Self {
        let mut result = Self::default();
        let len = bytes.len();

        // SIMD splat vectors for each metacharacter
        let backslash_vec = u8x32::splat(b'\\');
        let open_paren_vec = u8x32::splat(b'(');
        let close_paren_vec = u8x32::splat(b')');
        let plus_vec = u8x32::splat(b'+');
        let star_vec = u8x32::splat(b'*');
        let open_brace_vec = u8x32::splat(b'{');

        // Process 32 bytes at a time
        let chunks = len / 32;
        for chunk_idx in 0..chunks {
            let offset = chunk_idx * 32;
            let chunk: [u8; 32] = bytes[offset..offset + 32]
                .try_into()
                .expect("slice length verified");
            let data = u8x32::from(chunk);

            // Compare all 32 bytes against each metacharacter simultaneously
            Self::extract_positions(data.cmp_eq(backslash_vec), offset, &mut result.backslash);
            Self::extract_positions(data.cmp_eq(open_paren_vec), offset, &mut result.open_paren);
            Self::extract_positions(
                data.cmp_eq(close_paren_vec),
                offset,
                &mut result.close_paren,
            );
            Self::extract_positions(data.cmp_eq(plus_vec), offset, &mut result.plus);
            Self::extract_positions(data.cmp_eq(star_vec), offset, &mut result.star);
            Self::extract_positions(data.cmp_eq(open_brace_vec), offset, &mut result.open_brace);
        }

        // Handle remaining bytes (tail < 32 bytes) with scalar fallback
        let tail_start = chunks * 32;
        for (i, &byte) in bytes[tail_start..].iter().enumerate() {
            let pos = tail_start + i;
            match byte {
                b'\\' => result.backslash.push(pos),
                b'(' => result.open_paren.push(pos),
                b')' => result.close_paren.push(pos),
                b'+' => result.plus.push(pos),
                b'*' => result.star.push(pos),
                b'{' => result.open_brace.push(pos),
                _ => {}
            }
        }

        result
    }

    /// Extract matching positions from SIMD comparison result.
    /// The comparison result has 0xFF for matches, 0x00 for non-matches.
    #[inline]
    fn extract_positions(cmp_result: u8x32, base_offset: usize, positions: &mut Vec<usize>) {
        // Convert to array and check each lane
        let arr: [u8; 32] = cmp_result.into();
        for (i, &mask) in arr.iter().enumerate() {
            if mask != 0 {
                positions.push(base_offset + i);
            }
        }
    }

    /// Check if a position is escaped (preceded by an odd number of backslashes).
    fn is_escaped(&self, pos: usize) -> bool {
        if pos == 0 {
            return false;
        }
        // Count consecutive backslashes before this position
        let mut count = 0;
        for &bs_pos in self.backslash.iter().rev() {
            if bs_pos == pos - 1 - count {
                count += 1;
            } else if bs_pos < pos - 1 - count {
                break;
            }
        }
        // Odd number of backslashes means the character is escaped
        count % 2 == 1
    }
}

// =============================================================================
// Types
// =============================================================================

/// Type of ReDoS vulnerability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum VulnerabilityType {
    /// Exponential time complexity O(2^n) - catastrophic backtracking.
    /// Caused by nested quantifiers or overlapping alternations with quantifiers.
    Exponential,
    /// Polynomial time complexity O(n^k) - still problematic for large inputs.
    /// Caused by overlapping adjacent quantifiers.
    Polynomial,
}

impl std::fmt::Display for VulnerabilityType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Exponential => write!(f, "exponential"),
            Self::Polynomial => write!(f, "polynomial"),
        }
    }
}

/// Severity level for ReDoS findings.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Severity {
    /// Critical: Exponential complexity with user-controlled input.
    Critical,
    /// High: Exponential complexity or polynomial with user input.
    High,
    /// Medium: Polynomial complexity or exponential without clear user input.
    Medium,
    /// Low: Potential issue, needs review.
    Low,
    /// Informational: Pattern detected but likely safe (e.g., Rust regex crate).
    Info,
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Critical => write!(f, "CRITICAL"),
            Self::High => write!(f, "HIGH"),
            Self::Medium => write!(f, "MEDIUM"),
            Self::Low => write!(f, "LOW"),
            Self::Info => write!(f, "INFO"),
        }
    }
}

impl std::str::FromStr for Severity {
    type Err = String;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "critical" => Ok(Self::Critical),
            "high" => Ok(Self::High),
            "medium" => Ok(Self::Medium),
            "low" => Ok(Self::Low),
            "info" => Ok(Self::Info),
            _ => Err(format!("Unknown severity: {s}")),
        }
    }
}

/// Confidence level for detection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Confidence {
    /// High confidence: Clear vulnerable pattern identified.
    High,
    /// Medium confidence: Likely vulnerable but may have mitigations.
    Medium,
    /// Low confidence: Possible issue, manual review recommended.
    Low,
}

impl std::fmt::Display for Confidence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::High => write!(f, "HIGH"),
            Self::Medium => write!(f, "MEDIUM"),
            Self::Low => write!(f, "LOW"),
        }
    }
}

impl std::str::FromStr for Confidence {
    type Err = String;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "high" => Ok(Self::High),
            "medium" => Ok(Self::Medium),
            "low" => Ok(Self::Low),
            _ => Err(format!("Unknown confidence: {s}")),
        }
    }
}

/// Location of a finding in source code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Location {
    /// File path.
    pub file: String,
    /// Line number (1-indexed).
    pub line: usize,
    /// Column number (1-indexed).
    pub column: usize,
    /// End line number (1-indexed).
    pub end_line: usize,
    /// End column number (1-indexed).
    pub end_column: usize,
}

/// Specific vulnerable construct identified in the regex.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VulnerableConstruct {
    /// Type of construct (e.g., "nested_quantifier", "overlapping_alternation").
    pub construct_type: String,
    /// The specific pattern fragment that is vulnerable.
    pub pattern_fragment: String,
    /// Position within the regex pattern (0-indexed).
    pub position: usize,
    /// Length of the vulnerable fragment.
    pub length: usize,
}

/// A ReDoS vulnerability finding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReDoSFinding {
    /// Location in source code.
    pub location: Location,
    /// The regex pattern that is vulnerable.
    pub regex_pattern: String,
    /// Type of vulnerability (exponential or polynomial).
    pub vulnerability_type: VulnerabilityType,
    /// Generated attack string that triggers the vulnerability.
    pub attack_string: String,
    /// Estimated time complexity (e.g., "O(2^n)", "O(n^2)").
    pub complexity: String,
    /// Severity level.
    pub severity: Severity,
    /// Confidence level.
    pub confidence: Confidence,
    /// Specific vulnerable constructs identified.
    pub vulnerable_constructs: Vec<VulnerableConstruct>,
    /// Human-readable description.
    pub description: String,
    /// Suggested remediation.
    pub remediation: String,
    /// Whether the regex is anchored (affects exploitability).
    pub is_anchored: bool,
    /// The regex function/method used (e.g., "re.compile", "RegExp").
    pub regex_function: String,
    /// Code snippet showing the vulnerable regex.
    pub code_snippet: String,
}

/// Summary of ReDoS scan results.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScanResult {
    /// All findings.
    pub findings: Vec<ReDoSFinding>,
    /// Number of files scanned.
    pub files_scanned: usize,
    /// Number of regex patterns analyzed.
    pub patterns_analyzed: usize,
    /// Counts by severity.
    pub severity_counts: HashMap<String, usize>,
    /// Counts by vulnerability type.
    pub vulnerability_type_counts: HashMap<String, usize>,
    /// Language filter used.
    pub language: String,
}

// =============================================================================
// Regex Pattern Analysis
// =============================================================================

/// Token in a parsed regex pattern.
#[derive(Debug, Clone, PartialEq)]
enum RegexToken {
    /// Literal character.
    Literal(char),
    /// Character class [abc] or [^abc].
    CharClass { negated: bool, chars: String },
    /// Predefined class like \d, \w, \s.
    PredefinedClass(char),
    /// Dot (matches any character).
    Dot,
    /// Start anchor ^.
    StartAnchor,
    /// End anchor $.
    EndAnchor,
    /// Quantifier: *, +, ?, {n}, {n,}, {n,m}.
    Quantifier {
        min: usize,
        max: Option<usize>,
        greedy: bool,
        possessive: bool,
    },
    /// Group start (.
    GroupStart {
        capturing: bool,
        atomic: bool,
        lookahead: bool,
        lookbehind: bool,
    },
    /// Group end ).
    GroupEnd,
    /// Alternation |.
    Alternation,
    /// Backreference \1, \2, etc.
    Backreference(usize),
    /// Word boundary \b or \B.
    WordBoundary(bool),
}

/// Parsed group with its contents and quantifier.
#[derive(Debug, Clone)]
struct ParsedGroup {
    /// Tokens inside the group.
    tokens: Vec<RegexToken>,
    /// Nested groups.
    nested_groups: Vec<ParsedGroup>,
    /// Quantifier applied to this group (if any).
    quantifier: Option<RegexToken>,
    /// Whether this group is atomic.
    is_atomic: bool,
    /// Start position in original pattern.
    start_pos: usize,
    /// End position in original pattern.
    end_pos: usize,
}

/// Result of regex vulnerability analysis.
#[derive(Debug, Clone)]
struct AnalysisResult {
    /// Vulnerable constructs found.
    constructs: Vec<VulnerableConstruct>,
    /// Most severe vulnerability type.
    vulnerability_type: Option<VulnerabilityType>,
    /// Whether the pattern is anchored at start.
    anchored_start: bool,
    /// Whether the pattern is anchored at end.
    anchored_end: bool,
    /// Estimated complexity string.
    complexity: String,
}

/// Regex pattern analyzer for detecting ReDoS vulnerabilities.
struct RegexAnalyzer {
    pattern: String,
    position: usize,
}

impl RegexAnalyzer {
    fn new(pattern: &str) -> Self {
        Self {
            pattern: pattern.to_string(),
            position: 0,
        }
    }

    /// Analyze a regex pattern for ReDoS vulnerabilities.
    fn analyze(&mut self) -> AnalysisResult {
        let mut constructs = Vec::new();
        let mut vulnerability_type = None;
        let mut anchored_start = false;
        let mut anchored_end = false;

        // Check for anchors
        if self.pattern.starts_with('^') {
            anchored_start = true;
        }
        if self.pattern.ends_with('$') && !self.pattern.ends_with("\\$") {
            anchored_end = true;
        }

        // Detect nested quantifiers: (a+)+, (a*)+, etc.
        self.detect_nested_quantifiers(&mut constructs, &mut vulnerability_type);

        // Detect overlapping alternations: (a|a)+, (ab|a)+
        self.detect_overlapping_alternations(&mut constructs, &mut vulnerability_type);

        // Detect adjacent overlapping quantifiers: .*.*
        self.detect_adjacent_quantifiers(&mut constructs, &mut vulnerability_type);

        // Detect quantified backreferences: (a+)\1+
        self.detect_quantified_backreferences(&mut constructs, &mut vulnerability_type);

        let complexity = match vulnerability_type {
            Some(VulnerabilityType::Exponential) => "O(2^n)".to_string(),
            Some(VulnerabilityType::Polynomial) => "O(n^2)".to_string(),
            None => "O(n)".to_string(),
        };

        AnalysisResult {
            constructs,
            vulnerability_type,
            anchored_start,
            anchored_end,
            complexity,
        }
    }

    /// Detect nested quantifiers like (a+)+, (a*)+, (a+)*, etc.
    fn detect_nested_quantifiers(
        &self,
        constructs: &mut Vec<VulnerableConstruct>,
        vuln_type: &mut Option<VulnerabilityType>,
    ) {
        // Patterns for nested quantifiers with capturing or non-capturing groups
        let nested_patterns = [
            // (x+)+ patterns
            (r"\([^)]*[+*][^)]*\)[+*]", "nested_quantifier"),
            (r"\([^)]*[+*][^)]*\)\{", "nested_quantifier"),
            // (?:x+)+ patterns
            (r"\(\?:[^)]*[+*][^)]*\)[+*]", "nested_quantifier"),
            (r"\(\?:[^)]*[+*][^)]*\)\{", "nested_quantifier"),
            // Specific evil patterns
            (r"\([a-zA-Z\[\]\\dws.-]+\+\)+\+", "evil_nested"),
            (r"\([a-zA-Z\[\]\\dws.-]+\*\)+\*", "evil_nested"),
            (r"\([a-zA-Z\[\]\\dws.-]+\+\)+\*", "evil_nested"),
            (r"\([a-zA-Z\[\]\\dws.-]+\*\)+\+", "evil_nested"),
        ];

        let re_nested = regex::Regex::new(
            r"(?x)
            # Match groups with internal quantifiers followed by external quantifiers
            \(
                (?:\?:)?                    # Optional non-capturing marker
                [^()]*                      # Content without nested groups
                (?:
                    [+*]                    # Internal quantifier
                    |
                    \{[0-9]+(?:,[0-9]*)?\}  # Or {n,m} quantifier
                )
                [^()]*                      # More content
            \)
            (?:
                [+*]                        # External quantifier
                |
                \{[0-9]+(?:,[0-9]*)?\}      # Or {n,m} quantifier
            )
        ",
        )
        .ok();

        if let Some(re) = re_nested {
            for m in re.find_iter(&self.pattern) {
                constructs.push(VulnerableConstruct {
                    construct_type: "nested_quantifier".to_string(),
                    pattern_fragment: m.as_str().to_string(),
                    position: m.start(),
                    length: m.len(),
                });
                *vuln_type = Some(VulnerabilityType::Exponential);
            }
        }

        // Also check for simple patterns manually for reliability
        self.detect_simple_nested_quantifiers(constructs, vuln_type);
    }

    /// Simple pattern matching for common nested quantifier cases.
    ///
    /// Uses SIMD pre-pass to find all metacharacter positions at once,
    /// then processes positions instead of scanning byte by byte.
    /// This provides significant speedup for longer patterns.
    fn detect_simple_nested_quantifiers(
        &self,
        constructs: &mut Vec<VulnerableConstruct>,
        vuln_type: &mut Option<VulnerabilityType>,
    ) {
        let pattern = &self.pattern;
        let bytes = pattern.as_bytes();

        // SIMD pre-pass: find all metacharacter positions at once
        let positions = MetacharPositions::find_all(bytes);

        // Build escape set for O(1) lookup of escaped positions
        let escaped_positions: HashSet<usize> = positions
            .backslash
            .iter()
            .filter_map(|&bs_pos| {
                // The character after a backslash is escaped (if not itself escaped)
                if bs_pos + 1 < bytes.len() && !positions.is_escaped(bs_pos) {
                    Some(bs_pos + 1)
                } else {
                    None
                }
            })
            .collect();

        // Filter out escaped parentheses
        let open_parens: Vec<usize> = positions
            .open_paren
            .iter()
            .filter(|&&pos| !escaped_positions.contains(&pos))
            .copied()
            .collect();

        let close_parens: Vec<usize> = positions
            .close_paren
            .iter()
            .filter(|&&pos| !escaped_positions.contains(&pos))
            .copied()
            .collect();

        // Build quantifier position set for fast internal quantifier detection
        let quantifier_positions: HashSet<usize> = positions
            .plus
            .iter()
            .chain(positions.star.iter())
            .chain(positions.open_brace.iter())
            .filter(|&&pos| !escaped_positions.contains(&pos))
            .copied()
            .collect();

        // Match open parens to close parens using stack-based pairing
        // Result: Vec<(open_pos, close_pos)>
        let mut group_stack: Vec<usize> = Vec::with_capacity(open_parens.len());
        let mut groups: Vec<(usize, usize)> = Vec::with_capacity(open_parens.len());

        // Merge open and close parens into sorted event stream
        let mut open_idx = 0;
        let mut close_idx = 0;
        while open_idx < open_parens.len() || close_idx < close_parens.len() {
            let open_pos = open_parens.get(open_idx).copied();
            let close_pos = close_parens.get(close_idx).copied();

            match (open_pos, close_pos) {
                (Some(o), Some(c)) if o < c => {
                    group_stack.push(o);
                    open_idx += 1;
                }
                (Some(_), Some(c)) => {
                    if let Some(start) = group_stack.pop() {
                        groups.push((start, c));
                    }
                    close_idx += 1;
                }
                (Some(o), None) => {
                    group_stack.push(o);
                    open_idx += 1;
                }
                (None, Some(_)) => {
                    if let Some(start) = group_stack.pop() {
                        groups.push((start, close_parens[close_idx]));
                    }
                    close_idx += 1;
                }
                (None, None) => break,
            }
        }

        // Check each group for nested quantifier pattern
        for (start, end) in groups {
            // Check if group content has internal quantifier
            let has_internal_quantifier = quantifier_positions
                .iter()
                .any(|&pos| pos > start && pos < end);

            if !has_internal_quantifier {
                continue;
            }

            // Check if group is followed by external quantifier
            let next_pos = end + 1;
            if next_pos >= bytes.len() {
                continue;
            }

            let has_external_quantifier = quantifier_positions.contains(&next_pos);
            if !has_external_quantifier {
                continue;
            }

            // Calculate fragment end position
            let fragment_end = if bytes[next_pos] == b'{' {
                // Find closing brace for {n,m} quantifier
                bytes[next_pos..]
                    .iter()
                    .position(|&b| b == b'}')
                    .map(|p| next_pos + p + 1)
                    .unwrap_or(next_pos + 1)
            } else {
                next_pos + 1
            };

            // Extract fragment (handle UTF-8 properly)
            let fragment = String::from_utf8_lossy(&bytes[start..fragment_end]).to_string();

            // Deduplicate with already found constructs
            let already_found = constructs
                .iter()
                .any(|c| c.position == start && c.construct_type == "nested_quantifier");

            if !already_found {
                constructs.push(VulnerableConstruct {
                    construct_type: "nested_quantifier".to_string(),
                    pattern_fragment: fragment,
                    position: start,
                    length: fragment_end - start,
                });
                *vuln_type = Some(VulnerabilityType::Exponential);
            }
        }
    }

    /// Detect overlapping alternations like (a|a)+, (ab|a)+.
    fn detect_overlapping_alternations(
        &self,
        constructs: &mut Vec<VulnerableConstruct>,
        vuln_type: &mut Option<VulnerabilityType>,
    ) {
        // Pattern for groups with alternation followed by quantifier
        let re_alt =
            regex::Regex::new(r"\((?:\?:)?([^()]+\|[^()]+)\)([+*]|\{[0-9]+(?:,[0-9]*)?\})").ok();

        if let Some(re) = re_alt {
            for m in re.find_iter(&self.pattern) {
                let alt_content = m.as_str();

                // Extract alternatives from the group
                if let Some(start) = alt_content.find('(') {
                    if let Some(end) = alt_content.rfind(')') {
                        let inner = &alt_content[start + 1..end];
                        let inner = inner.strip_prefix("?:").unwrap_or(inner);
                        let alternatives: Vec<&str> = inner.split('|').collect();

                        // Check for overlapping alternatives
                        if self.check_alternatives_overlap(&alternatives) {
                            constructs.push(VulnerableConstruct {
                                construct_type: "overlapping_alternation".to_string(),
                                pattern_fragment: m.as_str().to_string(),
                                position: m.start(),
                                length: m.len(),
                            });
                            *vuln_type = Some(VulnerabilityType::Exponential);
                        }
                    }
                }
            }
        }
    }

    /// Check if alternatives in an alternation overlap.
    fn check_alternatives_overlap(&self, alternatives: &[&str]) -> bool {
        if alternatives.len() < 2 {
            return false;
        }

        // Convert alternatives to character sets for comparison
        let sets: Vec<HashSet<char>> = alternatives
            .iter()
            .map(|alt| self.get_first_chars(alt))
            .collect();

        // Check for any overlap between alternatives
        for i in 0..sets.len() {
            for j in i + 1..sets.len() {
                if !sets[i].is_disjoint(&sets[j]) {
                    return true;
                }
            }
        }

        // Also check for prefix overlap
        for i in 0..alternatives.len() {
            for j in i + 1..alternatives.len() {
                if alternatives[i].starts_with(alternatives[j])
                    || alternatives[j].starts_with(alternatives[i])
                {
                    return true;
                }
            }
        }

        false
    }

    /// Get the set of possible first characters for a pattern.
    fn get_first_chars(&self, pattern: &str) -> HashSet<char> {
        let mut chars = HashSet::new();
        let pattern_chars: Vec<char> = pattern.chars().collect();

        if pattern_chars.is_empty() {
            return chars;
        }

        let first = pattern_chars[0];
        match first {
            '.' => {
                // Dot matches any character - represent with common chars
                for c in 'a'..='z' {
                    chars.insert(c);
                }
                for c in 'A'..='Z' {
                    chars.insert(c);
                }
                for c in '0'..='9' {
                    chars.insert(c);
                }
            }
            '[' => {
                // Character class - extract chars
                if let Some(end) = pattern.find(']') {
                    let class_content = &pattern[1..end];
                    let negated = class_content.starts_with('^');
                    let content = if negated {
                        &class_content[1..]
                    } else {
                        class_content
                    };

                    // Simple character extraction (doesn't handle ranges perfectly)
                    for c in content.chars() {
                        if c != '-' {
                            chars.insert(c);
                        }
                    }

                    // Handle ranges like a-z
                    let content_chars: Vec<char> = content.chars().collect();
                    for i in 0..content_chars.len() {
                        if i + 2 < content_chars.len() && content_chars[i + 1] == '-' {
                            let start = content_chars[i];
                            let end = content_chars[i + 2];
                            if start < end {
                                for c in start..=end {
                                    chars.insert(c);
                                }
                            }
                        }
                    }
                }
            }
            '\\' if pattern_chars.len() > 1 => match pattern_chars[1] {
                'd' => {
                    for c in '0'..='9' {
                        chars.insert(c);
                    }
                }
                'w' => {
                    for c in 'a'..='z' {
                        chars.insert(c);
                    }
                    for c in 'A'..='Z' {
                        chars.insert(c);
                    }
                    for c in '0'..='9' {
                        chars.insert(c);
                    }
                    chars.insert('_');
                }
                's' => {
                    chars.insert(' ');
                    chars.insert('\t');
                    chars.insert('\n');
                    chars.insert('\r');
                }
                c => {
                    chars.insert(c);
                }
            },
            c if c != '^' && c != '$' && c != '(' && c != ')' => {
                chars.insert(c);
            }
            _ => {}
        }

        chars
    }

    /// Detect adjacent overlapping quantifiers like .*.*.
    fn detect_adjacent_quantifiers(
        &self,
        constructs: &mut Vec<VulnerableConstruct>,
        vuln_type: &mut Option<VulnerabilityType>,
    ) {
        // Patterns for adjacent quantifiers that overlap
        let patterns = [
            // .*.*
            (r"\.\*\.\*", "adjacent_star_star"),
            // .+.+
            (r"\.\+\.\+", "adjacent_plus_plus"),
            // .*.+
            (r"\.\*\.\+", "adjacent_star_plus"),
            // .+.*
            (r"\.\+\.\*", "adjacent_plus_star"),
            // \w*\w* and similar
            (
                r"\\[wWdDsS][+*]\\[wWdDsS][+*]",
                "adjacent_class_quantifiers",
            ),
            // [...]* [...]*
            (
                r"\[[^\]]+\][+*]\[[^\]]+\][+*]",
                "adjacent_class_quantifiers",
            ),
            // a+a+ style
            (r"([a-zA-Z])\+\1\+", "adjacent_same_char"),
            (r"([a-zA-Z])\*\1\*", "adjacent_same_char"),
        ];

        for (pattern, construct_type) in patterns {
            if let Ok(re) = regex::Regex::new(pattern) {
                for m in re.find_iter(&self.pattern) {
                    // Check if we already found this
                    let already_found = constructs.iter().any(|c| c.position == m.start());
                    if !already_found {
                        constructs.push(VulnerableConstruct {
                            construct_type: construct_type.to_string(),
                            pattern_fragment: m.as_str().to_string(),
                            position: m.start(),
                            length: m.len(),
                        });

                        // Adjacent quantifiers cause polynomial complexity
                        if vuln_type.is_none() {
                            *vuln_type = Some(VulnerabilityType::Polynomial);
                        }
                    }
                }
            }
        }
    }

    /// Detect quantified backreferences like (a+)\1+.
    fn detect_quantified_backreferences(
        &self,
        constructs: &mut Vec<VulnerableConstruct>,
        vuln_type: &mut Option<VulnerabilityType>,
    ) {
        // Pattern for backreferences with quantifiers
        let re_backref = regex::Regex::new(r"\\([1-9])([+*]|\{[0-9]+(?:,[0-9]*)?\})").ok();

        if let Some(re) = re_backref {
            for m in re.find_iter(&self.pattern) {
                constructs.push(VulnerableConstruct {
                    construct_type: "quantified_backreference".to_string(),
                    pattern_fragment: m.as_str().to_string(),
                    position: m.start(),
                    length: m.len(),
                });

                // Quantified backreferences can cause exponential complexity
                *vuln_type = Some(VulnerabilityType::Exponential);
            }
        }
    }

    /// Generate an attack string that triggers the vulnerability.
    fn generate_attack_string(&self, result: &AnalysisResult) -> String {
        if result.constructs.is_empty() {
            return String::new();
        }

        // Determine the repeating character based on the vulnerable construct
        let construct = &result.constructs[0];
        let repeat_char = self.extract_repeat_char(&construct.pattern_fragment);

        // Generate attack string based on vulnerability type
        match result.vulnerability_type {
            Some(VulnerabilityType::Exponential) => {
                // For exponential, we need a long string that matches partially
                // followed by a character that fails at the end
                let prefix: String = std::iter::repeat(repeat_char).take(30).collect();
                let suffix = if repeat_char.is_alphabetic() {
                    '!'
                } else {
                    'z'
                };
                format!("{prefix}{suffix}")
            }
            Some(VulnerabilityType::Polynomial) => {
                // For polynomial, similar approach but may need longer string
                let prefix: String = std::iter::repeat(repeat_char).take(50).collect();
                let suffix = if repeat_char.is_alphabetic() {
                    '!'
                } else {
                    'z'
                };
                format!("{prefix}{suffix}")
            }
            None => String::new(),
        }
    }

    /// Extract the character to repeat for attack string generation.
    fn extract_repeat_char(&self, fragment: &str) -> char {
        // Try to find a literal character in the fragment
        for c in fragment.chars() {
            match c {
                'a'..='z' | 'A'..='Z' => return c,
                _ => continue,
            }
        }

        // Check for character classes
        if fragment.contains("\\d") || fragment.contains("[0-9]") {
            return '0';
        }
        if fragment.contains("\\w") || fragment.contains("[a-z]") {
            return 'a';
        }
        if fragment.contains("\\s") {
            return ' ';
        }
        if fragment.contains('.') {
            return 'a'; // Dot matches anything, use 'a'
        }

        'a' // Default
    }
}

// =============================================================================
// Language-Specific Regex Extraction
// =============================================================================

/// Information about an extracted regex pattern.
#[derive(Debug, Clone)]
struct ExtractedRegex {
    /// The regex pattern string.
    pattern: String,
    /// The function/method used (e.g., "re.compile", "RegExp").
    function: String,
    /// Start line (1-indexed).
    line: usize,
    /// Start column (1-indexed).
    column: usize,
    /// End line (1-indexed).
    end_line: usize,
    /// End column (1-indexed).
    end_column: usize,
    /// The full code snippet.
    code_snippet: String,
}

/// Extract regex patterns from Python source code.
fn extract_python_regexes(source: &str, tree: &tree_sitter::Tree) -> Vec<ExtractedRegex> {
    let mut regexes = Vec::new();

    // Python regex functions
    let python_regex_query = r#"
        ; re.compile(pattern)
        (call
          function: (attribute
            object: (identifier) @module (#eq? @module "re")
            attribute: (identifier) @method)
          arguments: (argument_list
            (string) @pattern))

        ; re.match(pattern, string)
        (call
          function: (attribute
            object: (identifier) @module2 (#eq? @module2 "re")
            attribute: (identifier) @method2 (#match? @method2 "^(match|search|findall|finditer|sub|subn|split|fullmatch)$"))
          arguments: (argument_list
            (string) @pattern2))

        ; regex = r"pattern"  followed by re.compile or similar usage
        (assignment
          left: (identifier) @var_name
          right: (string) @pattern3)

        ; Pattern(pattern) for re.Pattern
        (call
          function: (identifier) @func (#eq? @func "Pattern")
          arguments: (argument_list
            (string) @pattern4))
    "#;

    let registry = LanguageRegistry::global();
    let lang_impl = match registry.get_by_name("python") {
        Some(l) => l,
        None => return regexes,
    };

    // Keep parser alive so language reference is valid
    let parser = match lang_impl.parser() {
        Ok(p) => p,
        Err(_) => return regexes,
    };
    let ts_lang = parser.language().expect("Parser should have language");
    let query = match Query::new(&ts_lang, python_regex_query) {
        Ok(q) => q,
        Err(_) => return regexes,
    };

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source.as_bytes());

    while let Some(m) = matches.next() {
        for cap in m.captures {
            let name = query.capture_names()[cap.index as usize];
            if name.starts_with("pattern") {
                let node = cap.node;
                let pattern_text = node_text(node, source);

                // Extract the actual pattern from string literals
                let pattern = extract_string_content(&pattern_text);
                if pattern.is_empty() {
                    continue;
                }

                // Determine the function used
                let function = if name == "pattern" || name == "pattern2" {
                    // Look for the method name in the match
                    let mut func_name = "re.compile".to_string();
                    for cap2 in m.captures {
                        let cap_name = query.capture_names()[cap2.index as usize];
                        if cap_name == "method" || cap_name == "method2" {
                            func_name = format!("re.{}", node_text(cap2.node, source));
                            break;
                        }
                    }
                    func_name
                } else if name == "pattern4" {
                    "Pattern".to_string()
                } else {
                    "string_literal".to_string()
                };

                // Get parent for code snippet
                let snippet_node = node.parent().and_then(|p| p.parent()).unwrap_or(node);

                regexes.push(ExtractedRegex {
                    pattern,
                    function,
                    line: node.start_position().row + 1,
                    column: node.start_position().column + 1,
                    end_line: node.end_position().row + 1,
                    end_column: node.end_position().column + 1,
                    code_snippet: node_text(snippet_node, source),
                });
            }
        }
    }

    regexes
}

/// Extract regex patterns from TypeScript/JavaScript source code.
fn extract_typescript_regexes(
    source: &str,
    tree: &tree_sitter::Tree,
    is_tsx: bool,
) -> Vec<ExtractedRegex> {
    let mut regexes = Vec::new();

    // TypeScript/JavaScript regex patterns
    let ts_regex_query = r#"
        ; /pattern/ regex literals
        (regex) @literal

        ; new RegExp(pattern)
        (new_expression
          constructor: (identifier) @ctor (#eq? @ctor "RegExp")
          arguments: (arguments
            [(string) (template_string)] @pattern))

        ; RegExp(pattern) direct call
        (call_expression
          function: (identifier) @func (#eq? @func "RegExp")
          arguments: (arguments
            [(string) (template_string)] @pattern2))

        ; string.match(pattern), string.replace(pattern, ...)
        (call_expression
          function: (member_expression
            property: (property_identifier) @method (#match? @method "^(match|matchAll|replace|replaceAll|search|split)$"))
          arguments: (arguments
            [(regex) (string) (template_string)] @pattern3))
    "#;

    let registry = LanguageRegistry::global();
    let lang_name = if is_tsx { "tsx" } else { "typescript" };
    let lang_impl = match registry.get_by_name(lang_name) {
        Some(l) => l,
        None => return regexes,
    };

    // Keep parser alive so language reference is valid
    let parser = match lang_impl.parser() {
        Ok(p) => p,
        Err(_) => return regexes,
    };
    let ts_lang = parser.language().expect("Parser should have language");
    let query = match Query::new(&ts_lang, ts_regex_query) {
        Ok(q) => q,
        Err(_) => return regexes,
    };

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source.as_bytes());

    while let Some(m) = matches.next() {
        for cap in m.captures {
            let name = query.capture_names()[cap.index as usize];
            let node = cap.node;

            let (pattern, function) = if name == "literal" {
                // Regex literal /pattern/flags
                let text = node_text(node, source);
                let pattern = extract_regex_literal(&text);
                (pattern, "regex_literal".to_string())
            } else if name.starts_with("pattern") {
                let text = node_text(node, source);
                let pattern = if text.starts_with('`') {
                    // Template string
                    extract_template_string(&text)
                } else {
                    extract_string_content(&text)
                };

                let function = if name == "pattern" {
                    "new RegExp".to_string()
                } else if name == "pattern2" {
                    "RegExp".to_string()
                } else {
                    // Find the method name
                    let mut func_name = "string_method".to_string();
                    for cap2 in m.captures {
                        let cap_name = query.capture_names()[cap2.index as usize];
                        if cap_name == "method" {
                            func_name = format!("String.{}", node_text(cap2.node, source));
                            break;
                        }
                    }
                    func_name
                };
                (pattern, function)
            } else {
                continue;
            };

            if pattern.is_empty() {
                continue;
            }

            let snippet_node = node.parent().and_then(|p| p.parent()).unwrap_or(node);

            regexes.push(ExtractedRegex {
                pattern,
                function,
                line: node.start_position().row + 1,
                column: node.start_position().column + 1,
                end_line: node.end_position().row + 1,
                end_column: node.end_position().column + 1,
                code_snippet: node_text(snippet_node, source),
            });
        }
    }

    regexes
}

/// Extract regex patterns from Rust source code.
/// Note: Rust's regex crate uses a DFA engine and is inherently safe from ReDoS.
fn extract_rust_regexes(source: &str, tree: &tree_sitter::Tree) -> Vec<ExtractedRegex> {
    let mut regexes = Vec::new();

    // Rust regex patterns
    let rust_regex_query = r#"
        ; Regex::new(pattern)
        (call_expression
          function: (scoped_identifier
            path: (identifier) @path (#eq? @path "Regex")
            name: (identifier) @method (#eq? @method "new"))
          arguments: (arguments
            (string_literal) @pattern))

        ; regex::Regex::new(pattern)
        (call_expression
          function: (scoped_identifier
            path: (scoped_identifier)
            name: (identifier) @method2 (#eq? @method2 "new"))
          arguments: (arguments
            (string_literal) @pattern2))

        ; RegexBuilder::new(pattern)
        (call_expression
          function: (scoped_identifier
            path: (identifier) @builder (#eq? @builder "RegexBuilder")
            name: (identifier) @method3 (#eq? @method3 "new"))
          arguments: (arguments
            (string_literal) @pattern3))

        ; RegexSet::new([patterns])
        (call_expression
          function: (scoped_identifier
            path: (identifier) @set (#eq? @set "RegexSet")
            name: (identifier) @method4 (#eq? @method4 "new"))
          arguments: (arguments
            (array_expression
              (string_literal) @pattern4)))

        ; lazy_static! with Regex
        (macro_invocation
          macro: (identifier) @macro (#match? @macro "^(lazy_static|once_cell)$")
          (token_tree
            (string_literal) @pattern5))
    "#;

    let registry = LanguageRegistry::global();
    let lang_impl = match registry.get_by_name("rust") {
        Some(l) => l,
        None => return regexes,
    };

    // Keep parser alive so language reference is valid
    let parser = match lang_impl.parser() {
        Ok(p) => p,
        Err(_) => return regexes,
    };
    let ts_lang = parser.language().expect("Parser should have language");
    let query = match Query::new(&ts_lang, rust_regex_query) {
        Ok(q) => q,
        Err(_) => return regexes,
    };

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source.as_bytes());

    while let Some(m) = matches.next() {
        for cap in m.captures {
            let name = query.capture_names()[cap.index as usize];
            if name.starts_with("pattern") {
                let node = cap.node;
                let pattern_text = node_text(node, source);
                let pattern = extract_rust_string(&pattern_text);

                if pattern.is_empty() {
                    continue;
                }

                let function = if name == "pattern" || name == "pattern2" {
                    "Regex::new".to_string()
                } else if name == "pattern3" {
                    "RegexBuilder::new".to_string()
                } else if name == "pattern4" {
                    "RegexSet::new".to_string()
                } else {
                    "lazy_static".to_string()
                };

                let snippet_node = node.parent().and_then(|p| p.parent()).unwrap_or(node);

                regexes.push(ExtractedRegex {
                    pattern,
                    function,
                    line: node.start_position().row + 1,
                    column: node.start_position().column + 1,
                    end_line: node.end_position().row + 1,
                    end_column: node.end_position().column + 1,
                    code_snippet: node_text(snippet_node, source),
                });
            }
        }
    }

    regexes
}

/// Extract regex patterns from Go source code.
fn extract_go_regexes(source: &str, tree: &tree_sitter::Tree) -> Vec<ExtractedRegex> {
    let mut regexes = Vec::new();

    // Go regex patterns
    let go_regex_query = r#"
        ; regexp.Compile(pattern)
        (call_expression
          function: (selector_expression
            operand: (identifier) @pkg (#eq? @pkg "regexp")
            field: (field_identifier) @method (#match? @method "^(Compile|MustCompile|CompilePOSIX|MustCompilePOSIX)$"))
          arguments: (argument_list
            [(interpreted_string_literal) (raw_string_literal)] @pattern))

        ; regexp.Match(pattern, input)
        (call_expression
          function: (selector_expression
            operand: (identifier) @pkg2 (#eq? @pkg2 "regexp")
            field: (field_identifier) @method2 (#match? @method2 "^(Match|MatchString|MatchReader)$"))
          arguments: (argument_list
            [(interpreted_string_literal) (raw_string_literal)] @pattern2
            . _*))
    "#;

    let registry = LanguageRegistry::global();
    let lang_impl = match registry.get_by_name("go") {
        Some(l) => l,
        None => return regexes,
    };

    // Keep parser alive so language reference is valid
    let parser = match lang_impl.parser() {
        Ok(p) => p,
        Err(_) => return regexes,
    };
    let ts_lang = parser.language().expect("Parser should have language");
    let query = match Query::new(&ts_lang, go_regex_query) {
        Ok(q) => q,
        Err(_) => return regexes,
    };

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source.as_bytes());

    while let Some(m) = matches.next() {
        for cap in m.captures {
            let name = query.capture_names()[cap.index as usize];
            if name.starts_with("pattern") {
                let node = cap.node;
                let pattern_text = node_text(node, source);
                let pattern = extract_go_string(&pattern_text);

                if pattern.is_empty() {
                    continue;
                }

                // Find the method name
                let mut function = "regexp.Compile".to_string();
                for cap2 in m.captures {
                    let cap_name = query.capture_names()[cap2.index as usize];
                    if cap_name == "method" || cap_name == "method2" {
                        function = format!("regexp.{}", node_text(cap2.node, source));
                        break;
                    }
                }

                let snippet_node = node.parent().and_then(|p| p.parent()).unwrap_or(node);

                regexes.push(ExtractedRegex {
                    pattern,
                    function,
                    line: node.start_position().row + 1,
                    column: node.start_position().column + 1,
                    end_line: node.end_position().row + 1,
                    end_column: node.end_position().column + 1,
                    code_snippet: node_text(snippet_node, source),
                });
            }
        }
    }

    regexes
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Get text content of a node.
fn node_text(node: Node<'_>, source: &str) -> String {
    source[node.byte_range()].to_string()
}

/// Extract the actual string content from a Python/JS string literal.
fn extract_string_content(s: &str) -> String {
    let s = s.trim();

    // Handle raw strings r"..." or r'...'
    let s = s
        .strip_prefix('r')
        .or_else(|| s.strip_prefix('R'))
        .unwrap_or(s);
    let s = s
        .strip_prefix('b')
        .or_else(|| s.strip_prefix('B'))
        .unwrap_or(s);

    // Handle triple-quoted strings
    if s.starts_with("\"\"\"") && s.ends_with("\"\"\"") && s.len() >= 6 {
        return s[3..s.len() - 3].to_string();
    }
    if s.starts_with("'''") && s.ends_with("'''") && s.len() >= 6 {
        return s[3..s.len() - 3].to_string();
    }

    // Handle regular strings
    if (s.starts_with('"') && s.ends_with('"')) || (s.starts_with('\'') && s.ends_with('\'')) {
        if s.len() >= 2 {
            return s[1..s.len() - 1].to_string();
        }
    }

    s.to_string()
}

/// Extract pattern from regex literal /pattern/flags.
fn extract_regex_literal(s: &str) -> String {
    let s = s.trim();
    if s.starts_with('/') {
        // Find the closing / (not escaped)
        let mut end = 1;
        let chars: Vec<char> = s.chars().collect();
        while end < chars.len() {
            if chars[end] == '/' && (end == 1 || chars[end - 1] != '\\') {
                break;
            }
            end += 1;
        }
        if end > 1 && end < chars.len() {
            return chars[1..end].iter().collect();
        }
    }
    s.to_string()
}

/// Extract content from template string `...`.
fn extract_template_string(s: &str) -> String {
    let s = s.trim();
    if s.starts_with('`') && s.ends_with('`') && s.len() >= 2 {
        return s[1..s.len() - 1].to_string();
    }
    s.to_string()
}

/// Extract content from Rust string literal.
fn extract_rust_string(s: &str) -> String {
    let s = s.trim();

    // Raw strings r"..." or r#"..."#
    if s.starts_with("r#") {
        // Count the number of #
        let hash_count = s[1..].chars().take_while(|&c| c == '#').count();
        let prefix = format!("r{}\"", "#".repeat(hash_count));
        let suffix = format!("\"{}", "#".repeat(hash_count));
        if s.starts_with(&prefix) && s.ends_with(&suffix) {
            let start = prefix.len();
            let end = s.len() - suffix.len();
            if end > start {
                return s[start..end].to_string();
            }
        }
    }

    // Raw string r"..."
    if s.starts_with("r\"") && s.ends_with('"') && s.len() >= 3 {
        return s[2..s.len() - 1].to_string();
    }

    // Regular string "..."
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        return s[1..s.len() - 1].to_string();
    }

    s.to_string()
}

/// Extract content from Go string literal.
fn extract_go_string(s: &str) -> String {
    let s = s.trim();

    // Raw string `...`
    if s.starts_with('`') && s.ends_with('`') && s.len() >= 2 {
        return s[1..s.len() - 1].to_string();
    }

    // Interpreted string "..."
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        return s[1..s.len() - 1].to_string();
    }

    s.to_string()
}

// =============================================================================
// Detector Implementation
// =============================================================================

/// ReDoS vulnerability detector.
pub struct ReDoSDetector {
    /// Minimum severity to report.
    min_severity: Severity,
    /// Minimum confidence to report.
    min_confidence: Confidence,
}

impl Default for ReDoSDetector {
    fn default() -> Self {
        Self::new()
    }
}

impl ReDoSDetector {
    /// Create a new ReDoS detector with default settings.
    pub fn new() -> Self {
        Self {
            min_severity: Severity::Low,
            min_confidence: Confidence::Low,
        }
    }

    /// Set the minimum severity level to report.
    #[must_use]
    pub fn with_min_severity(mut self, severity: Severity) -> Self {
        self.min_severity = severity;
        self
    }

    /// Set the minimum confidence level to report.
    #[must_use]
    pub fn with_min_confidence(mut self, confidence: Confidence) -> Self {
        self.min_confidence = confidence;
        self
    }

    /// Scan a file for ReDoS vulnerabilities.
    pub fn scan_file(&self, file_path: &str) -> Result<Vec<ReDoSFinding>> {
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

        let source = std::fs::read_to_string(path).map_err(|e| BrrrError::io_with_path(e, path))?;

        // Get parser and parse the source
        let mut parser = lang.parser_for_path(path)?;
        let tree = parser
            .parse(source.as_bytes(), None)
            .ok_or_else(|| BrrrError::Parse {
                file: file_path.to_string(),
                message: "Failed to parse source file".to_string(),
            })?;

        let lang_name = lang.name();
        self.analyze_tree(file_path, &source, &tree, lang_name)
    }

    /// Analyze a parsed tree for ReDoS vulnerabilities.
    fn analyze_tree(
        &self,
        file_path: &str,
        source: &str,
        tree: &tree_sitter::Tree,
        lang: &str,
    ) -> Result<Vec<ReDoSFinding>> {
        // Extract regex patterns based on language
        let regexes = match lang {
            "python" => extract_python_regexes(source, tree),
            "typescript" | "javascript" => extract_typescript_regexes(source, tree, false),
            "tsx" | "jsx" => extract_typescript_regexes(source, tree, true),
            "rust" => extract_rust_regexes(source, tree),
            "go" => extract_go_regexes(source, tree),
            _ => Vec::new(),
        };

        let mut findings = Vec::new();

        for regex in regexes {
            // Analyze the regex pattern
            let mut analyzer = RegexAnalyzer::new(&regex.pattern);
            let result = analyzer.analyze();

            // Skip if no vulnerability found
            if result.vulnerability_type.is_none() {
                continue;
            }

            let vuln_type = result.vulnerability_type.unwrap();
            let attack_string = analyzer.generate_attack_string(&result);

            // Determine severity based on vulnerability type and language
            let (severity, confidence) = self.determine_severity_confidence(
                vuln_type,
                lang,
                &regex.function,
                result.anchored_start && result.anchored_end,
            );

            // Filter by minimum severity and confidence
            if severity > self.min_severity || confidence > self.min_confidence {
                continue;
            }

            // Generate description and remediation
            let description = self.generate_description(vuln_type, &result.constructs, lang);
            let remediation = self.generate_remediation(vuln_type, lang, &regex.function);

            findings.push(ReDoSFinding {
                location: Location {
                    file: file_path.to_string(),
                    line: regex.line,
                    column: regex.column,
                    end_line: regex.end_line,
                    end_column: regex.end_column,
                },
                regex_pattern: regex.pattern,
                vulnerability_type: vuln_type,
                attack_string,
                complexity: result.complexity,
                severity,
                confidence,
                vulnerable_constructs: result.constructs,
                description,
                remediation,
                is_anchored: result.anchored_start && result.anchored_end,
                regex_function: regex.function,
                code_snippet: regex.code_snippet,
            });
        }

        Ok(findings)
    }

    /// Determine severity and confidence based on vulnerability characteristics.
    fn determine_severity_confidence(
        &self,
        vuln_type: VulnerabilityType,
        lang: &str,
        function: &str,
        is_anchored: bool,
    ) -> (Severity, Confidence) {
        // Rust regex crate is inherently safe (uses DFA, no backtracking)
        if lang == "rust" {
            return (Severity::Info, Confidence::High);
        }

        // Go RE2 is also safe (no backtracking)
        if lang == "go" {
            // RE2 is the default in Go, so this is informational
            return (Severity::Info, Confidence::High);
        }

        // For backtracking engines (Python, JavaScript)
        match vuln_type {
            VulnerabilityType::Exponential => {
                if is_anchored {
                    // Anchored patterns are easier to exploit
                    (Severity::Critical, Confidence::High)
                } else {
                    // Unanchored may have mitigations
                    (Severity::High, Confidence::High)
                }
            }
            VulnerabilityType::Polynomial => {
                if is_anchored {
                    (Severity::High, Confidence::Medium)
                } else {
                    (Severity::Medium, Confidence::Medium)
                }
            }
        }
    }

    /// Generate a human-readable description.
    fn generate_description(
        &self,
        vuln_type: VulnerabilityType,
        constructs: &[VulnerableConstruct],
        lang: &str,
    ) -> String {
        let type_desc = match vuln_type {
            VulnerabilityType::Exponential => {
                "This regex pattern is vulnerable to exponential backtracking (catastrophic ReDoS)"
            }
            VulnerabilityType::Polynomial => {
                "This regex pattern is vulnerable to polynomial backtracking"
            }
        };

        let constructs_desc: Vec<String> = constructs
            .iter()
            .map(|c| match c.construct_type.as_str() {
                "nested_quantifier" => format!(
                    "nested quantifier at position {}: '{}'",
                    c.position, c.pattern_fragment
                ),
                "overlapping_alternation" => format!(
                    "overlapping alternation at position {}: '{}'",
                    c.position, c.pattern_fragment
                ),
                "adjacent_star_star"
                | "adjacent_plus_plus"
                | "adjacent_star_plus"
                | "adjacent_plus_star"
                | "adjacent_class_quantifiers"
                | "adjacent_same_char" => format!(
                    "overlapping adjacent quantifiers at position {}: '{}'",
                    c.position, c.pattern_fragment
                ),
                "quantified_backreference" => format!(
                    "quantified backreference at position {}: '{}'",
                    c.position, c.pattern_fragment
                ),
                _ => format!(
                    "{} at position {}: '{}'",
                    c.construct_type, c.position, c.pattern_fragment
                ),
            })
            .collect();

        let safe_note = match lang {
            "rust" => {
                " Note: Rust's regex crate uses a DFA engine which is inherently safe from ReDoS."
            }
            "go" => " Note: Go's regexp package uses RE2 which is inherently safe from ReDoS.",
            _ => "",
        };

        format!(
            "{}. Vulnerable construct(s): {}.{}",
            type_desc,
            constructs_desc.join("; "),
            safe_note
        )
    }

    /// Generate remediation advice.
    fn generate_remediation(
        &self,
        vuln_type: VulnerabilityType,
        lang: &str,
        function: &str,
    ) -> String {
        // Language-specific safe alternatives
        let lang_specific = match lang {
            "python" => {
                "Consider using the 'regex' library with possessive quantifiers (++) or \
                atomic groups (?>...), or use the 're2' library which uses a safe DFA engine. \
                Example: Install 'google-re2' and use 're2.compile()' instead of 're.compile()'."
            }
            "javascript" | "typescript" | "jsx" | "tsx" => {
                "Consider using the 're2' npm package which wraps Google's RE2 library \
                (safe DFA engine). Example: const RE2 = require('re2'); new RE2(pattern). \
                Alternatively, add input length limits before regex matching."
            }
            "rust" => {
                "The Rust 'regex' crate already uses a safe DFA engine - this is informational only. \
                If using a different regex library that supports backtracking, consider switching \
                to the standard 'regex' crate."
            }
            "go" => {
                "Go's standard 'regexp' package uses RE2 (safe DFA engine) - this is informational only. \
                Ensure you're not using third-party regex libraries with backtracking support."
            }
            _ => {
                "Consider using a regex library with a non-backtracking engine (DFA-based) \
                such as Google RE2, or add strict input length limits before matching."
            }
        };

        let pattern_fix = match vuln_type {
            VulnerabilityType::Exponential => {
                "For nested quantifiers like (a+)+, rewrite to avoid nesting: \
                - Use atomic groups if available: (?>a+)+ \
                - Use possessive quantifiers if available: (a++)+ \
                - Rewrite the pattern to be more specific: [a]+ instead of (a)+ \
                - Add maximum length limits: {1,100} instead of +"
            }
            VulnerabilityType::Polynomial => {
                "For overlapping quantifiers like .*.*: \
                - Be more specific about what you're matching \
                - Use atomic groups or possessive quantifiers \
                - Split into separate regex operations \
                - Add maximum length limits with {n,m} syntax"
            }
        };

        format!("{} {}", pattern_fix, lang_specific)
    }

    /// Scan a directory for ReDoS vulnerabilities.
    pub fn scan_directory(&self, dir_path: &str, lang_filter: Option<&str>) -> Result<ScanResult> {
        let path = Path::new(dir_path);
        if !path.exists() {
            return Err(BrrrError::io_with_path(
                std::io::Error::new(std::io::ErrorKind::NotFound, "Directory not found"),
                path,
            ));
        }

        // Use ProjectScanner for directory traversal
        let scanner = ProjectScanner::new(dir_path)?;
        let config = match lang_filter {
            Some(lang) => ScanConfig::for_language(lang),
            None => ScanConfig::default(),
        };
        let scan_result = scanner.scan_with_config(&config)?;

        let mut findings = Vec::new();
        let mut patterns_analyzed = 0;
        let mut files_scanned = 0;

        for file in &scan_result.files {
            let file_path_str = file.to_string_lossy();

            // Filter by language if specified
            if let Some(filter) = lang_filter {
                let registry = LanguageRegistry::global();
                if let Some(detected) = registry.detect_language(file) {
                    if detected.name() != filter {
                        continue;
                    }
                } else {
                    continue;
                }
            }

            match self.scan_file(&file_path_str) {
                Ok(file_findings) => {
                    patterns_analyzed += file_findings.len();
                    findings.extend(file_findings);
                    files_scanned += 1;
                }
                Err(e) => {
                    // Log but continue on errors
                    tracing::warn!("Error scanning {}: {}", file_path_str, e);
                }
            }
        }

        // Count by severity
        let mut severity_counts: HashMap<String, usize> = HashMap::new();
        for finding in &findings {
            *severity_counts
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
        }

        // Count by vulnerability type
        let mut vulnerability_type_counts: HashMap<String, usize> = HashMap::new();
        for finding in &findings {
            *vulnerability_type_counts
                .entry(finding.vulnerability_type.to_string())
                .or_insert(0) += 1;
        }

        Ok(ScanResult {
            findings,
            files_scanned,
            patterns_analyzed,
            severity_counts,
            vulnerability_type_counts,
            language: lang_filter.unwrap_or("all").to_string(),
        })
    }
}

// =============================================================================
// Public API
// =============================================================================

/// Scan a file or directory for ReDoS vulnerabilities.
///
/// # Arguments
///
/// * `path` - Path to file or directory to scan
/// * `lang_filter` - Optional language filter (e.g., "python", "typescript")
///
/// # Returns
///
/// Scan result with all findings
///
/// # Example
///
/// ```ignore
/// use brrr::security::redos::scan_redos;
///
/// let result = scan_redos("./src", Some("python"))?;
/// for finding in &result.findings {
///     println!("{}: {} at {}:{}",
///         finding.severity,
///         finding.regex_pattern,
///         finding.location.file,
///         finding.location.line
///     );
/// }
/// ```
pub fn scan_redos(path: &str, lang_filter: Option<&str>) -> Result<ScanResult> {
    let detector = ReDoSDetector::new();
    let path_obj = Path::new(path);

    if path_obj.is_file() {
        let findings = detector.scan_file(path)?;
        let mut severity_counts = HashMap::new();
        let mut vulnerability_type_counts = HashMap::new();

        for finding in &findings {
            *severity_counts
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
            *vulnerability_type_counts
                .entry(finding.vulnerability_type.to_string())
                .or_insert(0) += 1;
        }

        Ok(ScanResult {
            patterns_analyzed: findings.len(),
            findings,
            files_scanned: 1,
            severity_counts,
            vulnerability_type_counts,
            language: lang_filter.unwrap_or("auto").to_string(),
        })
    } else {
        detector.scan_directory(path, lang_filter)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nested_quantifier_detection() {
        let mut analyzer = RegexAnalyzer::new("(a+)+");
        let result = analyzer.analyze();
        assert_eq!(
            result.vulnerability_type,
            Some(VulnerabilityType::Exponential)
        );
        assert!(!result.constructs.is_empty());
        assert_eq!(result.constructs[0].construct_type, "nested_quantifier");
    }

    #[test]
    fn test_nested_quantifier_star() {
        let mut analyzer = RegexAnalyzer::new("(a*)*");
        let result = analyzer.analyze();
        assert_eq!(
            result.vulnerability_type,
            Some(VulnerabilityType::Exponential)
        );
    }

    #[test]
    fn test_nested_quantifier_mixed() {
        let mut analyzer = RegexAnalyzer::new("(a+)*");
        let result = analyzer.analyze();
        assert_eq!(
            result.vulnerability_type,
            Some(VulnerabilityType::Exponential)
        );
    }

    #[test]
    fn test_dot_star_nested() {
        let mut analyzer = RegexAnalyzer::new("(.*)+");
        let result = analyzer.analyze();
        assert_eq!(
            result.vulnerability_type,
            Some(VulnerabilityType::Exponential)
        );
    }

    #[test]
    fn test_character_class_nested() {
        let mut analyzer = RegexAnalyzer::new("([a-zA-Z]+)+");
        let result = analyzer.analyze();
        assert_eq!(
            result.vulnerability_type,
            Some(VulnerabilityType::Exponential)
        );
    }

    #[test]
    fn test_adjacent_quantifiers() {
        let mut analyzer = RegexAnalyzer::new(".*.*");
        let result = analyzer.analyze();
        assert_eq!(
            result.vulnerability_type,
            Some(VulnerabilityType::Polynomial)
        );
    }

    #[test]
    fn test_overlapping_alternation() {
        let mut analyzer = RegexAnalyzer::new("(a|a)+");
        let result = analyzer.analyze();
        assert_eq!(
            result.vulnerability_type,
            Some(VulnerabilityType::Exponential)
        );
    }

    #[test]
    fn test_overlapping_alternation_prefix() {
        let mut analyzer = RegexAnalyzer::new("(ab|a)+");
        let result = analyzer.analyze();
        assert_eq!(
            result.vulnerability_type,
            Some(VulnerabilityType::Exponential)
        );
    }

    #[test]
    fn test_safe_pattern_no_quantifier() {
        let mut analyzer = RegexAnalyzer::new("abc");
        let result = analyzer.analyze();
        assert_eq!(result.vulnerability_type, None);
    }

    #[test]
    fn test_safe_pattern_simple_quantifier() {
        let mut analyzer = RegexAnalyzer::new("a+");
        let result = analyzer.analyze();
        assert_eq!(result.vulnerability_type, None);
    }

    #[test]
    fn test_safe_pattern_non_overlapping_alt() {
        let mut analyzer = RegexAnalyzer::new("(a|b)+");
        let result = analyzer.analyze();
        // Non-overlapping alternatives should not be flagged
        assert!(
            result.vulnerability_type.is_none()
                || result
                    .constructs
                    .iter()
                    .all(|c| c.construct_type != "overlapping_alternation")
        );
    }

    #[test]
    fn test_anchored_detection() {
        let mut analyzer = RegexAnalyzer::new("^(a+)+$");
        let result = analyzer.analyze();
        assert!(result.anchored_start);
        assert!(result.anchored_end);
        assert_eq!(
            result.vulnerability_type,
            Some(VulnerabilityType::Exponential)
        );
    }

    #[test]
    fn test_non_capturing_group() {
        let mut analyzer = RegexAnalyzer::new("(?:a+)+");
        let result = analyzer.analyze();
        assert_eq!(
            result.vulnerability_type,
            Some(VulnerabilityType::Exponential)
        );
    }

    #[test]
    fn test_attack_string_generation() {
        let mut analyzer = RegexAnalyzer::new("(a+)+");
        let result = analyzer.analyze();
        let attack = analyzer.generate_attack_string(&result);
        assert!(!attack.is_empty());
        assert!(attack.starts_with('a'));
        assert!(!attack.ends_with('a')); // Should end with a non-matching char
    }

    #[test]
    fn test_quantified_backreference() {
        let mut analyzer = RegexAnalyzer::new(r"(a+)\1+");
        let result = analyzer.analyze();
        // Should detect the backreference vulnerability
        let has_backref = result
            .constructs
            .iter()
            .any(|c| c.construct_type == "quantified_backreference");
        assert!(has_backref || result.vulnerability_type == Some(VulnerabilityType::Exponential));
    }

    #[test]
    fn test_string_extraction() {
        assert_eq!(extract_string_content("'hello'"), "hello");
        assert_eq!(extract_string_content("\"hello\""), "hello");
        assert_eq!(extract_string_content("r'hello'"), "hello");
        assert_eq!(extract_string_content("\"\"\"hello\"\"\""), "hello");
    }

    #[test]
    fn test_regex_literal_extraction() {
        assert_eq!(extract_regex_literal("/hello/"), "hello");
        assert_eq!(extract_regex_literal("/hello/gi"), "hello");
        assert_eq!(extract_regex_literal("/a\\/b/"), "a\\/b");
    }

    #[test]
    fn test_rust_string_extraction() {
        assert_eq!(extract_rust_string("\"hello\""), "hello");
        assert_eq!(extract_rust_string("r\"hello\""), "hello");
        assert_eq!(extract_rust_string("r#\"hello\"#"), "hello");
    }

    #[test]
    fn test_go_string_extraction() {
        assert_eq!(extract_go_string("\"hello\""), "hello");
        assert_eq!(extract_go_string("`hello`"), "hello");
    }

    #[test]
    fn test_severity_ordering() {
        assert!(Severity::Critical < Severity::High);
        assert!(Severity::High < Severity::Medium);
        assert!(Severity::Medium < Severity::Low);
        assert!(Severity::Low < Severity::Info);
    }

    #[test]
    fn test_evil_regex_email() {
        // Classic evil email regex
        let mut analyzer = RegexAnalyzer::new(r"^([a-zA-Z0-9]+)+@");
        let result = analyzer.analyze();
        assert_eq!(
            result.vulnerability_type,
            Some(VulnerabilityType::Exponential)
        );
    }

    #[test]
    fn test_evil_regex_url() {
        // Evil URL-like pattern
        let mut analyzer = RegexAnalyzer::new(r"^(https?://)?([a-zA-Z0-9]+\.)+");
        let result = analyzer.analyze();
        // This has nested group with + inside followed by +
        assert!(result.vulnerability_type.is_some());
    }

    #[test]
    fn test_word_boundary_safe() {
        let mut analyzer = RegexAnalyzer::new(r"\b\w+\b");
        let result = analyzer.analyze();
        assert_eq!(result.vulnerability_type, None);
    }

    #[test]
    fn test_complex_safe_pattern() {
        // Complex but safe pattern
        let mut analyzer = RegexAnalyzer::new(r"^\d{4}-\d{2}-\d{2}$");
        let result = analyzer.analyze();
        assert_eq!(result.vulnerability_type, None);
    }
}
