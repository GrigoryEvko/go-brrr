# Bundled/Mangled JavaScript Diff System Design

## Executive Summary

This document describes the design for a system that can semantically compare two versions of bundled, minified, and mangled JavaScript files (such as Claude Code releases). The system must handle:

- **20MB+ files** with 50,000+ functions
- **Mangled identifiers** (e.g., `authenticateUser` becomes `a`)
- **No module boundaries** (everything bundled into one file)
- **No whitespace/comments** (fully minified)

The solution uses multi-dimensional fingerprinting, anchor-based matching, and graph propagation to match functions across versions despite identifier mangling.

---

## 1. Problem Analysis

### 1.1 What Mangling Destroys

| Element | Before | After | Status |
|---------|--------|-------|--------|
| Function names | `authenticateUser` | `a` | DESTROYED |
| Variable names | `config` | `b` | DESTROYED |
| Parameter names | `(user, token)` | `(c,d)` | DESTROYED |
| Private method names | `_validate` | `e` | DESTROYED |
| Comments | `// Check auth` | (removed) | DESTROYED |
| Whitespace | Formatted | Single line | DESTROYED |

### 1.2 What Mangling Preserves (Anchor Points)

| Element | Example | Why Preserved |
|---------|---------|---------------|
| String literals | `"Authentication failed"` | Runtime strings |
| Export names | `export { validateToken }` | Public API |
| Property names | `obj.userId` | API contracts |
| Imported names | `require('fs')` | External APIs |
| Numbers | `3600000` (1 hour in ms) | Magic constants |
| Regex patterns | `/^Bearer\s+/` | Pattern matching |
| AST structure | `if-else-return` | Syntax |
| Control flow shape | Loop with 3 branches | Topology |

### 1.3 Scale Considerations

For a 20MB bundled JS file:
- ~500,000 - 1,000,000 lines of code
- ~30,000 - 80,000 functions
- ~100,000+ string literals
- ~1,000,000+ AST nodes

Must complete in < 60 seconds for interactive use.

---

## 2. Architecture Overview

```
                    +-----------------+
                    |   bundle-diff   |
                    +--------+--------+
                             |
        +--------------------+--------------------+
        v                    v                    v
+---------------+    +---------------+    +---------------+
|    Parser     |    |  Fingerprint  |    |   Matcher     |
|   (Phase 1)   |    |   (Phase 2)   |    |   (Phase 3)   |
+---------------+    +---------------+    +---------------+
        |                    |                    |
        v                    v                    v
+---------------+    +---------------+    +---------------+
|  FunctionUnit |    |  Fingerprint  |    |  MatchResult  |
|    Vector     |    |    Vector     |    |    Vector     |
+---------------+    +---------------+    +---------------+
                             |
                    +--------+--------+
                    v                 v
            +---------------+  +---------------+
            |  Diff Engine  |  |   Reporter    |
            |   (Phase 4)   |  |   (Phase 5)   |
            +---------------+  +---------------+
```

---

## 3. Data Structures

### 3.1 Function Unit (Extracted Function Representation)

```rust
/// A single function extracted from a bundled JS file.
/// Contains all information needed for fingerprinting and matching.
#[derive(Debug, Clone)]
pub struct FunctionUnit {
    /// Unique ID within this bundle (ordinal position)
    pub id: u32,

    /// Byte range in source file [start, end)
    pub byte_range: (usize, usize),

    /// Line range [start, end] (1-indexed)
    pub line_range: (usize, usize),

    /// The mangled name (may be single letter like 'a')
    pub mangled_name: String,

    /// Parameter count (survives mangling)
    pub param_count: usize,

    /// Is this an async function?
    pub is_async: bool,

    /// Is this a generator function?
    pub is_generator: bool,

    /// Is this an arrow function?
    pub is_arrow: bool,

    /// Normalized source code (for structural comparison)
    pub normalized_source: String,

    /// CFG topology (see below)
    pub cfg: CFGTopology,

    /// Extracted anchors (strings, numbers, etc.)
    pub anchors: AnchorSet,

    /// Call sites within this function
    pub call_sites: Vec<CallSite>,

    /// Computed fingerprints (lazily populated)
    pub fingerprints: FingerprintSet,
}

/// Represents the control flow graph topology without identifier names
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct CFGTopology {
    /// Number of basic blocks
    pub block_count: u16,

    /// Number of edges
    pub edge_count: u16,

    /// Cyclomatic complexity
    pub complexity: u16,

    /// Block type sequence (Entry, Branch, Loop, Exit, etc.)
    pub block_types: Vec<BlockType>,

    /// Edge type sequence
    pub edge_types: Vec<EdgeType>,

    /// Maximum nesting depth
    pub max_depth: u8,

    /// Has try-catch
    pub has_exception_handling: bool,

    /// Number of loops
    pub loop_count: u8,

    /// Number of branches
    pub branch_count: u8,
}

/// Anchor points that survive mangling
#[derive(Debug, Clone, Default)]
pub struct AnchorSet {
    /// String literals used in this function
    pub strings: Vec<StringAnchor>,

    /// Numeric literals
    pub numbers: Vec<NumberAnchor>,

    /// Regex patterns
    pub regexes: Vec<String>,

    /// Property names accessed (obj.property)
    pub properties: Vec<String>,

    /// Imported/required module names
    pub imports: Vec<String>,

    /// Export names (if this function is exported)
    pub exports: Vec<String>,

    /// Template literal patterns
    pub templates: Vec<TemplateAnchor>,
}

/// A string literal with context
#[derive(Debug, Clone)]
pub struct StringAnchor {
    /// The string value
    pub value: String,

    /// How the string is used
    pub usage: StringUsage,

    /// Frequency within function (for weighting)
    pub count: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringUsage {
    /// throw new Error("...")
    ErrorMessage,
    /// console.log("...")
    LogMessage,
    /// obj["property"]
    PropertyAccess,
    /// fetch("https://...")
    Url,
    /// Regular string
    Generic,
    /// Object key in literal { "key": value }
    ObjectKey,
}

/// Numeric literal with context
#[derive(Debug, Clone)]
pub struct NumberAnchor {
    /// The value (stored as f64 for uniformity)
    pub value: f64,

    /// Is this likely a "magic number"?
    pub is_magic: bool,

    /// Usage context
    pub usage: NumberUsage,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumberUsage {
    /// Array index like arr[0]
    ArrayIndex,
    /// Timeout/delay value
    Timeout,
    /// Buffer size
    BufferSize,
    /// Status code
    StatusCode,
    /// Bitwise operation
    Bitmask,
    /// Generic number
    Generic,
}

/// Template literal structure
#[derive(Debug, Clone)]
pub struct TemplateAnchor {
    /// Static parts of the template
    pub static_parts: Vec<String>,

    /// Number of interpolations
    pub interpolation_count: u8,
}

/// A call site within a function
#[derive(Debug, Clone)]
pub struct CallSite {
    /// Index of called function (if known)
    pub callee_id: Option<u32>,

    /// Mangled callee name
    pub callee_name: String,

    /// Number of arguments
    pub arg_count: u8,

    /// Relative position in function (0.0 - 1.0)
    pub position: f32,

    /// Is this a method call (obj.method())?
    pub is_method_call: bool,

    /// Property name if method call
    pub method_name: Option<String>,
}
```

### 3.2 Fingerprint Set (Multi-Dimensional Signature)

```rust
/// Collection of fingerprints for matching functions across mangled versions.
/// Each fingerprint captures a different aspect of the function that survives mangling.
#[derive(Debug, Clone, Default)]
pub struct FingerprintSet {
    /// Structural fingerprint based on AST shape (ignoring identifiers)
    pub structural: StructuralFingerprint,

    /// CFG topology fingerprint
    pub cfg: CFGFingerprint,

    /// Anchor-based fingerprint (strings, numbers, etc.)
    pub anchor: AnchorFingerprint,

    /// Call pattern fingerprint
    pub call_pattern: CallPatternFingerprint,

    /// Size-based fingerprint
    pub size: SizeFingerprint,

    /// Semantic embedding (optional, expensive)
    pub semantic: Option<Vec<f32>>,
}

/// Structural fingerprint based on normalized AST
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq)]
pub struct StructuralFingerprint {
    /// Hash of AST node type sequence (ignoring identifiers)
    pub ast_shape_hash: u64,

    /// Statement type histogram [assignment, call, return, if, loop, etc.]
    pub statement_histogram: [u16; 16],

    /// Expression type histogram
    pub expression_histogram: [u16; 16],

    /// Maximum AST depth
    pub max_depth: u8,

    /// Total node count
    pub node_count: u32,
}

/// CFG topology fingerprint
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq)]
pub struct CFGFingerprint {
    /// Topology hash (block types + edge types)
    pub topology_hash: u64,

    /// Cyclomatic complexity
    pub complexity: u16,

    /// [blocks, edges, loops, branches, try-catch]
    pub shape_vector: [u8; 8],

    /// Dominance tree depth
    pub dominance_depth: u8,
}

/// Anchor-based fingerprint for matching via preserved strings/numbers
#[derive(Debug, Clone, Default)]
pub struct AnchorFingerprint {
    /// Hash of all string literals (sorted, concatenated)
    pub string_hash: u64,

    /// Hash of error message strings specifically
    pub error_hash: u64,

    /// Hash of property names accessed
    pub property_hash: u64,

    /// Set of "unique" strings (rare across codebase)
    pub unique_strings: Vec<u64>,

    /// Set of significant numbers
    pub significant_numbers: Vec<i64>,

    /// Bloom filter of all anchors (for fast negative matching)
    pub anchor_bloom: [u64; 4],
}

/// Call pattern fingerprint
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq)]
pub struct CallPatternFingerprint {
    /// Total number of calls made
    pub call_count: u16,

    /// Number of unique callees
    pub unique_callee_count: u16,

    /// Call argument count histogram
    pub arg_count_histogram: [u8; 8],

    /// Ratio of method calls to function calls (quantized 0-255)
    pub method_call_ratio: u8,

    /// Pattern of call positions (early/middle/late)
    pub position_pattern: u8,
}

/// Size-based fingerprint
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq)]
pub struct SizeFingerprint {
    /// Byte count (may vary slightly due to different minifiers)
    pub byte_count: u32,

    /// Statement count (more stable)
    pub statement_count: u16,

    /// Expression count
    pub expression_count: u16,

    /// Identifier count (survives mangling, just names change)
    pub identifier_count: u16,

    /// Literal count (strings + numbers + booleans)
    pub literal_count: u16,
}
```

### 3.3 Match Result

```rust
/// Result of matching a function between two versions
#[derive(Debug, Clone)]
pub struct MatchResult {
    /// Function ID in old version
    pub old_id: u32,

    /// Function ID in new version
    pub new_id: u32,

    /// Overall confidence score (0.0 - 1.0)
    pub confidence: f32,

    /// Individual match scores by fingerprint type
    pub scores: MatchScores,

    /// Match classification
    pub match_type: MatchType,
}

#[derive(Debug, Clone, Default)]
pub struct MatchScores {
    pub structural: f32,
    pub cfg: f32,
    pub anchor: f32,
    pub call_pattern: f32,
    pub size: f32,
    pub semantic: Option<f32>,
    pub context: f32, // From graph propagation
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MatchType {
    /// Exact match - all fingerprints identical
    Exact,
    /// High confidence match - multiple fingerprints agree
    HighConfidence,
    /// Medium confidence - some fingerprints agree
    MediumConfidence,
    /// Low confidence - only context/semantic match
    LowConfidence,
    /// Ambiguous - multiple candidates with similar scores
    Ambiguous,
    /// No match found
    Unmatched,
}

/// Represents a difference between matched functions
#[derive(Debug, Clone)]
pub struct FunctionDiff {
    pub match_result: MatchResult,

    /// What changed
    pub changes: Vec<ChangeType>,

    /// Detailed structural diff
    pub structural_diff: Option<StructuralDiff>,

    /// CFG diff
    pub cfg_diff: Option<CFGDiff>,

    /// String changes
    pub string_changes: Vec<StringChange>,
}

#[derive(Debug, Clone)]
pub enum ChangeType {
    /// New code path added
    AddedBranch,
    /// Code path removed
    RemovedBranch,
    /// Loop added
    AddedLoop,
    /// Loop removed
    RemovedLoop,
    /// String literal changed
    StringChanged { old: String, new: String },
    /// Number literal changed
    NumberChanged { old: f64, new: f64 },
    /// Function call added
    CallAdded { callee: String },
    /// Function call removed
    CallRemoved { callee: String },
    /// Async/generator status changed
    AsyncChanged,
    /// Parameter count changed
    ParamCountChanged { old: usize, new: usize },
    /// Size changed significantly
    SizeChanged { old: u32, new: u32 },
    /// Exception handling changed
    ExceptionHandlingChanged,
}
```

---

## 4. Algorithms

### 4.1 Phase 1: Parsing and Extraction

```
ALGORITHM ExtractFunctions(source: &[u8]) -> Vec<FunctionUnit>

INPUT: Minified JavaScript source bytes
OUTPUT: Vector of extracted function units

1. Parse source using tree-sitter JavaScript/TypeScript grammar
2. Create empty function list
3. Walk AST in pre-order:
   FOR each node in AST:
       IF node is function_declaration OR arrow_function OR method_definition:
           unit = ExtractFunctionUnit(node, source)
           functions.push(unit)
4. Post-process: resolve internal call targets
   FOR each function in functions:
       FOR each call_site in function.call_sites:
           callee_id = FindCalleeByName(call_site.callee_name, functions)
           call_site.callee_id = callee_id
5. RETURN functions

SUBROUTINE ExtractFunctionUnit(node: Node, source: &[u8]) -> FunctionUnit
    unit = FunctionUnit::new()
    unit.byte_range = (node.start_byte(), node.end_byte())
    unit.line_range = (node.start_line() + 1, node.end_line() + 1)
    unit.mangled_name = extract_name(node)
    unit.param_count = count_params(node)
    unit.is_async = has_async_keyword(node)
    unit.is_generator = has_generator_star(node)
    unit.is_arrow = node.kind() == "arrow_function"

    // Build normalized AST (identifiers replaced with placeholders)
    unit.normalized_source = normalize_ast(node, source)

    // Build CFG
    unit.cfg = build_cfg_topology(node, source)

    // Extract anchors
    unit.anchors = extract_anchors(node, source)

    // Extract call sites
    unit.call_sites = extract_call_sites(node, source)

    RETURN unit
```

### 4.2 Phase 2: Fingerprint Computation

```
ALGORITHM ComputeFingerprints(functions: &mut Vec<FunctionUnit>, global_stats: &GlobalStats)

INPUT: Vector of function units, global statistics for weighting
OUTPUT: Populates fingerprint fields on each function

PARALLEL FOR each function in functions:
    // Structural fingerprint
    function.fingerprints.structural = ComputeStructuralFingerprint(function)

    // CFG fingerprint
    function.fingerprints.cfg = ComputeCFGFingerprint(function.cfg)

    // Anchor fingerprint (with global stats for uniqueness weighting)
    function.fingerprints.anchor = ComputeAnchorFingerprint(function.anchors, global_stats)

    // Call pattern fingerprint
    function.fingerprints.call_pattern = ComputeCallPatternFingerprint(function.call_sites)

    // Size fingerprint
    function.fingerprints.size = ComputeSizeFingerprint(function)

SUBROUTINE ComputeStructuralFingerprint(function: &FunctionUnit) -> StructuralFingerprint
    // Parse normalized source to get AST without identifiers
    nodes = parse_normalized(function.normalized_source)

    // Build node type sequence
    type_sequence = []
    histogram = [0; 16]

    FOR node in depth_first_traversal(nodes):
        type_sequence.push(node.type_id)
        histogram[classify_node(node)] += 1

    RETURN StructuralFingerprint {
        ast_shape_hash: hash(type_sequence),
        statement_histogram: histogram,
        expression_histogram: compute_expr_histogram(nodes),
        max_depth: compute_max_depth(nodes),
        node_count: nodes.len(),
    }

SUBROUTINE ComputeAnchorFingerprint(anchors: &AnchorSet, global: &GlobalStats) -> AnchorFingerprint
    // Sort strings for consistent hashing
    sorted_strings = anchors.strings.sorted_by(|s| s.value)

    // Identify "unique" strings (appear in < 3 functions globally)
    unique_strings = []
    FOR string in sorted_strings:
        IF global.string_frequency(string.value) < 3:
            unique_strings.push(hash(string.value))

    // Compute bloom filter for fast negative matching
    bloom = [0u64; 4]
    FOR anchor in all_anchors(anchors):
        bloom_insert(bloom, hash(anchor))

    RETURN AnchorFingerprint {
        string_hash: hash(concat(sorted_strings)),
        error_hash: hash(filter_errors(sorted_strings)),
        property_hash: hash(anchors.properties.sorted()),
        unique_strings,
        significant_numbers: filter_significant(anchors.numbers),
        anchor_bloom: bloom,
    }
```

### 4.3 Phase 3: Multi-Phase Matching Algorithm

```
ALGORITHM MatchFunctions(old: &[FunctionUnit], new: &[FunctionUnit]) -> Vec<MatchResult>

INPUT: Functions from old and new versions
OUTPUT: Match results with confidence scores

// Phase 1: Exact structural matches (highest confidence)
exact_matches = []
FOR old_fn in old:
    FOR new_fn in new:
        IF old_fn.fingerprints.structural == new_fn.fingerprints.structural:
            IF old_fn.fingerprints.cfg == new_fn.fingerprints.cfg:
                IF old_fn.fingerprints.anchor == new_fn.fingerprints.anchor:
                    exact_matches.push(MatchResult {
                        old_id: old_fn.id,
                        new_id: new_fn.id,
                        confidence: 1.0,
                        match_type: MatchType::Exact,
                    })
                    MARK old_fn, new_fn as matched

// Phase 2: Anchor-based matching (unique strings/errors)
anchor_matches = []
unmatched_old = filter_unmatched(old)
unmatched_new = filter_unmatched(new)

FOR old_fn in unmatched_old:
    IF old_fn.fingerprints.anchor.unique_strings.is_not_empty():
        candidates = []
        FOR new_fn in unmatched_new:
            // Bloom filter for fast negative check
            IF NOT bloom_disjoint(old_fn.anchor_bloom, new_fn.anchor_bloom):
                overlap = jaccard_similarity(
                    old_fn.unique_strings,
                    new_fn.unique_strings
                )
                IF overlap > 0.5:
                    candidates.push((new_fn, overlap))

        IF candidates.len() == 1:
            // Unique match
            anchor_matches.push(MatchResult {
                old_id: old_fn.id,
                new_id: candidates[0].0.id,
                confidence: 0.9 * candidates[0].1,
                match_type: MatchType::HighConfidence,
            })
            MARK as matched

// Phase 3: Structural + CFG matching
structural_matches = []
unmatched_old = filter_unmatched(old)
unmatched_new = filter_unmatched(new)

FOR old_fn in unmatched_old:
    candidates = []
    FOR new_fn in unmatched_new:
        score = ComputeMatchScore(old_fn, new_fn)
        IF score > 0.7:
            candidates.push((new_fn, score))

    candidates.sort_by_score_desc()
    IF candidates.len() > 0:
        best = candidates[0]
        second_best = candidates.get(1)

        // Check for ambiguity
        IF second_best.is_none() OR best.score - second_best.score > 0.1:
            structural_matches.push(MatchResult {
                old_id: old_fn.id,
                new_id: best.0.id,
                confidence: best.1,
                match_type: classify_confidence(best.1),
            })
            MARK as matched

// Phase 4: Context propagation (use call graph structure)
REPEAT:
    new_matches = PropagateMatches(matches, old, new)
    IF new_matches.is_empty():
        BREAK
    matches.extend(new_matches)

// Phase 5: Semantic matching (embedding similarity) for remaining
IF semantic_enabled:
    semantic_matches = SemanticMatch(filter_unmatched(old), filter_unmatched(new))
    matches.extend(semantic_matches)

// Phase 6: Low confidence fuzzy matching for remaining
fuzzy_matches = FuzzyMatch(filter_unmatched(old), filter_unmatched(new))
matches.extend(fuzzy_matches)

RETURN matches

SUBROUTINE ComputeMatchScore(old: &FunctionUnit, new: &FunctionUnit) -> f32
    scores = MatchScores::default()

    // Structural similarity (0.0 - 1.0)
    scores.structural = structural_similarity(
        old.fingerprints.structural,
        new.fingerprints.structural
    )

    // CFG similarity
    scores.cfg = cfg_similarity(
        old.fingerprints.cfg,
        new.fingerprints.cfg
    )

    // Anchor similarity (Jaccard with weighting)
    scores.anchor = anchor_similarity(
        old.fingerprints.anchor,
        new.fingerprints.anchor
    )

    // Call pattern similarity
    scores.call_pattern = call_pattern_similarity(
        old.fingerprints.call_pattern,
        new.fingerprints.call_pattern
    )

    // Size similarity (with tolerance for minifier differences)
    scores.size = size_similarity(
        old.fingerprints.size,
        new.fingerprints.size
    )

    // Weighted combination
    weights = [0.25, 0.20, 0.25, 0.15, 0.15]  // structural, cfg, anchor, call, size
    RETURN weighted_average(scores, weights)

SUBROUTINE PropagateMatches(matches: &[MatchResult], old: &[FunctionUnit], new: &[FunctionUnit]) -> Vec<MatchResult>
    // Build call graphs
    old_cg = build_call_graph(old)
    new_cg = build_call_graph(new)

    new_matches = []

    // For each unmatched function in old
    FOR old_fn in filter_unmatched(old):
        // Find matched callers and callees
        matched_callers = []
        FOR caller in old_cg.callers_of(old_fn.id):
            IF has_match(caller):
                matched_callers.push(get_match(caller))

        matched_callees = []
        FOR callee in old_cg.callees_of(old_fn.id):
            IF has_match(callee):
                matched_callees.push(get_match(callee))

        // Find candidates in new that have same matched neighbors
        candidates = []
        FOR new_fn in filter_unmatched(new):
            new_callers = new_cg.callers_of(new_fn.id)
            new_callees = new_cg.callees_of(new_fn.id)

            // Count how many neighbors match
            caller_overlap = count_overlap(
                matched_callers.map(|m| m.new_id),
                new_callers
            )
            callee_overlap = count_overlap(
                matched_callees.map(|m| m.new_id),
                new_callees
            )

            IF caller_overlap + callee_overlap > 0:
                // Boost with structural similarity
                base_score = ComputeMatchScore(old_fn, new_fn)
                context_boost = (caller_overlap + callee_overlap) as f32 /
                               (matched_callers.len() + matched_callees.len()) as f32

                combined = base_score * 0.7 + context_boost * 0.3
                IF combined > 0.6:
                    candidates.push((new_fn, combined))

        IF candidates.len() == 1:
            new_matches.push(...)

    RETURN new_matches
```

### 4.4 Phase 4: Diff Generation

```
ALGORITHM GenerateDiff(matches: &[MatchResult], old: &[FunctionUnit], new: &[FunctionUnit]) -> BundleDiff

INPUT: Match results and function units from both versions
OUTPUT: Complete diff structure

diff = BundleDiff::new()

// Categorize functions
diff.added = []
diff.removed = []
diff.modified = []
diff.unchanged = []

// Find added functions (in new but not matched)
FOR new_fn in new:
    IF NOT is_matched(new_fn.id, matches):
        diff.added.push(AddedFunction {
            function: new_fn.clone(),
            probable_source: infer_source(new_fn, old),  // Might be split/renamed
        })

// Find removed functions (in old but not matched)
FOR old_fn in old:
    IF NOT is_matched(old_fn.id, matches):
        diff.removed.push(RemovedFunction {
            function: old_fn.clone(),
            probable_fate: infer_fate(old_fn, new),  // Might be merged/inlined
        })

// Generate detailed diffs for modified functions
FOR match in matches:
    old_fn = old[match.old_id]
    new_fn = new[match.new_id]

    IF match.match_type != MatchType::Exact:
        func_diff = GenerateFunctionDiff(old_fn, new_fn)
        IF func_diff.changes.is_not_empty():
            diff.modified.push(func_diff)
        ELSE:
            diff.unchanged.push(match)
    ELSE:
        diff.unchanged.push(match)

// Compute summary statistics
diff.summary = ComputeSummary(diff)

RETURN diff

SUBROUTINE GenerateFunctionDiff(old: &FunctionUnit, new: &FunctionUnit) -> FunctionDiff
    changes = []

    // Compare CFG structure
    IF old.cfg.branch_count != new.cfg.branch_count:
        IF new.cfg.branch_count > old.cfg.branch_count:
            changes.push(ChangeType::AddedBranch)
        ELSE:
            changes.push(ChangeType::RemovedBranch)

    IF old.cfg.loop_count != new.cfg.loop_count:
        IF new.cfg.loop_count > old.cfg.loop_count:
            changes.push(ChangeType::AddedLoop)
        ELSE:
            changes.push(ChangeType::RemovedLoop)

    // Compare strings
    old_strings = set(old.anchors.strings.map(|s| s.value))
    new_strings = set(new.anchors.strings.map(|s| s.value))

    FOR removed in old_strings - new_strings:
        FOR added in new_strings - old_strings:
            IF levenshtein_similarity(removed, added) > 0.8:
                changes.push(ChangeType::StringChanged { old: removed, new: added })

    // Compare calls
    old_calls = set(old.call_sites.map(|c| c.callee_name))
    new_calls = set(new.call_sites.map(|c| c.callee_name))

    FOR added in new_calls - old_calls:
        changes.push(ChangeType::CallAdded { callee: added })
    FOR removed in old_calls - new_calls:
        changes.push(ChangeType::CallRemoved { callee: removed })

    // Compare sizes
    IF abs(old.byte_count - new.byte_count) > old.byte_count * 0.2:
        changes.push(ChangeType::SizeChanged {
            old: old.byte_count,
            new: new.byte_count
        })

    RETURN FunctionDiff {
        match_result: ...,
        changes,
        structural_diff: compute_structural_diff(old, new),
        cfg_diff: compute_cfg_diff(old.cfg, new.cfg),
        string_changes: compute_string_changes(old.anchors, new.anchors),
    }
```

---

## 5. Similarity Functions

### 5.1 Structural Similarity

```rust
fn structural_similarity(a: &StructuralFingerprint, b: &StructuralFingerprint) -> f32 {
    // If exact hash match, perfect score
    if a.ast_shape_hash == b.ast_shape_hash {
        return 1.0;
    }

    // Otherwise compute histogram similarity
    let hist_sim = histogram_cosine_similarity(
        &a.statement_histogram,
        &b.statement_histogram
    );

    let expr_sim = histogram_cosine_similarity(
        &a.expression_histogram,
        &b.expression_histogram
    );

    // Node count ratio (penalize large differences)
    let count_ratio = f32::min(a.node_count, b.node_count) as f32 /
                      f32::max(a.node_count, b.node_count) as f32;

    // Depth similarity
    let depth_diff = (a.max_depth as i32 - b.max_depth as i32).abs();
    let depth_sim = 1.0 / (1.0 + depth_diff as f32 * 0.2);

    // Weighted combination
    hist_sim * 0.4 + expr_sim * 0.3 + count_ratio * 0.2 + depth_sim * 0.1
}

fn histogram_cosine_similarity(a: &[u16], b: &[u16]) -> f32 {
    let dot: f32 = a.iter().zip(b.iter())
        .map(|(x, y)| (*x as f32) * (*y as f32))
        .sum();

    let mag_a: f32 = a.iter().map(|x| (*x as f32).powi(2)).sum::<f32>().sqrt();
    let mag_b: f32 = b.iter().map(|x| (*x as f32).powi(2)).sum::<f32>().sqrt();

    if mag_a == 0.0 || mag_b == 0.0 {
        return 0.0;
    }

    dot / (mag_a * mag_b)
}
```

### 5.2 CFG Similarity

```rust
fn cfg_similarity(a: &CFGFingerprint, b: &CFGFingerprint) -> f32 {
    // If exact topology hash match
    if a.topology_hash == b.topology_hash {
        return 1.0;
    }

    // Compare shape vectors
    let shape_diff: u32 = a.shape_vector.iter().zip(b.shape_vector.iter())
        .map(|(x, y)| (*x as i32 - *y as i32).unsigned_abs())
        .sum();

    let max_shape: u32 = a.shape_vector.iter().chain(b.shape_vector.iter())
        .map(|x| *x as u32)
        .sum();

    let shape_sim = if max_shape == 0 {
        1.0
    } else {
        1.0 - (shape_diff as f32 / max_shape as f32).min(1.0)
    };

    // Complexity similarity
    let complexity_ratio = f32::min(a.complexity, b.complexity) as f32 /
                          f32::max(a.complexity, b.complexity).max(1) as f32;

    shape_sim * 0.7 + complexity_ratio * 0.3
}
```

### 5.3 Anchor Similarity

```rust
fn anchor_similarity(a: &AnchorFingerprint, b: &AnchorFingerprint) -> f32 {
    // Fast negative check using bloom filter
    if bloom_disjoint(&a.anchor_bloom, &b.anchor_bloom) {
        return 0.0;
    }

    // Unique strings Jaccard similarity (heavily weighted - these are discriminative)
    let unique_jaccard = if a.unique_strings.is_empty() && b.unique_strings.is_empty() {
        0.5  // No unique strings, neutral score
    } else {
        jaccard_similarity(&a.unique_strings, &b.unique_strings)
    };

    // Error message similarity (very discriminative)
    let error_match = if a.error_hash == b.error_hash { 1.0 } else { 0.0 };

    // Property names similarity
    let property_match = if a.property_hash == b.property_hash { 1.0 } else { 0.0 };

    // Significant numbers overlap
    let number_jaccard = jaccard_similarity(&a.significant_numbers, &b.significant_numbers);

    // Weighted combination
    unique_jaccard * 0.4 + error_match * 0.3 + property_match * 0.2 + number_jaccard * 0.1
}

fn bloom_disjoint(a: &[u64; 4], b: &[u64; 4]) -> bool {
    // If ANDing produces all zeros, they share no elements
    for i in 0..4 {
        if a[i] & b[i] != 0 {
            return false;
        }
    }
    true
}

fn jaccard_similarity<T: Eq + std::hash::Hash>(a: &[T], b: &[T]) -> f32 {
    let set_a: std::collections::HashSet<&T> = a.iter().collect();
    let set_b: std::collections::HashSet<&T> = b.iter().collect();

    let intersection = set_a.intersection(&set_b).count();
    let union = set_a.union(&set_b).count();

    if union == 0 {
        return 1.0;  // Both empty
    }

    intersection as f32 / union as f32
}
```

---

## 6. Performance Optimizations

### 6.1 Indexing for Fast Candidate Lookup

```rust
/// Index for fast candidate lookup during matching
pub struct MatchIndex {
    /// Exact structural hash -> function IDs
    structural_exact: HashMap<u64, Vec<u32>>,

    /// Complexity bucket -> function IDs
    complexity_bucket: HashMap<u8, Vec<u32>>,

    /// Unique string hash -> function IDs
    unique_string_index: HashMap<u64, Vec<u32>>,

    /// Error hash -> function IDs
    error_hash_index: HashMap<u64, Vec<u32>>,

    /// LSH buckets for structural fingerprints
    structural_lsh: LSHIndex,

    /// LSH buckets for anchor fingerprints
    anchor_lsh: LSHIndex,
}

impl MatchIndex {
    /// Build index from function units
    pub fn build(functions: &[FunctionUnit]) -> Self {
        let mut index = Self::new();

        for func in functions {
            let id = func.id;
            let fp = &func.fingerprints;

            // Exact structural hash
            index.structural_exact
                .entry(fp.structural.ast_shape_hash)
                .or_default()
                .push(id);

            // Complexity bucket (quantize to reduce buckets)
            let complexity_bucket = (fp.cfg.complexity / 5).min(20) as u8;
            index.complexity_bucket
                .entry(complexity_bucket)
                .or_default()
                .push(id);

            // Unique strings
            for hash in &fp.anchor.unique_strings {
                index.unique_string_index
                    .entry(*hash)
                    .or_default()
                    .push(id);
            }

            // Error hash
            index.error_hash_index
                .entry(fp.anchor.error_hash)
                .or_default()
                .push(id);

            // LSH for approximate matching
            index.structural_lsh.insert(id, &fp.structural);
            index.anchor_lsh.insert(id, &fp.anchor);
        }

        index
    }

    /// Find candidates for matching a function
    pub fn find_candidates(&self, func: &FunctionUnit) -> Vec<u32> {
        let fp = &func.fingerprints;
        let mut candidates = HashSet::new();

        // Exact structural matches
        if let Some(ids) = self.structural_exact.get(&fp.structural.ast_shape_hash) {
            candidates.extend(ids);
        }

        // Same complexity bucket +/- 1
        let bucket = (fp.cfg.complexity / 5).min(20) as u8;
        for b in bucket.saturating_sub(1)..=bucket.saturating_add(1) {
            if let Some(ids) = self.complexity_bucket.get(&b) {
                candidates.extend(ids);
            }
        }

        // Unique string matches
        for hash in &fp.anchor.unique_strings {
            if let Some(ids) = self.unique_string_index.get(hash) {
                candidates.extend(ids);
            }
        }

        // Error hash match
        if let Some(ids) = self.error_hash_index.get(&fp.anchor.error_hash) {
            candidates.extend(ids);
        }

        // LSH approximate matches
        candidates.extend(self.structural_lsh.query(&fp.structural, 10));
        candidates.extend(self.anchor_lsh.query(&fp.anchor, 10));

        candidates.into_iter().collect()
    }
}
```

### 6.2 Parallel Processing

```rust
use rayon::prelude::*;

/// Parallel fingerprint computation
pub fn compute_fingerprints_parallel(
    functions: &mut [FunctionUnit],
    global_stats: &GlobalStats,
) {
    functions.par_iter_mut().for_each(|func| {
        func.fingerprints = FingerprintSet {
            structural: compute_structural_fingerprint(func),
            cfg: compute_cfg_fingerprint(&func.cfg),
            anchor: compute_anchor_fingerprint(&func.anchors, global_stats),
            call_pattern: compute_call_pattern_fingerprint(&func.call_sites),
            size: compute_size_fingerprint(func),
            semantic: None,  // Computed separately if needed
        };
    });
}

/// Parallel matching with work stealing
pub fn match_parallel(
    old: &[FunctionUnit],
    new_index: &MatchIndex,
    new: &[FunctionUnit],
) -> Vec<MatchResult> {
    let matches: Vec<MatchResult> = old.par_iter()
        .filter_map(|old_func| {
            let candidates = new_index.find_candidates(old_func);

            let mut best_match: Option<(u32, f32)> = None;
            let mut second_best_score = 0.0;

            for &new_id in &candidates {
                let new_func = &new[new_id as usize];
                let score = compute_match_score(old_func, new_func);

                if let Some((_, best_score)) = best_match {
                    if score > best_score {
                        second_best_score = best_score;
                        best_match = Some((new_id, score));
                    } else if score > second_best_score {
                        second_best_score = score;
                    }
                } else if score > 0.5 {
                    best_match = Some((new_id, score));
                }
            }

            // Require clear winner (avoid ambiguous matches)
            best_match.and_then(|(new_id, score)| {
                if score - second_best_score > 0.1 {
                    Some(MatchResult {
                        old_id: old_func.id,
                        new_id,
                        confidence: score,
                        match_type: classify_confidence(score),
                        scores: Default::default(),  // Fill in later
                    })
                } else {
                    None
                }
            })
        })
        .collect();

    // Resolve conflicts (multiple old functions matched to same new function)
    resolve_conflicts(matches)
}
```

### 6.3 Memory Efficiency

```rust
/// Streaming parser for large files
pub struct StreamingParser {
    chunk_size: usize,
    overlap: usize,
}

impl StreamingParser {
    /// Parse functions incrementally to avoid loading entire AST
    pub fn parse_streaming<'a>(
        &self,
        source: &'a [u8],
    ) -> impl Iterator<Item = FunctionUnit> + 'a {
        // Find function boundaries first (lightweight scan)
        let boundaries = find_function_boundaries(source);

        boundaries.into_iter().map(move |(start, end)| {
            // Parse only this function's slice
            let chunk = &source[start..end];
            parse_single_function(chunk, start)
        })
    }
}

/// Compact fingerprint storage for large-scale matching
#[repr(C, packed)]
pub struct CompactFingerprint {
    structural_hash: u64,
    cfg_hash: u64,
    anchor_bloom: [u64; 4],
    complexity: u16,
    node_count: u16,
    size: u32,
}

impl CompactFingerprint {
    /// 48 bytes per function - for 80K functions, ~4MB total
    pub const SIZE: usize = std::mem::size_of::<Self>();
}
```

---

## 7. Output Formats

### 7.1 Human-Readable Summary

```
Bundle Diff: old.js -> new.js
================================================================================

Summary:
  - Total functions (old): 45,231
  - Total functions (new): 46,892
  - Matched: 44,120 (97.5%)
  - Added: 2,772 (5.9% of new)
  - Removed: 1,111 (2.5% of old)
  - Modified: 3,456 (7.8% of matched)
  - Unchanged: 40,664 (92.2% of matched)

High-Impact Changes:
  1. [MODIFIED] Function at new:1234 (was old:1122)
     - Added 2 new branches (error handling)
     - Changed error message: "Auth failed" -> "Authentication failed: {reason}"
     - Added call to validateToken()
     Match confidence: 0.92

  2. [ADDED] Function at new:5678
     - Probable source: Split from old:4567
     - Contains unique string: "rate_limit_exceeded"
     - Complexity: 8 (moderate)

  3. [REMOVED] Function at old:9012
     - Probable fate: Inlined into old:9000
     - Was called by: 3 functions
     - Contained: "deprecated_api" string

Size Changes:
  - Old bundle: 18,432,100 bytes
  - New bundle: 19,567,200 bytes
  - Delta: +1,135,100 bytes (+6.2%)

  Largest growth areas:
    - Authentication module: +234KB (estimated)
    - Error handling: +156KB (estimated)
```

### 7.2 JSON Output

```json
{
  "version": "1.0",
  "old_file": "claude-code-1.0.0.js",
  "new_file": "claude-code-1.1.0.js",
  "timestamp": "2024-01-15T10:30:00Z",
  "summary": {
    "old_function_count": 45231,
    "new_function_count": 46892,
    "matched_count": 44120,
    "added_count": 2772,
    "removed_count": 1111,
    "modified_count": 3456,
    "unchanged_count": 40664,
    "match_rate": 0.975,
    "old_size_bytes": 18432100,
    "new_size_bytes": 19567200
  },
  "matches": [
    {
      "old_id": 1122,
      "new_id": 1234,
      "confidence": 0.92,
      "match_type": "high_confidence",
      "scores": {
        "structural": 0.95,
        "cfg": 0.88,
        "anchor": 0.91,
        "call_pattern": 0.85,
        "size": 0.94
      },
      "changes": [
        {"type": "added_branch", "count": 2},
        {"type": "string_changed", "old": "Auth failed", "new": "Authentication failed: {reason}"},
        {"type": "call_added", "callee": "validateToken"}
      ]
    }
  ],
  "added": [
    {
      "new_id": 5678,
      "byte_range": [123456, 124567],
      "probable_source": {"old_id": 4567, "confidence": 0.65, "reason": "split"},
      "anchors": {
        "unique_strings": ["rate_limit_exceeded"],
        "complexity": 8
      }
    }
  ],
  "removed": [
    {
      "old_id": 9012,
      "byte_range": [234567, 235678],
      "probable_fate": {"new_id": 9000, "confidence": 0.72, "reason": "inlined"},
      "call_count": 3,
      "anchors": {
        "strings": ["deprecated_api"]
      }
    }
  ]
}
```

### 7.3 HTML Report

Interactive HTML with:
- Collapsible sections for added/removed/modified
- Side-by-side diff view for modified functions
- CFG visualization (using Mermaid)
- Search/filter by string, function size, change type
- Statistics charts

---

## 8. CLI Interface

```
USAGE:
    tldr bundle-diff <OLD> <NEW> [OPTIONS]

ARGS:
    <OLD>    Path to old bundle file
    <NEW>    Path to new bundle file

OPTIONS:
    -f, --format <FORMAT>
            Output format [default: text]
            [possible values: text, json, html]

    -o, --output <FILE>
            Write output to file instead of stdout

    --threshold <SCORE>
            Minimum match confidence threshold [default: 0.7]

    --function <NAME>
            Show diff for specific function (by string content or index)

    --show-matched
            Include unchanged matched functions in output

    --show-unmatched
            Show details of unmatched functions

    --semantic
            Enable semantic matching (requires embedding model)

    --parallel <N>
            Number of parallel workers [default: num_cpus]

    --progress
            Show progress bar during analysis

    --cache <DIR>
            Cache directory for intermediate results

    -v, --verbose
            Increase verbosity (can be repeated)

EXAMPLES:
    # Basic comparison
    tldr bundle-diff old.js new.js

    # JSON output with semantic matching
    tldr bundle-diff old.js new.js -f json --semantic -o diff.json

    # Focus on specific function
    tldr bundle-diff old.js new.js --function "Authentication failed"

    # Show all matches including unchanged
    tldr bundle-diff old.js new.js --show-matched --format html -o report.html
```

---

## 9. Edge Cases and Error Handling

### 9.1 Problematic Patterns

| Pattern | Problem | Mitigation |
|---------|---------|------------|
| Eval/Function constructor | Dynamic code not in AST | Mark as "dynamic", exclude from analysis |
| Heavily inlined code | Many functions disappear | Detect inline patterns, track content movement |
| Split functions | One function becomes many | Track common anchors, note probable splits |
| Merged functions | Many functions become one | Track anchor aggregation |
| Complete rewrites | No structural similarity | Fall back to semantic matching |
| Different minifiers | Slightly different output | Use minifier-agnostic metrics |
| Source maps present | Can deminify | Use source maps when available |

### 9.2 Error Recovery

```rust
/// Robust parsing with error recovery
pub fn parse_with_recovery(source: &[u8]) -> ParseResult {
    match parse_javascript(source) {
        Ok(ast) => ParseResult::Success(ast),
        Err(e) => {
            // Try recovery strategies

            // 1. Remove problematic constructs
            let cleaned = remove_eval_constructs(source);
            if let Ok(ast) = parse_javascript(&cleaned) {
                return ParseResult::PartialSuccess {
                    ast,
                    warnings: vec![format!("Removed eval constructs: {}", e)],
                };
            }

            // 2. Parse in chunks
            let chunks = split_at_function_boundaries(source);
            let mut functions = Vec::new();
            let mut errors = Vec::new();

            for chunk in chunks {
                match parse_function_chunk(&chunk) {
                    Ok(func) => functions.push(func),
                    Err(e) => errors.push(e),
                }
            }

            if !functions.is_empty() {
                ParseResult::PartialSuccess {
                    ast: construct_partial_ast(functions),
                    warnings: errors.iter().map(|e| e.to_string()).collect(),
                }
            } else {
                ParseResult::Failure(e)
            }
        }
    }
}
```

---

## 10. Testing Strategy

### 10.1 Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fingerprint_identical_functions() {
        let source = "function foo(a, b) { return a + b; }";
        let func1 = parse_function(source);
        let func2 = parse_function(source);

        let fp1 = compute_fingerprints(&func1);
        let fp2 = compute_fingerprints(&func2);

        assert_eq!(fp1.structural, fp2.structural);
        assert_eq!(fp1.cfg, fp2.cfg);
        assert_eq!(fp1.anchor, fp2.anchor);
    }

    #[test]
    fn test_fingerprint_survives_mangling() {
        let original = "function authenticate(user, token) {
            if (!token) throw new Error('No token');
            return validate(user, token);
        }";

        let mangled = "function a(b,c){if(!c)throw new Error('No token');return d(b,c)}";

        let fp1 = compute_fingerprints(&parse_function(original));
        let fp2 = compute_fingerprints(&parse_function(mangled));

        // Structural should match
        assert!(structural_similarity(&fp1.structural, &fp2.structural) > 0.9);

        // CFG should match
        assert!(cfg_similarity(&fp1.cfg, &fp2.cfg) > 0.95);

        // Anchors should match (error string preserved)
        assert!(anchor_similarity(&fp1.anchor, &fp2.anchor) > 0.8);
    }

    #[test]
    fn test_match_modified_function() {
        let old = "function a(b){if(b>0)return 1;return 0}";
        let new = "function a(b){if(b>0){console.log('positive');return 1}return 0}";

        let old_fp = compute_fingerprints(&parse_function(old));
        let new_fp = compute_fingerprints(&parse_function(new));

        let score = compute_match_score_from_fps(&old_fp, &new_fp);

        // Should match with high confidence despite change
        assert!(score > 0.7);
        assert!(score < 1.0);  // Not exact match
    }
}
```

### 10.2 Integration Tests

```rust
#[test]
fn test_real_bundle_diff() {
    // Use actual Claude Code bundles (anonymized/subset)
    let old_bundle = include_bytes!("fixtures/bundle_v1.js");
    let new_bundle = include_bytes!("fixtures/bundle_v2.js");

    let result = bundle_diff(old_bundle, new_bundle, &DiffOptions::default());

    // Should complete in reasonable time
    assert!(result.elapsed < Duration::from_secs(60));

    // Should find high match rate for similar versions
    assert!(result.summary.match_rate > 0.9);

    // Verify known changes are detected
    assert!(result.modified.iter().any(|d|
        d.changes.iter().any(|c| matches!(c, ChangeType::StringChanged { .. }))
    ));
}
```

### 10.3 Fuzzing

```rust
#[test]
fn fuzz_parser() {
    // Generate random JS-like strings
    for _ in 0..10000 {
        let random_js = generate_random_js();
        // Should not panic
        let _ = parse_with_recovery(random_js.as_bytes());
    }
}

#[test]
fn fuzz_fingerprinting() {
    // Generate valid ASTs with random structure
    for _ in 0..1000 {
        let ast = generate_random_ast();
        let func = FunctionUnit::from_ast(ast);
        // Should not panic
        let _ = compute_fingerprints(&func);
    }
}
```

---

## 11. Future Enhancements

1. **Source Map Integration**: When source maps are available, demangle before comparison for better accuracy.

2. **Semantic Diffing**: Use LLM to explain what changed in natural language ("Added rate limiting to authentication").

3. **Security Analysis**: Flag suspicious changes (removed validation, added eval, etc.).

4. **Regression Detection**: Track metrics over time, alert on unexpected changes.

5. **Interactive Explorer**: Web UI for exploring diffs with search and filtering.

6. **Multi-Version Tracking**: Track function evolution across many versions.

7. **Call Graph Visualization**: Show how call relationships changed between versions.

---

## 12. Implementation Phases

### Phase 1: Core Infrastructure (Week 1-2)
- [ ] Function extraction from minified JS
- [ ] Basic fingerprint computation
- [ ] Exact matching

### Phase 2: Advanced Matching (Week 3-4)
- [ ] Multi-phase matching algorithm
- [ ] Context propagation
- [ ] Conflict resolution

### Phase 3: Diff Generation (Week 5)
- [ ] Detailed function-level diffs
- [ ] Output formatters (text, JSON, HTML)
- [ ] CLI interface

### Phase 4: Optimization (Week 6)
- [ ] Parallel processing
- [ ] Indexing and LSH
- [ ] Memory optimization

### Phase 5: Testing & Polish (Week 7-8)
- [ ] Comprehensive test suite
- [ ] Performance benchmarks
- [ ] Documentation

---

## Appendix A: AST Normalization Rules

For structural fingerprinting, identifiers are normalized:

```javascript
// Original
function authenticateUser(user, token) {
    const result = validate(user);
    if (result.valid) {
        return createSession(user, token);
    }
    throw new Error("Authentication failed");
}

// Normalized (identifiers replaced with positional placeholders)
function $_F0($_P0, $_P1) {
    const $_V0 = $_C0($_P0);
    if ($_V0.$_M0) {
        return $_C1($_P0, $_P1);
    }
    throw new Error("Authentication failed");  // Strings preserved!
}
```

Normalization rules:
1. Function name -> `$_F{index}`
2. Parameters -> `$_P{index}` (in order)
3. Local variables -> `$_V{index}` (in order of first appearance)
4. Called functions -> `$_C{index}` (in order of first call)
5. Member access -> `$_M{index}` (in order)
6. String literals -> PRESERVED
7. Number literals -> PRESERVED
8. Operators -> PRESERVED
9. Keywords -> PRESERVED

---

## Appendix B: CFG Topology Encoding

```
Block Types (4 bits each):
  0 = Entry
  1 = Exit
  2 = Body
  3 = Branch (if/switch)
  4 = LoopHeader
  5 = LoopBody
  6 = Return
  7 = Exception
  8 = Finally
  9-15 = Reserved

Edge Types (4 bits each):
  0 = Unconditional
  1 = True
  2 = False
  3 = BackEdge
  4 = Break
  5 = Continue
  6 = Exception
  7 = Return
  8-15 = Reserved

Topology Hash:
  hash = fnv1a_64(
    concat(
      encode_blocks(block_types),  // Pack 4 bits per block
      encode_edges(edge_types),    // Pack 4 bits per edge
      [complexity, max_depth, loop_count, branch_count]
    )
  )
```

---

## Appendix C: Bloom Filter Parameters

For anchor bloom filter:

```
Size: 256 bits (4 x u64)
Hash functions: 3 (optimal for ~50 elements)
Expected false positive rate: ~2.5%

Insert(item):
  h1 = fnv1a_64(item)
  h2 = xxhash64(item)
  for i in 0..3:
    bit = (h1 + i * h2) % 256
    filter[bit / 64] |= 1 << (bit % 64)

Query(item):
  h1 = fnv1a_64(item)
  h2 = xxhash64(item)
  for i in 0..3:
    bit = (h1 + i * h2) % 256
    if (filter[bit / 64] & (1 << (bit % 64))) == 0:
      return false
  return true
```
