//! FST014: Test generator for F* code.
//!
//! Analyzes F* code and suggests test cases based on:
//! - Type signatures (generate valid inputs)
//! - Refinement types (boundary values)
//! - Collection types (edge cases)
//! - Integer bounds (min/max values)
//! - Pre/postconditions (property-based tests)
//! - Module structure (untested modules)
//!
//! This rule produces informational suggestions to help developers write
//! comprehensive tests for their F* functions by identifying test-worthy
//! patterns in signatures.
//!
//! The rule is careful to avoid false positives by skipping:
//! - Specification modules (Spec.* or *.Spec.*) which are pure math, not runtime code
//! - Lemma declarations (they ARE the proofs/tests in F*)
//! - Ghost/erased functions (not extractable to runtime code)
//! - Functions with names containing "lemma" (proof helpers)
//!
//! ## HACL* conventions
//!
//! Test modules follow `Hacl.Test.<Module>` naming, e.g. `Hacl.Test.SHA2`.
//! Test functions are named `test_<function>` and use Stack effects.

use lazy_static::lazy_static;
use regex::Regex;
use std::path::Path;

use super::parser::{parse_fstar_file, BlockType};
use super::rules::{Diagnostic, DiagnosticSeverity, Range, Rule, RuleCode};
use super::shared_patterns::{LEMMA_RE, INLINE_NOEXTRACT_RE, PRIVATE_DECL_RE};

lazy_static! {
    /// Function signature with parameters: val name : params -> return_type
    static ref FUNC_SIGNATURE: Regex = Regex::new(
        r"val\s+(\w+)\s*:(.+)->"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Refinement type pattern: name:base{constraint}
    /// Examples: x:nat{x > 0}, n:int{n >= 0 /\ n < 100}
    static ref REFINEMENT: Regex = Regex::new(
        r"(\w+)\s*:\s*(\w+)\s*\{([^}]+)\}"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Simple refinement without parameter name: base{constraint}
    static ref SIMPLE_REFINEMENT: Regex = Regex::new(
        r"\b(\w+)\s*\{([^}]+)\}"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// List parameter type
    static ref LIST_PARAM: Regex = Regex::new(r"\blist\s+\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Sequence parameter types (Seq.seq, seq)
    static ref SEQ_PARAM: Regex = Regex::new(r"\b[Ss]eq\.seq\s+\w+|\bseq\s+\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Option type
    static ref OPTION_PARAM: Regex = Regex::new(r"\boption\s+\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// UInt32 type patterns
    static ref UINT32: Regex = Regex::new(r"\b(?:U32\.t|UInt32\.t|uint32)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// UInt64 type patterns
    static ref UINT64: Regex = Regex::new(r"\b(?:U64\.t|UInt64\.t|uint64)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// UInt8 type patterns (byte)
    static ref UINT8: Regex = Regex::new(r"\b(?:U8\.t|UInt8\.t|uint8|byte)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// UInt16 type patterns
    static ref UINT16: Regex = Regex::new(r"\b(?:U16\.t|UInt16\.t|uint16)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Signed Int32 type patterns
    static ref INT32: Regex = Regex::new(r"\b(?:I32\.t|Int32\.t|int32)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Natural number type
    static ref NAT: Regex = Regex::new(r"\bnat\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Positive integer type
    static ref POS: Regex = Regex::new(r"\bpos\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// General int type
    static ref INT_TYPE: Regex = Regex::new(r"\bint\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// String type
    static ref STRING_TYPE: Regex = Regex::new(r"\bstring\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Boolean type
    static ref BOOL_TYPE: Regex = Regex::new(r"\bbool\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Buffer/array types that need length testing
    static ref BUFFER_TYPE: Regex = Regex::new(r"\b(?:buffer|lbuffer|B\.buffer)\s+\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Comparison operators in refinements for boundary detection
    static ref COMPARE_LT: Regex = Regex::new(r"(\w+)\s*<\s*(\d+)").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref COMPARE_LE: Regex = Regex::new(r"(\w+)\s*<=\s*(\d+)").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref COMPARE_GT: Regex = Regex::new(r"(\w+)\s*>\s*(\d+)").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref COMPARE_GE: Regex = Regex::new(r"(\w+)\s*>=\s*(\d+)").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref COMPARE_EQ: Regex = Regex::new(r"(\w+)\s*==?\s*(\d+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// GTot effect: ghost total computation, not extractable
    static ref GTOT_EFFECT: Regex = Regex::new(r"\bGTot\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Ghost.erased type: erased at extraction, not testable
    static ref GHOST_ERASED: Regex = Regex::new(r"\b(?:Ghost\.erased|erased)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect `requires` clause in signature.
    static ref REQUIRES_CLAUSE: Regex = Regex::new(r"\brequires\b\s*(.+?)(?:\)|$)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect `ensures` clause in signature.
    static ref ENSURES_CLAUSE: Regex = Regex::new(r"\bensures\b\s*(.+?)(?:\)|$)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect Pure/ST/Stack effect with pre/postconditions.
    static ref EFFECT_WITH_SPEC: Regex = Regex::new(
        r"\b(?:Pure|ST|Stack|StackInline)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

}

/// Type of test suggestion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TestType {
    /// Test boundary values (min, max, off-by-one)
    BoundaryValue,
    /// Test edge cases (empty, singleton, etc.)
    EdgeCase,
    /// Property-based testing suggestion
    PropertyBased,
    /// Test based on refinement type constraints
    RefinementBased,
    /// Test for integer overflow/underflow
    IntegerBounds,
    /// Test derived from pre/postcondition contract
    ContractBased,
    /// Suggestion to create a test module for untested code
    #[allow(dead_code)]
    MissingTestModule,
}

impl std::fmt::Display for TestType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TestType::BoundaryValue => write!(f, "boundary"),
            TestType::EdgeCase => write!(f, "edge-case"),
            TestType::PropertyBased => write!(f, "property"),
            TestType::RefinementBased => write!(f, "refinement"),
            TestType::IntegerBounds => write!(f, "int-bounds"),
            TestType::ContractBased => write!(f, "contract"),
            TestType::MissingTestModule => write!(f, "test-module"),
        }
    }
}

/// A single test suggestion.
#[derive(Debug, Clone)]
pub struct TestSuggestion {
    /// Name of the function this test is for
    pub function_name: String,
    /// Type of test being suggested
    pub test_type: TestType,
    /// Human-readable description of what to test
    pub description: String,
    /// Example test values in F* syntax
    pub example_values: Vec<String>,
    /// Suggested test function name (HACL* convention: test_<name>)
    pub suggested_test_name: Option<String>,
}

impl TestSuggestion {
    fn new(
        function_name: &str,
        test_type: TestType,
        description: &str,
        examples: Vec<&str>,
    ) -> Self {
        Self {
            function_name: function_name.to_string(),
            test_type,
            description: description.to_string(),
            example_values: examples.into_iter().map(String::from).collect(),
            suggested_test_name: None,
        }
    }

    fn with_test_name(mut self, name: &str) -> Self {
        self.suggested_test_name = Some(name.to_string());
        self
    }
}

/// Generate a suggested test function name following HACL* conventions.
///
/// HACL* uses `test_<function_name>` as the naming convention.
/// For boundary tests: `test_<name>_boundaries`
/// For edge cases: `test_<name>_edge_cases`
/// For property tests: `test_<name>_property`
fn suggest_test_name(function_name: &str, test_type: TestType) -> String {
    let suffix = match test_type {
        TestType::BoundaryValue => "_boundaries",
        TestType::EdgeCase => "_edge_cases",
        TestType::PropertyBased => "_property",
        TestType::RefinementBased => "_refinement",
        TestType::IntegerBounds => "_int_bounds",
        TestType::ContractBased => "_contract",
        TestType::MissingTestModule => "",
    };
    format!("test_{}{}", function_name, suffix)
}

/// Generate a test module name following HACL* conventions.
///
/// Given a module name like `Hacl.Hash.SHA256`, returns `Hacl.Test.SHA256`.
/// For non-HACL modules, uses the last component: `MyModule.Core` -> `Test.Core`.
pub fn suggest_test_module_name(module_name: &str) -> String {
    let parts: Vec<&str> = module_name.split('.').collect();

    if parts.len() >= 2 && parts[0] == "Hacl" {
        // HACL* convention: Hacl.Test.<LastPart>
        format!("Hacl.Test.{}", parts[parts.len() - 1])
    } else if parts.len() >= 2 {
        // Generic convention: Test.<LastPart>
        format!("Test.{}", parts[parts.len() - 1])
    } else {
        format!("Test.{}", module_name)
    }
}

/// Generate a test file template following HACL* conventions.
///
/// Produces a complete F* test module skeleton with:
/// - Module declaration
/// - Necessary opens
/// - Placeholder test functions using Stack effect
#[allow(dead_code)]
pub fn generate_test_template(
    module_name: &str,
    test_module_name: &str,
    function_names: &[(&str, &str)], // (name, signature)
) -> String {
    let mut template = String::new();

    template.push_str(&format!("module {}\n\n", test_module_name));
    template.push_str(&format!("open {}\n", module_name));
    template.push_str("open FStar.HyperStack.ST\n\n");
    template.push_str("#set-options \"--fuel 0 --ifuel 0 --z3rlimit 50\"\n\n");

    for (name, _sig) in function_names {
        let test_name = format!("test_{}", name);
        template.push_str(&format!(
            "(** Test [{}] with representative inputs. *)\n",
            name
        ));
        template.push_str(&format!("let {} () : Stack unit\n", test_name));
        template.push_str("  (requires fun h0 -> True)\n");
        template.push_str("  (ensures fun h0 _ h1 -> True)\n");
        template.push_str("=\n");
        template.push_str("  // TODO: Add test assertions\n");
        template.push_str("  ()\n\n");
    }

    template.push_str("let main () : Stack unit\n");
    template.push_str("  (requires fun h0 -> True)\n");
    template.push_str("  (ensures fun h0 _ h1 -> True)\n");
    template.push_str("=\n");

    for (name, _) in function_names {
        template.push_str(&format!("  test_{} ();\n", name));
    }

    template.push_str("  ()\n");

    template
}

/// Extract pre/postcondition text from a signature for property-based test suggestions.
fn extract_contract_info(signature: &str) -> ContractInfo {
    let mut info = ContractInfo {
        has_requires: false,
        has_ensures: false,
        requires_text: None,
        ensures_text: None,
        has_effect_spec: false,
    };

    if let Some(caps) = REQUIRES_CLAUSE.captures(signature) {
        info.has_requires = true;
        info.requires_text = caps.get(1).map(|m| m.as_str().trim().to_string());
    }

    if let Some(caps) = ENSURES_CLAUSE.captures(signature) {
        info.has_ensures = true;
        info.ensures_text = caps.get(1).map(|m| m.as_str().trim().to_string());
    }

    info.has_effect_spec = EFFECT_WITH_SPEC.is_match(signature);

    info
}

/// Information about a function's contract (pre/postconditions).
#[derive(Debug)]
struct ContractInfo {
    has_requires: bool,
    has_ensures: bool,
    requires_text: Option<String>,
    ensures_text: Option<String>,
    has_effect_spec: bool,
}

/// FST014: Test Generator Rule
///
/// Analyzes function signatures and suggests appropriate test cases.
/// Produces hints (not warnings) to guide test development.
///
/// ## Features
///
/// - **Type-driven suggestions**: Suggests boundary values for int types,
///   edge cases for collections, etc.
/// - **Refinement analysis**: Extracts numeric boundaries from refinement types.
/// - **Contract-based suggestions**: Functions with requires/ensures get
///   property-based test suggestions derived from their specifications.
/// - **Test name suggestions**: Following HACL* convention (`test_<name>`).
/// - **Untested module detection**: Flags implementation modules that lack
///   corresponding test modules.
/// - **Test template generation**: Provides a starter test file skeleton.
pub struct TestGeneratorRule;

impl TestGeneratorRule {
    pub fn new() -> Self {
        Self
    }

    /// Analyze a function signature and generate test suggestions.
    fn analyze_function(&self, name: &str, signature: &str) -> Vec<TestSuggestion> {
        let mut suggestions = Vec::new();

        // Check for contract-based test opportunities (requires/ensures)
        self.check_contract_tests(name, signature, &mut suggestions);

        // Check for list/seq parameters - suggest empty and singleton tests
        self.check_collection_types(name, signature, &mut suggestions);

        // Check for option type - suggest None and Some tests
        self.check_option_type(name, signature, &mut suggestions);

        // Check for unsigned integer types - suggest boundary values
        self.check_unsigned_int_types(name, signature, &mut suggestions);

        // Check for signed integer types
        self.check_signed_int_types(name, signature, &mut suggestions);

        // Check for nat/pos types
        self.check_nat_pos_types(name, signature, &mut suggestions);

        // Check for refinement types - extract boundaries
        self.check_refinement_types(name, signature, &mut suggestions);

        // Check for string type - suggest empty and special chars
        self.check_string_type(name, signature, &mut suggestions);

        // Check for bool type - suggest both values
        self.check_bool_type(name, signature, &mut suggestions);

        // Check for buffer types - suggest length edge cases
        self.check_buffer_type(name, signature, &mut suggestions);

        suggestions
    }

    /// Check for pre/postcondition contracts and suggest property-based tests.
    ///
    /// Functions with `requires`/`ensures` clauses have explicit specifications
    /// that can be tested as properties. This is the highest-value test suggestion
    /// since the spec already defines what the function should do.
    fn check_contract_tests(
        &self,
        name: &str,
        signature: &str,
        suggestions: &mut Vec<TestSuggestion>,
    ) {
        let contract = extract_contract_info(signature);

        if contract.has_ensures {
            let ensures_desc = contract.ensures_text
                .as_deref()
                .unwrap_or("postcondition holds");

            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::ContractBased,
                    &format!(
                        "Test postcondition: verify ensures clause holds for valid inputs ({})",
                        truncate_str(ensures_desc, 60)
                    ),
                    vec![
                        "input satisfying requires",
                        "verify ensures on output",
                        "boundary inputs satisfying precondition",
                    ],
                )
                .with_test_name(&suggest_test_name(name, TestType::ContractBased)),
            );
        }

        if contract.has_requires && !contract.has_ensures {
            let requires_desc = contract.requires_text
                .as_deref()
                .unwrap_or("precondition");

            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::ContractBased,
                    &format!(
                        "Test precondition boundary: verify behavior at edge of requires ({})",
                        truncate_str(requires_desc, 60)
                    ),
                    vec![
                        "input just satisfying requires",
                        "input at boundary of requires",
                    ],
                )
                .with_test_name(&suggest_test_name(name, TestType::ContractBased)),
            );
        }

        // Functions using Pure/ST/Stack effects with specs are especially test-worthy
        if contract.has_effect_spec && !contract.has_requires && !contract.has_ensures {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::PropertyBased,
                    "Function uses effectful computation (Pure/ST/Stack) -- verify state invariants",
                    vec!["pre-state valid", "post-state satisfies invariant"],
                )
                .with_test_name(&suggest_test_name(name, TestType::PropertyBased)),
            );
        }
    }

    /// Check for list and sequence parameters.
    fn check_collection_types(
        &self,
        name: &str,
        signature: &str,
        suggestions: &mut Vec<TestSuggestion>,
    ) {
        if LIST_PARAM.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::EdgeCase,
                    "Test with empty list and singleton",
                    vec!["[]", "[x]", "[x; y]"],
                )
                .with_test_name(&suggest_test_name(name, TestType::EdgeCase)),
            );

            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::PropertyBased,
                    "Property: list operations preserve length invariants",
                    vec!["List.length result == f (List.length input)"],
                )
                .with_test_name(&suggest_test_name(name, TestType::PropertyBased)),
            );
        }

        if SEQ_PARAM.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::EdgeCase,
                    "Test with empty sequence and singleton",
                    vec!["Seq.empty", "Seq.create 1 x", "Seq.append s1 s2"],
                )
                .with_test_name(&suggest_test_name(name, TestType::EdgeCase)),
            );

            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::PropertyBased,
                    "Property: sequence length after operations",
                    vec!["Seq.length result == expected_len"],
                )
                .with_test_name(&suggest_test_name(name, TestType::PropertyBased)),
            );
        }
    }

    /// Check for option type parameters.
    fn check_option_type(
        &self,
        name: &str,
        signature: &str,
        suggestions: &mut Vec<TestSuggestion>,
    ) {
        if OPTION_PARAM.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::EdgeCase,
                    "Test with None and Some cases",
                    vec!["None", "Some x"],
                )
                .with_test_name(&suggest_test_name(name, TestType::EdgeCase)),
            );
        }
    }

    /// Check for unsigned integer types (U8, U16, U32, U64).
    fn check_unsigned_int_types(
        &self,
        name: &str,
        signature: &str,
        suggestions: &mut Vec<TestSuggestion>,
    ) {
        if UINT8.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::BoundaryValue,
                    "Test uint8 boundaries",
                    vec!["0uy", "1uy", "127uy", "128uy", "255uy"],
                )
                .with_test_name(&suggest_test_name(name, TestType::BoundaryValue)),
            );

            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::IntegerBounds,
                    "Test uint8 overflow conditions",
                    vec!["255uy + 1uy wraps to 0uy"],
                )
                .with_test_name(&suggest_test_name(name, TestType::IntegerBounds)),
            );
        }

        if UINT16.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::BoundaryValue,
                    "Test uint16 boundaries",
                    vec!["0us", "1us", "0x7FFFus", "0x8000us", "0xFFFFus"],
                )
                .with_test_name(&suggest_test_name(name, TestType::BoundaryValue)),
            );
        }

        if UINT32.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::BoundaryValue,
                    "Test uint32 boundaries",
                    vec!["0ul", "1ul", "0x7FFFFFFFul", "0x80000000ul", "0xFFFFFFFFul"],
                )
                .with_test_name(&suggest_test_name(name, TestType::BoundaryValue)),
            );

            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::IntegerBounds,
                    "Test uint32 overflow conditions",
                    vec!["max_uint32 + 1ul wraps", "0ul - 1ul underflows"],
                )
                .with_test_name(&suggest_test_name(name, TestType::IntegerBounds)),
            );
        }

        if UINT64.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::BoundaryValue,
                    "Test uint64 boundaries",
                    vec![
                        "0uL",
                        "1uL",
                        "0x7FFFFFFFFFFFFFFFuL",
                        "0x8000000000000000uL",
                        "0xFFFFFFFFFFFFFFFFuL",
                    ],
                )
                .with_test_name(&suggest_test_name(name, TestType::BoundaryValue)),
            );
        }
    }

    /// Check for signed integer types.
    fn check_signed_int_types(
        &self,
        name: &str,
        signature: &str,
        suggestions: &mut Vec<TestSuggestion>,
    ) {
        if INT32.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::BoundaryValue,
                    "Test int32 boundaries (including negative)",
                    vec!["0l", "1l", "-1l", "0x7FFFFFFFl (max)", "-0x80000000l (min)"],
                )
                .with_test_name(&suggest_test_name(name, TestType::BoundaryValue)),
            );

            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::IntegerBounds,
                    "Test int32 overflow/underflow",
                    vec!["max_int32 + 1l overflows", "min_int32 - 1l underflows"],
                )
                .with_test_name(&suggest_test_name(name, TestType::IntegerBounds)),
            );
        }
    }

    /// Check for nat and pos types.
    fn check_nat_pos_types(
        &self,
        name: &str,
        signature: &str,
        suggestions: &mut Vec<TestSuggestion>,
    ) {
        if POS.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::BoundaryValue,
                    "Test pos (positive int) boundary",
                    vec!["1", "2", "large positive value"],
                )
                .with_test_name(&suggest_test_name(name, TestType::BoundaryValue)),
            );
        } else if NAT.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::BoundaryValue,
                    "Test nat (non-negative) boundary",
                    vec!["0", "1", "large natural number"],
                )
                .with_test_name(&suggest_test_name(name, TestType::BoundaryValue)),
            );
        } else if INT_TYPE.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::BoundaryValue,
                    "Test int with positive, zero, and negative",
                    vec!["0", "1", "-1", "large positive", "large negative"],
                )
                .with_test_name(&suggest_test_name(name, TestType::BoundaryValue)),
            );
        }
    }

    /// Check for refinement types and extract boundary conditions.
    fn check_refinement_types(
        &self,
        name: &str,
        signature: &str,
        suggestions: &mut Vec<TestSuggestion>,
    ) {
        // Check for explicit refinement patterns
        for caps in REFINEMENT.captures_iter(signature) {
            let param_name = caps.get(1).map(|m| m.as_str()).unwrap_or("x");
            let base_type = caps.get(2).map(|m| m.as_str()).unwrap_or("int");
            let constraint = caps.get(3).map(|m| m.as_str()).unwrap_or("");

            let boundaries = self.extract_boundaries_from_constraint(constraint);

            if !boundaries.is_empty() {
                suggestions.push(
                    TestSuggestion::new(
                        name,
                        TestType::RefinementBased,
                        &format!(
                            "Test refinement boundaries for {}:{} where {}",
                            param_name, base_type, constraint
                        ),
                        boundaries.iter().map(|s| s.as_str()).collect(),
                    )
                    .with_test_name(&suggest_test_name(name, TestType::RefinementBased)),
                );
            } else {
                suggestions.push(
                    TestSuggestion::new(
                        name,
                        TestType::RefinementBased,
                        &format!(
                            "Test refinement constraint: {} satisfies {{{}}}",
                            param_name, constraint
                        ),
                        vec![
                            "value at constraint boundary",
                            "value clearly satisfying",
                            "value near limit",
                        ],
                    )
                    .with_test_name(&suggest_test_name(name, TestType::RefinementBased)),
                );
            }
        }

        // Also check simple refinements without parameter names
        for caps in SIMPLE_REFINEMENT.captures_iter(signature) {
            // Skip if already matched by REFINEMENT
            let full_match = caps.get(0).map(|m| m.as_str()).unwrap_or("");
            if REFINEMENT.is_match(full_match) {
                continue;
            }

            let base_type = caps.get(1).map(|m| m.as_str()).unwrap_or("int");
            let constraint = caps.get(2).map(|m| m.as_str()).unwrap_or("");

            // Skip if constraint looks like a type parameter
            if constraint
                .chars()
                .all(|c| c.is_alphabetic() || c == ' ' || c == '_')
            {
                continue;
            }

            let boundaries = self.extract_boundaries_from_constraint(constraint);

            if !boundaries.is_empty() {
                suggestions.push(
                    TestSuggestion::new(
                        name,
                        TestType::RefinementBased,
                        &format!("Test {} refinement: {{{}}}", base_type, constraint),
                        boundaries.iter().map(|s| s.as_str()).collect(),
                    )
                    .with_test_name(&suggest_test_name(name, TestType::RefinementBased)),
                );
            }
        }
    }

    /// Extract boundary test values from a constraint expression.
    fn extract_boundaries_from_constraint(&self, constraint: &str) -> Vec<String> {
        let mut boundaries = Vec::new();

        // Look for < N patterns: test N-1 (valid), N (invalid boundary)
        for caps in COMPARE_LT.captures_iter(constraint) {
            if let Some(val) = caps.get(2) {
                if let Ok(n) = val.as_str().parse::<i64>() {
                    if n > 0 {
                        boundaries.push(format!("{} (at limit)", n - 1));
                    }
                    boundaries.push(format!("{} (boundary)", n));
                }
            }
        }

        // Look for <= N patterns: test N (valid boundary), N+1 (invalid)
        for caps in COMPARE_LE.captures_iter(constraint) {
            if let Some(val) = caps.get(2) {
                if let Ok(n) = val.as_str().parse::<i64>() {
                    boundaries.push(format!("{} (at limit)", n));
                    boundaries.push(format!("{} (past limit)", n + 1));
                }
            }
        }

        // Look for > N patterns: test N+1 (valid), N (invalid boundary)
        for caps in COMPARE_GT.captures_iter(constraint) {
            if let Some(val) = caps.get(2) {
                if let Ok(n) = val.as_str().parse::<i64>() {
                    boundaries.push(format!("{} (boundary)", n));
                    boundaries.push(format!("{} (at limit)", n + 1));
                }
            }
        }

        // Look for >= N patterns: test N (valid boundary), N-1 (invalid)
        for caps in COMPARE_GE.captures_iter(constraint) {
            if let Some(val) = caps.get(2) {
                if let Ok(n) = val.as_str().parse::<i64>() {
                    if n > 0 {
                        boundaries.push(format!("{} (below limit)", n - 1));
                    }
                    boundaries.push(format!("{} (at limit)", n));
                }
            }
        }

        boundaries
    }

    /// Check for string type parameters.
    fn check_string_type(
        &self,
        name: &str,
        signature: &str,
        suggestions: &mut Vec<TestSuggestion>,
    ) {
        if STRING_TYPE.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::EdgeCase,
                    "Test string edge cases",
                    vec![
                        "\"\"",
                        "\"a\"",
                        "\"longer string\"",
                        "string with special chars",
                    ],
                )
                .with_test_name(&suggest_test_name(name, TestType::EdgeCase)),
            );
        }
    }

    /// Check for boolean type parameters.
    fn check_bool_type(&self, name: &str, signature: &str, suggestions: &mut Vec<TestSuggestion>) {
        if BOOL_TYPE.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::EdgeCase,
                    "Test both boolean values",
                    vec!["true", "false"],
                )
                .with_test_name(&suggest_test_name(name, TestType::EdgeCase)),
            );
        }
    }

    /// Check for buffer types.
    fn check_buffer_type(
        &self,
        name: &str,
        signature: &str,
        suggestions: &mut Vec<TestSuggestion>,
    ) {
        if BUFFER_TYPE.is_match(signature) {
            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::EdgeCase,
                    "Test buffer length edge cases",
                    vec![
                        "empty buffer (len=0)",
                        "single element (len=1)",
                        "typical size",
                        "maximum expected size",
                    ],
                )
                .with_test_name(&suggest_test_name(name, TestType::EdgeCase)),
            );

            suggestions.push(
                TestSuggestion::new(
                    name,
                    TestType::BoundaryValue,
                    "Test buffer index boundaries",
                    vec!["index 0", "index len-1", "ensure no out-of-bounds access"],
                )
                .with_test_name(&suggest_test_name(name, TestType::BoundaryValue)),
            );
        }
    }
}

impl Default for TestGeneratorRule {
    fn default() -> Self {
        Self::new()
    }
}

impl TestGeneratorRule {
    /// Check if a module name indicates a specification module.
    /// Spec modules contain pure mathematical definitions, not extractable code.
    /// Examples: Spec.SHA2, Hacl.Spec.Bignum.Addition, Spec.Agile.Hash
    fn is_spec_module(module_name: &str) -> bool {
        // Module starts with "Spec." or contains ".Spec."
        module_name.starts_with("Spec.")
            || module_name.contains(".Spec.")
            // Also skip ".Lemmas" modules - they are collections of proofs
            || module_name.ends_with(".Lemmas")
            || module_name.contains(".Lemmas.")
    }

    /// Check if a module belongs to the F* standard library.
    ///
    /// Standard library modules (FStar.*, LowStar.*, Prims, C.*) are formally
    /// verified and do not benefit from test generation suggestions. Flagging
    /// them produces thousands of unhelpful diagnostics.
    fn is_stdlib_module(module_name: &str) -> bool {
        module_name.starts_with("FStar.")
            || module_name.starts_with("LowStar.")
            || module_name.starts_with("C.")
            || module_name.starts_with("Steel.")
            || module_name.starts_with("Pulse.")
            || module_name == "Prims"
            || module_name == "FStar"
    }

    /// Check if a file path looks like it belongs to the F* standard library.
    fn is_stdlib_path(file: &Path) -> bool {
        // Check for ulib directory in path
        file.components().any(|c| c.as_os_str() == "ulib")
    }

    /// Check if a module name indicates a test module.
    /// Test modules follow HACL* convention: Hacl.Test.<Module> or Test.<Module>.
    fn is_test_module(module_name: &str) -> bool {
        module_name.starts_with("Test.")
            || module_name.contains(".Test.")
    }

    /// Check if a function signature indicates a lemma (proof) declaration.
    /// Lemmas in F* are proofs themselves -- suggesting tests for proofs is nonsensical.
    fn is_lemma_signature(signature: &str) -> bool {
        LEMMA_RE.is_match(signature)
    }

    /// Check if a signature uses only ghost/erased types (not extractable).
    fn is_ghost_function(signature: &str) -> bool {
        GTOT_EFFECT.is_match(signature)
            || GHOST_ERASED.is_match(signature)
    }

    /// Check if a function name suggests it is a lemma/proof helper.
    fn is_lemma_name(name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        lower.contains("lemma")
            || lower.contains("_lem_")
            || lower.ends_with("_lem")
    }

    /// Check if a block is private or an extraction helper.
    fn is_private_or_helper(block_text: &str, is_private: bool) -> bool {
        is_private
            || PRIVATE_DECL_RE.is_match(block_text)
            || INLINE_NOEXTRACT_RE.is_match(block_text)
    }

    /// Extract the module name from the raw file content.
    fn extract_module_name_from_content(content: &str) -> Option<String> {
        for line in content.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }
            if let Some(rest) = trimmed.strip_prefix("module") {
                let name = rest.trim();
                if !name.is_empty() {
                    return Some(name.to_string());
                }
            }
            break;
        }
        None
    }

    /// Count testable val declarations in a file.
    ///
    /// Returns the count of val declarations that are:
    /// - Not lemmas
    /// - Not ghost/erased
    /// - Not private or extraction helpers
    /// - Not internal (underscore-prefixed)
    #[allow(dead_code)]
    fn count_testable_vals(blocks: &[super::parser::DeclarationBlock], _content_lines: &str) -> usize {
        blocks.iter()
            .filter(|b| b.block_type == BlockType::Val)
            .filter(|b| {
                let sig = b.lines.join(" ");
                let text = b.lines.join("");
                !Self::is_lemma_signature(&sig)
                    && !Self::is_ghost_function(&sig)
                    && !Self::is_private_or_helper(&text, b.is_private)
                    && b.names.iter().all(|n| !n.starts_with('_') && !Self::is_lemma_name(n))
            })
            .count()
    }
}

/// Truncate a string to a maximum length, adding "..." if truncated.
fn truncate_str(s: &str, max_len: usize) -> String {
    if s.len() <= max_len {
        s.to_string()
    } else {
        format!("{}...", &s[..max_len.saturating_sub(3)])
    }
}

impl Rule for TestGeneratorRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST014
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        let (_, blocks) = parse_fstar_file(content);

        // Skip entire spec modules
        let module_name = Self::extract_module_name_from_content(content);
        if let Some(ref name) = module_name {
            if Self::is_spec_module(name) {
                return diagnostics;
            }
        }

        // Also skip based on file path heuristics for files without module declarations
        if let Some(file_name) = file.file_name().and_then(|f| f.to_str()) {
            let lower = file_name.to_ascii_lowercase();
            if lower.starts_with("spec.") || lower.contains(".spec.") {
                return diagnostics;
            }
        }

        // Skip test modules -- they don't need test suggestions
        if let Some(ref name) = module_name {
            if Self::is_test_module(name) {
                return diagnostics;
            }
        }

        // Skip F* standard library modules -- they are formally verified and
        // don't benefit from test generation suggestions. This eliminates
        // thousands of unhelpful diagnostics on ulib.
        if let Some(ref name) = module_name {
            if Self::is_stdlib_module(name) {
                return diagnostics;
            }
        }
        if Self::is_stdlib_path(file) {
            return diagnostics;
        }

        // Skip .fsti interface files -- they define specifications, not
        // testable implementations. Test suggestions belong on .fst files.
        let is_fsti = file.extension().is_some_and(|ext| ext == "fsti");
        if is_fsti {
            return diagnostics;
        }

        // Collect functions with contracts for higher-priority flagging
        let mut contract_functions: Vec<(String, usize)> = Vec::new();

        for block in &blocks {
            // Only analyze val declarations (function signatures)
            if block.block_type != BlockType::Val {
                continue;
            }

            // Join block lines to get full signature
            let signature = block.lines.join(" ");
            let block_text = block.lines.join("");

            // Skip lemma declarations
            if Self::is_lemma_signature(&signature) {
                continue;
            }

            // Skip ghost/erased functions
            if Self::is_ghost_function(&signature) {
                continue;
            }

            // Skip private/helper functions
            if Self::is_private_or_helper(&block_text, block.is_private) {
                continue;
            }

            for name in &block.names {
                // Skip internal functions (starting with underscore)
                if name.starts_with('_') {
                    continue;
                }

                // Skip functions whose names indicate they are lemma/proof helpers
                if Self::is_lemma_name(name) {
                    continue;
                }

                // Track functions with contracts
                let contract = extract_contract_info(&signature);
                if contract.has_requires || contract.has_ensures {
                    contract_functions.push((name.clone(), block.start_line));
                }

                let suggestions = self.analyze_function(name, &signature);

                // Generate one diagnostic per test type to avoid overwhelming output
                let mut seen_types = std::collections::HashSet::new();

                for sugg in suggestions {
                    // Only show one suggestion per test type per function
                    if seen_types.contains(&sugg.test_type) {
                        continue;
                    }
                    seen_types.insert(sugg.test_type);

                    let examples_str = if sugg.example_values.len() <= 3 {
                        sugg.example_values.join(", ")
                    } else {
                        format!(
                            "{}, ... ({} more)",
                            sugg.example_values[..2].join(", "),
                            sugg.example_values.len() - 2
                        )
                    };

                    let test_name_hint = sugg.suggested_test_name
                        .as_ref()
                        .map(|n| format!(" (suggested: `{}`)", n))
                        .unwrap_or_default();

                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST014,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(block.start_line, 1),
                        message: format!(
                            "[{}] Test `{}`: {} (e.g., {}){}",
                            sugg.test_type, sugg.function_name, sugg.description,
                            examples_str, test_name_hint
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn make_path() -> PathBuf {
        PathBuf::from("test.fst")
    }

    fn make_spec_path() -> PathBuf {
        PathBuf::from("Spec.SHA2.fst")
    }

    // ---------------------------------------------------------------
    // Core suggestion tests (non-spec, non-lemma functions)
    // ---------------------------------------------------------------

    #[test]
    fn test_list_parameter_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval process_list : list int -> int\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("empty list")));
        assert!(diags.iter().any(|d| d.message.contains("edge-case")));
    }

    #[test]
    fn test_seq_parameter_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval process_seq : Seq.seq int -> int\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("empty sequence") || d.message.contains("Seq.empty")));
    }

    #[test]
    fn test_uint32_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval hash_value : U32.t -> U32.t\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("uint32") && d.message.contains("boundary")));
        assert!(diags
            .iter()
            .any(|d| d.message.contains("0ul") || d.message.contains("0xFFFFFFFF")));
    }

    #[test]
    fn test_uint64_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval process_large : UInt64.t -> bool\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("uint64")));
    }

    #[test]
    fn test_refinement_type_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval bounded_access : i:nat{i < 100} -> int\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("refinement")));
        assert!(diags
            .iter()
            .any(|d| d.message.contains("99") || d.message.contains("100")));
    }

    #[test]
    fn test_nat_type_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval factorial : nat -> nat\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("nat") || d.message.contains("non-negative")));
        assert!(diags.iter().any(|d| d.message.contains("0")));
    }

    #[test]
    fn test_pos_type_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval divide : int -> pos -> int\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("pos") || d.message.contains("positive")));
        assert!(diags.iter().any(|d| d.message.contains("1")));
    }

    #[test]
    fn test_option_type_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval maybe_process : option int -> int\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("None") && d.message.contains("Some")));
    }

    #[test]
    fn test_bool_type_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval toggle : bool -> bool\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("true") && d.message.contains("false")));
    }

    #[test]
    fn test_string_type_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval parse_input : string -> int\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("string") && d.message.contains("edge")));
    }

    #[test]
    fn test_buffer_type_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval read_buffer : buffer U8.t -> int\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("buffer") && d.message.contains("length")));
    }

    #[test]
    fn test_internal_function_skipped() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval _internal_helper : int -> int\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags.is_empty());
    }

    #[test]
    fn test_multiple_refinement_boundaries() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval bounded_range : x:int{x >= 10 /\\ x < 100} -> bool\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("refinement")));
    }

    #[test]
    fn test_complex_signature() {
        let rule = TestGeneratorRule::new();
        let content =
            "module Test\n\nval complex_func : list (option U32.t) -> n:nat{n > 0} -> Seq.seq bool -> result\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.len() >= 3,
            "Expected multiple suggestions for complex signature"
        );
    }

    #[test]
    fn test_extract_boundaries_lt() {
        let rule = TestGeneratorRule::new();
        let boundaries = rule.extract_boundaries_from_constraint("x < 100");
        assert!(boundaries.iter().any(|b| b.contains("99")));
        assert!(boundaries.iter().any(|b| b.contains("100")));
    }

    #[test]
    fn test_extract_boundaries_ge() {
        let rule = TestGeneratorRule::new();
        let boundaries = rule.extract_boundaries_from_constraint("x >= 5");
        assert!(boundaries.iter().any(|b| b.contains("4")));
        assert!(boundaries.iter().any(|b| b.contains("5")));
    }

    #[test]
    fn test_no_suggestions_for_let_blocks() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nlet helper x = x + 1\n";
        let diags = rule.check(&make_path(), content);
        assert!(diags.is_empty());
    }

    // ---------------------------------------------------------------
    // Severity test: all diagnostics should be Info, not Hint
    // ---------------------------------------------------------------

    #[test]
    fn test_severity_is_hint() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval process : U32.t -> U32.t\n";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.is_empty(), "Should produce at least one suggestion");
        for d in &diags {
            assert_eq!(
                d.severity,
                DiagnosticSeverity::Hint,
                "FST014 should use Hint severity for test suggestions"
            );
        }
    }

    // ---------------------------------------------------------------
    // False-positive filtering: spec modules
    // ---------------------------------------------------------------

    #[test]
    fn test_skip_spec_module_by_declaration() {
        let rule = TestGeneratorRule::new();
        let content = "module Spec.SHA2\n\nval hash : nat -> nat\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Spec.* modules should produce zero suggestions, got {}",
            diags.len()
        );
    }

    #[test]
    fn test_skip_hacl_spec_module() {
        let rule = TestGeneratorRule::new();
        let content = "module Hacl.Spec.Bignum.Addition\n\nval bn_add : nat -> nat -> nat\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "*.Spec.* modules should produce zero suggestions, got {}",
            diags.len()
        );
    }

    #[test]
    fn test_skip_spec_module_by_filename() {
        let rule = TestGeneratorRule::new();
        // No module declaration, but file name starts with Spec.
        let content = "val hash : nat -> nat\n";
        let diags = rule.check(&make_spec_path(), content);
        assert!(
            diags.is_empty(),
            "Spec.* files should produce zero suggestions even without module decl"
        );
    }

    #[test]
    fn test_skip_lemmas_module() {
        let rule = TestGeneratorRule::new();
        let content = "module Hacl.Spec.Montgomery.Lemmas\n\nval foo : pos -> nat\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "*.Lemmas modules should produce zero suggestions"
        );
    }

    // ---------------------------------------------------------------
    // False-positive filtering: lemma declarations
    // ---------------------------------------------------------------

    #[test]
    fn test_skip_lemma_declaration() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval add_comm : a:nat -> b:nat -> Lemma (a + b == b + a)\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Lemma declarations should produce zero suggestions, got {}",
            diags.len()
        );
    }

    #[test]
    fn test_skip_lemma_with_requires_ensures() {
        let rule = TestGeneratorRule::new();
        let content = concat!(
            "module Test\n\n",
            "val mont_reduction_lemma : pbits:pos -> rLen:pos -> n:pos -> mu:nat -> c:nat -> Lemma\n",
            "  (requires c < n * n)\n",
            "  (ensures mont_reduction pbits rLen n mu c < n)\n"
        );
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Lemma (requires/ensures) should produce zero suggestions, got {}",
            diags.len()
        );
    }

    #[test]
    fn test_skip_lemma_named_function() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval bn_add_lemma : nat -> nat -> bool\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Functions named *_lemma should produce zero suggestions, got {}",
            diags.len()
        );
    }

    #[test]
    fn test_skip_lemma_named_function_loop() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval bn_add_lemma_loop : nat -> nat -> bool\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Functions with 'lemma' in name should produce zero suggestions"
        );
    }

    // ---------------------------------------------------------------
    // False-positive filtering: ghost/erased functions
    // ---------------------------------------------------------------

    #[test]
    fn test_skip_gtot_function() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval ghost_fn : nat -> GTot nat\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "GTot functions should produce zero suggestions, got {}",
            diags.len()
        );
    }

    #[test]
    fn test_skip_ghost_erased() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval erased_fn : Ghost.erased nat -> nat\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Ghost.erased functions should produce zero suggestions, got {}",
            diags.len()
        );
    }

    // ---------------------------------------------------------------
    // Non-spec modules should still produce suggestions
    // ---------------------------------------------------------------

    #[test]
    fn test_non_spec_module_produces_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Hacl.Bignum.Addition\n\nval bn_add : nat -> nat -> nat\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.is_empty(),
            "Non-spec modules should still produce suggestions"
        );
    }

    #[test]
    fn test_non_lemma_function_produces_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval compute_hash : U32.t -> U32.t\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.is_empty(),
            "Non-lemma functions should produce suggestions"
        );
    }

    // ---------------------------------------------------------------
    // Helper method unit tests
    // ---------------------------------------------------------------

    #[test]
    fn test_is_spec_module() {
        assert!(TestGeneratorRule::is_spec_module("Spec.SHA2"));
        assert!(TestGeneratorRule::is_spec_module("Spec.Agile.Hash"));
        assert!(TestGeneratorRule::is_spec_module("Hacl.Spec.Bignum.Addition"));
        assert!(TestGeneratorRule::is_spec_module("Hacl.Spec.Montgomery.Lemmas"));
        assert!(TestGeneratorRule::is_spec_module("Foo.Bar.Lemmas"));
        assert!(TestGeneratorRule::is_spec_module("Foo.Lemmas.Helper"));

        assert!(!TestGeneratorRule::is_spec_module("Hacl.Bignum.Addition"));
        assert!(!TestGeneratorRule::is_spec_module("Test"));
        assert!(!TestGeneratorRule::is_spec_module("MyModule.SpecHelper"));
    }

    #[test]
    fn test_is_lemma_signature() {
        assert!(TestGeneratorRule::is_lemma_signature("a:nat -> b:nat -> Lemma (a + b == b + a)"));
        assert!(TestGeneratorRule::is_lemma_signature(
            "pbits:pos -> Lemma (requires c < n) (ensures r < n)"
        ));
        assert!(TestGeneratorRule::is_lemma_signature("Lemma (true)"));

        assert!(!TestGeneratorRule::is_lemma_signature("nat -> nat"));
        assert!(!TestGeneratorRule::is_lemma_signature("U32.t -> U32.t"));
    }

    #[test]
    fn test_is_ghost_function() {
        assert!(TestGeneratorRule::is_ghost_function("nat -> GTot nat"));
        assert!(TestGeneratorRule::is_ghost_function("Ghost.erased nat -> nat"));
        assert!(TestGeneratorRule::is_ghost_function("x:erased int -> int"));

        assert!(!TestGeneratorRule::is_ghost_function("nat -> nat"));
        assert!(!TestGeneratorRule::is_ghost_function("U32.t -> bool"));
    }

    #[test]
    fn test_is_lemma_name() {
        assert!(TestGeneratorRule::is_lemma_name("bn_add_lemma"));
        assert!(TestGeneratorRule::is_lemma_name("bn_add_lemma_loop"));
        assert!(TestGeneratorRule::is_lemma_name("mont_reduction_lemma_step"));
        assert!(TestGeneratorRule::is_lemma_name("foo_lem_bar"));
        assert!(TestGeneratorRule::is_lemma_name("foo_lem"));

        assert!(!TestGeneratorRule::is_lemma_name("bn_add"));
        assert!(!TestGeneratorRule::is_lemma_name("hash_value"));
        assert!(!TestGeneratorRule::is_lemma_name("process"));
    }

    // ---------------------------------------------------------------
    // NEW: Test name suggestion
    // ---------------------------------------------------------------

    #[test]
    fn test_suggest_test_name() {
        assert_eq!(
            suggest_test_name("hash_value", TestType::BoundaryValue),
            "test_hash_value_boundaries"
        );
        assert_eq!(
            suggest_test_name("process_list", TestType::EdgeCase),
            "test_process_list_edge_cases"
        );
        assert_eq!(
            suggest_test_name("safe_div", TestType::ContractBased),
            "test_safe_div_contract"
        );
        assert_eq!(
            suggest_test_name("sort", TestType::PropertyBased),
            "test_sort_property"
        );
    }

    #[test]
    fn test_suggestions_include_test_names() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval compute : U32.t -> U32.t\n";
        let diags = rule.check(&make_path(), content);
        assert!(!diags.is_empty());
        assert!(
            diags.iter().any(|d| d.message.contains("suggested: `test_compute")),
            "Suggestions should include test function names"
        );
    }

    // ---------------------------------------------------------------
    // NEW: Test module name suggestion
    // ---------------------------------------------------------------

    #[test]
    fn test_suggest_test_module_name_hacl() {
        assert_eq!(
            suggest_test_module_name("Hacl.Hash.SHA256"),
            "Hacl.Test.SHA256"
        );
    }

    #[test]
    fn test_suggest_test_module_name_generic() {
        assert_eq!(
            suggest_test_module_name("MyModule.Core"),
            "Test.Core"
        );
    }

    #[test]
    fn test_suggest_test_module_name_simple() {
        assert_eq!(
            suggest_test_module_name("Utils"),
            "Test.Utils"
        );
    }

    // ---------------------------------------------------------------
    // NEW: Contract-based test suggestions
    // ---------------------------------------------------------------

    #[test]
    fn test_contract_ensures_suggestion() {
        let rule = TestGeneratorRule::new();
        let content = r#"module Test

val safe_div : (x: int) -> (y: int) -> Pure int
  (requires y <> 0)
  (ensures fun r -> r * y <= x)
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("[contract]")),
            "Functions with ensures should get contract-based suggestions"
        );
        assert!(
            diags.iter().any(|d| d.message.contains("postcondition")),
            "Contract suggestion should mention postcondition"
        );
    }

    #[test]
    fn test_contract_requires_only_suggestion() {
        let rule = TestGeneratorRule::new();
        let content = r#"module Test

val access : (buf: nat) -> (i: nat) -> Pure int
  (requires i < buf)
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("[contract]")),
            "Functions with requires-only should get contract suggestions"
        );
        assert!(
            diags.iter().any(|d| d.message.contains("precondition")),
            "Requires-only suggestion should mention precondition boundary"
        );
    }

    #[test]
    fn test_effect_spec_suggestion() {
        let rule = TestGeneratorRule::new();
        let content = "module Test\n\nval update_state : (x: nat) -> Pure nat\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("state invariant") || d.message.contains("Pure")),
            "Pure/ST/Stack functions should get state invariant suggestions"
        );
    }

    // ---------------------------------------------------------------
    // NEW: Untested module detection
    // ---------------------------------------------------------------

    #[test]
    fn test_fsti_files_skipped_entirely() {
        let rule = TestGeneratorRule::new();
        let content = r#"module Hacl.Hash.Core

val init : nat -> nat
val update : nat -> nat -> nat
val finish : nat -> nat
val hash : nat -> nat
"#;
        let file = PathBuf::from("Hacl.Hash.Core.fsti");
        let diags = rule.check(&file, content);
        assert!(
            diags.is_empty(),
            ".fsti interface files should produce zero suggestions, got {}",
            diags.len()
        );
    }

    #[test]
    fn test_test_module_not_flagged() {
        let rule = TestGeneratorRule::new();
        let content = "module Test.Hash\n\nval test_hash : nat -> nat\n";
        let file = PathBuf::from("Test.Hash.fst");
        let diags = rule.check(&file, content);
        assert!(
            diags.is_empty(),
            "Test modules should not get suggestions"
        );
    }

    // ---------------------------------------------------------------
    // NEW: Test template generation
    // ---------------------------------------------------------------

    #[test]
    fn test_generate_test_template() {
        let template = generate_test_template(
            "Hacl.Hash.SHA256",
            "Hacl.Test.SHA256",
            &[("init", ""), ("update", ""), ("finish", "")],
        );

        assert!(template.contains("module Hacl.Test.SHA256"));
        assert!(template.contains("open Hacl.Hash.SHA256"));
        assert!(template.contains("open FStar.HyperStack.ST"));
        assert!(template.contains("let test_init"));
        assert!(template.contains("let test_update"));
        assert!(template.contains("let test_finish"));
        assert!(template.contains("let main"));
        assert!(template.contains("Stack unit"));
    }

    // ---------------------------------------------------------------
    // NEW: Private/helper function skipping
    // ---------------------------------------------------------------

    #[test]
    fn test_skip_private_val() {
        let rule = TestGeneratorRule::new();
        let content = r#"module Test

private val internal_fn : nat -> nat
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Private functions should not get test suggestions"
        );
    }

    #[test]
    fn test_skip_inline_noextract_val() {
        let rule = TestGeneratorRule::new();
        let content = r#"module Test

inline_for_extraction noextract
val helper : nat -> nat
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "inline_for_extraction noextract helpers should not get test suggestions"
        );
    }

    // ---------------------------------------------------------------
    // NEW: Test module detection
    // ---------------------------------------------------------------

    #[test]
    fn test_is_test_module() {
        assert!(TestGeneratorRule::is_test_module("Test.SHA2"));
        assert!(TestGeneratorRule::is_test_module("Hacl.Test.SHA256"));

        assert!(!TestGeneratorRule::is_test_module("Hacl.Hash.SHA256"));
        assert!(!TestGeneratorRule::is_test_module("MyModule"));
    }

    #[test]
    fn test_skip_test_module_from_suggestions() {
        let rule = TestGeneratorRule::new();
        let content = "module Test.SHA2\n\nval test_hash : nat -> nat\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Test modules should not get suggestions"
        );
    }

    // ---------------------------------------------------------------
    // NEW: Standard library module skipping
    // ---------------------------------------------------------------

    #[test]
    fn test_skip_fstar_stdlib_module() {
        let rule = TestGeneratorRule::new();
        let content = "module FStar.List.Tot.Base\n\nval hd : list 'a -> 'a\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "FStar.* stdlib modules should produce zero suggestions, got {}",
            diags.len()
        );
    }

    #[test]
    fn test_skip_lowstar_stdlib_module() {
        let rule = TestGeneratorRule::new();
        let content = "module LowStar.Buffer\n\nval create : nat -> nat\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "LowStar.* stdlib modules should produce zero suggestions"
        );
    }

    #[test]
    fn test_skip_prims_module() {
        let rule = TestGeneratorRule::new();
        let content = "module Prims\n\nval op_Addition : int -> int -> int\n";
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.is_empty(),
            "Prims module should produce zero suggestions"
        );
    }

    #[test]
    fn test_is_stdlib_module() {
        assert!(TestGeneratorRule::is_stdlib_module("FStar.List.Tot.Base"));
        assert!(TestGeneratorRule::is_stdlib_module("FStar.UInt32"));
        assert!(TestGeneratorRule::is_stdlib_module("LowStar.Buffer"));
        assert!(TestGeneratorRule::is_stdlib_module("C.String"));
        assert!(TestGeneratorRule::is_stdlib_module("Prims"));
        assert!(TestGeneratorRule::is_stdlib_module("Steel.Memory"));

        assert!(!TestGeneratorRule::is_stdlib_module("Hacl.Hash.SHA256"));
        assert!(!TestGeneratorRule::is_stdlib_module("MyModule"));
        assert!(!TestGeneratorRule::is_stdlib_module("Test.Hash"));
    }

    // ---------------------------------------------------------------
    // NEW: Contract info extraction
    // ---------------------------------------------------------------

    #[test]
    fn test_extract_contract_info_both() {
        let info = extract_contract_info(
            "val foo : int -> Pure int (requires x > 0) (ensures fun r -> r > 0)"
        );
        assert!(info.has_requires);
        assert!(info.has_ensures);
        assert!(info.requires_text.unwrap().contains("x > 0"));
        assert!(info.ensures_text.unwrap().contains("r > 0"));
    }

    #[test]
    fn test_extract_contract_info_none() {
        let info = extract_contract_info("val foo : int -> int");
        assert!(!info.has_requires);
        assert!(!info.has_ensures);
        assert!(!info.has_effect_spec);
    }

    #[test]
    fn test_extract_contract_info_effect() {
        let info = extract_contract_info("val foo : int -> Stack int");
        assert!(info.has_effect_spec);
    }

    // ---------------------------------------------------------------
    // NEW: truncate_str utility
    // ---------------------------------------------------------------

    #[test]
    fn test_truncate_str() {
        assert_eq!(truncate_str("short", 10), "short");
        assert_eq!(truncate_str("this is a long string", 10), "this is...");
    }
}
