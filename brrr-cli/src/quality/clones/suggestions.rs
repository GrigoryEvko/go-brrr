//! Refactoring suggestion generation for detected clone clusters.
//!
//! Analyzes clone clusters to generate actionable refactoring recommendations
//! based on the type of duplication detected.
//!
//! # Refactoring Patterns
//!
//! | Pattern | Suggestion | Effort |
//! |---------|------------|--------|
//! | Identical functions | Delete duplicate, redirect callers | Low |
//! | Similar with params | Extract common function with parameters | Medium |
//! | Similar across classes | Extract trait/interface | Medium |
//! | Similar with types | Make generic over type T | High |
//! | Strategy-like | Apply Strategy pattern | High |
//! | Duplicate files | Delete duplicate file, update imports | Low |
//!
//! # Example
//!
//! ```ignore
//! use brrr::quality::clones::suggestions::{
//!     generate_suggestions, RefactoringSuggestion, RefactoringKind
//! };
//!
//! let suggestions = generate_suggestions(&cluster, &units);
//! for suggestion in &suggestions {
//!     println!("{}: {} (effort: {})",
//!         suggestion.kind, suggestion.description, suggestion.effort);
//! }
//! ```

use fxhash::{FxHashMap, FxHashSet};
use regex::Regex;
use serde::{Deserialize, Serialize};

use crate::semantic::{EmbeddingUnit, UnitKind};

use super::semantic::{CloneCluster, SemanticCloneType};

// =============================================================================
// TYPES
// =============================================================================

/// Kind of refactoring to apply for a clone cluster.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RefactoringKind {
    /// Delete duplicate code, redirect all callers to the canonical implementation.
    /// Used for identical or near-identical clones.
    DeleteDuplicate,

    /// Extract a common function with parameters for the varying parts.
    /// Used when clones differ only in values or identifiers.
    ExtractFunction,

    /// Extract a trait or interface that both implementations satisfy.
    /// Used when similar methods exist in different classes.
    ExtractTrait,

    /// Make the implementation generic over a type parameter.
    /// Used when clones differ primarily in types.
    MakeGeneric,

    /// Apply the Strategy pattern to extract varying behavior.
    /// Used for clones with different algorithmic strategies.
    ApplyStrategy,

    /// Delete a duplicate file and update all imports.
    /// Used for entire file duplications.
    DeleteDuplicateFile,
}

impl RefactoringKind {
    /// Get a human-readable name for this refactoring kind.
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::DeleteDuplicate => "delete_duplicate",
            Self::ExtractFunction => "extract_function",
            Self::ExtractTrait => "extract_trait",
            Self::MakeGeneric => "make_generic",
            Self::ApplyStrategy => "apply_strategy",
            Self::DeleteDuplicateFile => "delete_duplicate_file",
        }
    }

    /// Get a short description of this refactoring kind.
    #[must_use]
    pub fn description(&self) -> &'static str {
        match self {
            Self::DeleteDuplicate => "Delete duplicate, redirect callers",
            Self::ExtractFunction => "Extract common function with parameters",
            Self::ExtractTrait => "Extract trait/interface, implement in both",
            Self::MakeGeneric => "Make generic over type T",
            Self::ApplyStrategy => "Apply Strategy pattern, extract behavior",
            Self::DeleteDuplicateFile => "Delete duplicate file, update imports",
        }
    }
}

impl std::fmt::Display for RefactoringKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Effort level required for a refactoring.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum EffortLevel {
    /// Minimal effort - simple mechanical changes.
    Low,
    /// Moderate effort - requires some design decisions.
    Medium,
    /// Significant effort - requires architectural changes.
    High,
}

impl EffortLevel {
    /// Get string representation.
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Low => "low",
            Self::Medium => "medium",
            Self::High => "high",
        }
    }

    /// Estimate hours of work for this effort level.
    #[must_use]
    pub fn estimated_hours(&self) -> (f32, f32) {
        match self {
            Self::Low => (0.5, 2.0),
            Self::Medium => (2.0, 8.0),
            Self::High => (8.0, 40.0),
        }
    }
}

impl std::fmt::Display for EffortLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// A refactoring suggestion for a clone cluster.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RefactoringSuggestion {
    /// Type of refactoring recommended.
    pub kind: RefactoringKind,

    /// Human-readable description of the refactoring.
    pub description: String,

    /// IDs of units affected by this refactoring.
    pub affected_units: Vec<String>,

    /// Confidence score (0.0 to 1.0) that this is the right refactoring.
    pub confidence: f32,

    /// Estimated effort level.
    pub effort: EffortLevel,

    /// Example code showing the refactoring (optional).
    pub code_example: Option<String>,

    /// Estimated lines of code that could be saved.
    pub lines_saved: usize,

    /// Rationale explaining why this refactoring was suggested.
    pub rationale: String,
}

impl RefactoringSuggestion {
    /// Create a new refactoring suggestion.
    #[must_use]
    pub fn new(
        kind: RefactoringKind,
        description: impl Into<String>,
        affected_units: Vec<String>,
        confidence: f32,
        effort: EffortLevel,
    ) -> Self {
        Self {
            kind,
            description: description.into(),
            affected_units,
            confidence: confidence.clamp(0.0, 1.0),
            effort,
            code_example: None,
            lines_saved: 0,
            rationale: String::new(),
        }
    }

    /// Add a code example to the suggestion.
    #[must_use]
    pub fn with_code_example(mut self, example: impl Into<String>) -> Self {
        self.code_example = Some(example.into());
        self
    }

    /// Add lines saved estimate.
    #[must_use]
    pub fn with_lines_saved(mut self, lines: usize) -> Self {
        self.lines_saved = lines;
        self
    }

    /// Add rationale for the suggestion.
    #[must_use]
    pub fn with_rationale(mut self, rationale: impl Into<String>) -> Self {
        self.rationale = rationale.into();
        self
    }

    /// Get a summary string for display.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "[{} effort, {:.0}% confidence] {}: {} ({} units affected)",
            self.effort,
            self.confidence * 100.0,
            self.kind,
            self.description,
            self.affected_units.len()
        )
    }
}

// =============================================================================
// SUGGESTION GENERATION
// =============================================================================

/// Generate refactoring suggestions for a clone cluster.
///
/// Analyzes the units in the cluster to determine the most appropriate
/// refactoring pattern based on:
/// - Similarity level (identical vs similar)
/// - Unit kinds (functions vs methods vs classes)
/// - Parameter differences
/// - Type differences
/// - File distribution
///
/// # Arguments
///
/// * `cluster` - The clone cluster to analyze
/// * `units` - All embedding units (to look up by ID)
///
/// # Returns
///
/// Vector of refactoring suggestions, sorted by confidence (highest first).
#[must_use]
pub fn generate_suggestions(
    cluster: &CloneCluster,
    units: &[EmbeddingUnit],
) -> Vec<RefactoringSuggestion> {
    if cluster.unit_ids.len() < 2 {
        return Vec::new();
    }

    // Build unit lookup map
    let unit_map: FxHashMap<&str, &EmbeddingUnit> =
        units.iter().map(|u| (u.id.as_str(), u)).collect();

    // Collect cluster units
    let cluster_units: Vec<&EmbeddingUnit> = cluster
        .unit_ids
        .iter()
        .filter_map(|id| unit_map.get(id.as_str()).copied())
        .collect();

    if cluster_units.len() < 2 {
        return Vec::new();
    }

    let mut suggestions = Vec::new();

    // Analyze cluster characteristics
    let analysis = analyze_cluster(&cluster_units, cluster);

    // Generate suggestions based on analysis
    if let Some(suggestion) = suggest_for_identical_clones(&analysis, cluster) {
        suggestions.push(suggestion);
    }

    if let Some(suggestion) = suggest_for_parameter_differences(&analysis, cluster) {
        suggestions.push(suggestion);
    }

    if let Some(suggestion) = suggest_for_method_clones(&analysis, cluster) {
        suggestions.push(suggestion);
    }

    if let Some(suggestion) = suggest_for_type_differences(&analysis, cluster) {
        suggestions.push(suggestion);
    }

    if let Some(suggestion) = suggest_for_file_duplicates(&analysis, cluster) {
        suggestions.push(suggestion);
    }

    if let Some(suggestion) = suggest_for_strategy_pattern(&analysis, cluster) {
        suggestions.push(suggestion);
    }

    // Sort by confidence
    suggestions.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap());

    suggestions
}

/// Generate suggestions for a list of clone pairs.
///
/// Groups pairs into implicit clusters and generates suggestions.
#[must_use]
pub fn generate_suggestions_for_pairs(
    pairs: &[(String, String, f32)], // (unit_a_id, unit_b_id, similarity)
    units: &[EmbeddingUnit],
) -> Vec<RefactoringSuggestion> {
    if pairs.is_empty() {
        return Vec::new();
    }

    // Build unit lookup map
    let unit_map: FxHashMap<&str, &EmbeddingUnit> =
        units.iter().map(|u| (u.id.as_str(), u)).collect();

    let mut suggestions = Vec::new();

    // Process each pair as a mini-cluster
    for (unit_a_id, unit_b_id, similarity) in pairs {
        let unit_a = unit_map.get(unit_a_id.as_str());
        let unit_b = unit_map.get(unit_b_id.as_str());

        if let (Some(unit_a), Some(unit_b)) = (unit_a, unit_b) {
            if let Some(suggestion) = suggest_for_pair(unit_a, unit_b, *similarity) {
                suggestions.push(suggestion);
            }
        }
    }

    // Deduplicate and sort
    suggestions.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap());
    suggestions
}

// =============================================================================
// CLUSTER ANALYSIS
// =============================================================================

/// Analysis results for a clone cluster.
struct ClusterAnalysis<'a> {
    /// Units in the cluster
    units: Vec<&'a EmbeddingUnit>,
    /// Unique files in the cluster
    unique_files: FxHashSet<&'a str>,
    /// Unique parent classes/structs
    unique_parents: FxHashSet<Option<&'a str>>,
    /// Whether all units are methods
    all_methods: bool,
    /// Whether all units are functions
    all_functions: bool,
    /// Whether all units are in the same file
    same_file: bool,
    /// Whether this looks like entire file duplication
    is_file_duplicate: bool,
    /// Detected parameter differences
    param_differences: Vec<ParamDifference>,
    /// Detected type differences
    type_differences: Vec<TypeDifference>,
    /// Average similarity
    avg_similarity: f32,
    /// Minimum similarity
    min_similarity: f32,
    /// Total lines of code
    total_lines: usize,
}

/// Detected parameter difference between units.
struct ParamDifference {
    /// Parameter name in unit A
    param_a: String,
    /// Parameter name in unit B (or None if missing)
    param_b: Option<String>,
}

/// Detected type difference between units.
struct TypeDifference {
    /// Type in unit A
    type_a: String,
    /// Type in unit B
    type_b: String,
}

/// Analyze a cluster to understand its characteristics.
fn analyze_cluster<'a>(units: &[&'a EmbeddingUnit], cluster: &CloneCluster) -> ClusterAnalysis<'a> {
    let unique_files: FxHashSet<&str> = units.iter().map(|u| u.file.as_str()).collect();

    let unique_parents: FxHashSet<Option<&str>> = units
        .iter()
        .map(|u| u.parent.as_deref())
        .collect();

    let all_methods = units.iter().all(|u| u.kind == UnitKind::Method);
    let all_functions = units.iter().all(|u| u.kind == UnitKind::Function);
    let same_file = unique_files.len() == 1;

    // Check for file-level duplication (module units spanning entire file)
    let is_file_duplicate = units.iter().any(|u| u.kind == UnitKind::Module)
        && unique_files.len() > 1;

    // Analyze parameter differences
    let param_differences = detect_parameter_differences(units);

    // Analyze type differences
    let type_differences = detect_type_differences(units);

    // Calculate total lines
    let total_lines: usize = units
        .iter()
        .map(|u| u.end_line.saturating_sub(u.start_line) + 1)
        .sum();

    ClusterAnalysis {
        units: units.to_vec(),
        unique_files,
        unique_parents,
        all_methods,
        all_functions,
        same_file,
        is_file_duplicate,
        param_differences,
        type_differences,
        avg_similarity: cluster.avg_similarity,
        min_similarity: cluster.min_similarity,
        total_lines,
    }
}

// =============================================================================
// PATTERN DETECTION
// =============================================================================

/// Detect parameter differences between units by comparing signatures.
fn detect_parameter_differences(units: &[&EmbeddingUnit]) -> Vec<ParamDifference> {
    if units.len() < 2 {
        return Vec::new();
    }

    let mut differences = Vec::new();

    // Extract parameters from first two units for comparison
    let params_a = extract_parameters(&units[0].signature);
    let params_b = extract_parameters(&units[1].signature);

    // Find parameters that differ only in name
    for (i, param_a) in params_a.iter().enumerate() {
        if let Some(param_b) = params_b.get(i) {
            if param_a != param_b {
                differences.push(ParamDifference {
                    param_a: param_a.clone(),
                    param_b: Some(param_b.clone()),
                });
            }
        } else {
            differences.push(ParamDifference {
                param_a: param_a.clone(),
                param_b: None,
            });
        }
    }

    differences
}

/// Extract parameter names from a function signature.
fn extract_parameters(signature: &str) -> Vec<String> {
    // Match parameter patterns: name: type or name type or just name
    // This is a simplified extraction that works across languages
    static PARAM_PATTERN: once_cell::sync::Lazy<Regex> = once_cell::sync::Lazy::new(|| {
        Regex::new(r"\b([a-zA-Z_][a-zA-Z0-9_]*)\s*[:=]?\s*[A-Z]").expect("valid regex")
    });

    PARAM_PATTERN
        .captures_iter(signature)
        .filter_map(|cap| cap.get(1).map(|m| m.as_str().to_string()))
        .collect()
}

/// Detect type differences between units by comparing code.
fn detect_type_differences(units: &[&EmbeddingUnit]) -> Vec<TypeDifference> {
    if units.len() < 2 {
        return Vec::new();
    }

    let mut differences = Vec::new();

    // Extract type names from first two units
    let types_a = extract_type_names(&units[0].code);
    let types_b = extract_type_names(&units[1].code);

    // Find types that appear in one but not the other
    for type_a in &types_a {
        if !types_b.contains(type_a) {
            // Try to find a corresponding type in B
            for type_b in &types_b {
                if !types_a.contains(type_b) && types_are_similar(type_a, type_b) {
                    differences.push(TypeDifference {
                        type_a: type_a.clone(),
                        type_b: type_b.clone(),
                    });
                    break;
                }
            }
        }
    }

    differences
}

/// Extract type names from code.
fn extract_type_names(code: &str) -> FxHashSet<String> {
    // Match type patterns: capitalized words that look like type names
    static TYPE_PATTERN: once_cell::sync::Lazy<Regex> = once_cell::sync::Lazy::new(|| {
        Regex::new(r"\b([A-Z][a-zA-Z0-9]*(?:<[^>]+>)?)\b").expect("valid regex")
    });

    TYPE_PATTERN
        .captures_iter(code)
        .filter_map(|cap| cap.get(1).map(|m| m.as_str().to_string()))
        .filter(|t| !is_common_keyword(t))
        .collect()
}

/// Check if two types are similar (might be the same concept with different names).
fn types_are_similar(type_a: &str, type_b: &str) -> bool {
    // Simple heuristic: similar length and share some characters
    let len_diff = (type_a.len() as i32 - type_b.len() as i32).abs();
    if len_diff > 5 {
        return false;
    }

    // Check for common suffixes/prefixes indicating similar concepts
    let common_suffixes = ["Type", "Info", "Data", "Item", "Result", "Error", "Config"];
    for suffix in common_suffixes {
        if type_a.ends_with(suffix) && type_b.ends_with(suffix) {
            return true;
        }
    }

    false
}

/// Check if a word is a common language keyword (not a type).
fn is_common_keyword(word: &str) -> bool {
    matches!(
        word,
        "None" | "True" | "False" | "Self" | "Some" | "Ok" | "Err" | "Result" | "Option"
            | "String" | "Vec" | "Box" | "Arc" | "Rc" | "HashMap" | "HashSet"
    )
}

// =============================================================================
// SUGGESTION GENERATORS
// =============================================================================

/// Suggest for identical clones (similarity > 0.98).
fn suggest_for_identical_clones(
    analysis: &ClusterAnalysis,
    cluster: &CloneCluster,
) -> Option<RefactoringSuggestion> {
    if cluster.clone_type != SemanticCloneType::Identical {
        return None;
    }

    let canonical = &analysis.units[0];
    let duplicates: Vec<String> = cluster.unit_ids[1..].to_vec();

    let description = format!(
        "Delete {} duplicate(s), redirect all callers to '{}'",
        duplicates.len(),
        canonical.name
    );

    let rationale = format!(
        "These {} units are semantically identical (>{:.0}% similar). \
         Keep '{}' in {} as the canonical implementation and remove the others.",
        cluster.unit_ids.len(),
        cluster.min_similarity * 100.0,
        canonical.name,
        canonical.file
    );

    let lines_saved = analysis.total_lines / analysis.units.len() * (analysis.units.len() - 1);

    let code_example = format!(
        "// Before: {} duplicates\n\
         // {}: {}\n\
         // ...\n\n\
         // After: single implementation\n\
         // Keep: {}::{}\n\
         // Delete: {}",
        duplicates.len(),
        canonical.file,
        canonical.name,
        canonical.file,
        canonical.name,
        duplicates.join(", ")
    );

    Some(
        RefactoringSuggestion::new(
            RefactoringKind::DeleteDuplicate,
            description,
            cluster.unit_ids.clone(),
            0.95,
            EffortLevel::Low,
        )
        .with_lines_saved(lines_saved)
        .with_rationale(rationale)
        .with_code_example(code_example),
    )
}

/// Suggest extracting a common function when there are parameter differences.
fn suggest_for_parameter_differences(
    analysis: &ClusterAnalysis,
    cluster: &CloneCluster,
) -> Option<RefactoringSuggestion> {
    if analysis.param_differences.is_empty() {
        return None;
    }

    // Only suggest for function/method clones
    if !analysis.all_functions && !analysis.all_methods {
        return None;
    }

    // Higher similarity needed for this suggestion
    if analysis.min_similarity < 0.85 {
        return None;
    }

    let param_count = analysis.param_differences.len();
    let description = format!(
        "Extract common function with {} parameter(s) for varying values",
        param_count
    );

    let param_names: Vec<String> = analysis
        .param_differences
        .iter()
        .map(|p| p.param_a.clone())
        .collect();

    let rationale = format!(
        "These {} units have identical structure but differ in parameters: {}. \
         Extract a common function that accepts these as parameters.",
        cluster.unit_ids.len(),
        param_names.join(", ")
    );

    let lines_saved = analysis.total_lines / analysis.units.len() * (analysis.units.len() - 1);

    let confidence = if param_count <= 2 { 0.85 } else { 0.70 };

    Some(
        RefactoringSuggestion::new(
            RefactoringKind::ExtractFunction,
            description,
            cluster.unit_ids.clone(),
            confidence,
            EffortLevel::Medium,
        )
        .with_lines_saved(lines_saved)
        .with_rationale(rationale),
    )
}

/// Suggest extracting a trait for similar methods in different classes.
fn suggest_for_method_clones(
    analysis: &ClusterAnalysis,
    cluster: &CloneCluster,
) -> Option<RefactoringSuggestion> {
    if !analysis.all_methods {
        return None;
    }

    // Need methods from different classes
    if analysis.unique_parents.len() < 2 {
        return None;
    }

    let parents: Vec<&str> = analysis
        .unique_parents
        .iter()
        .filter_map(|p| *p)
        .collect();

    if parents.is_empty() {
        return None;
    }

    let method_name = &analysis.units[0].name;
    let description = format!(
        "Extract trait with '{}' method, implement in {} classes",
        method_name,
        parents.len()
    );

    let rationale = format!(
        "The method '{}' has similar implementations in classes: {}. \
         Extract a trait/interface that defines this behavior.",
        method_name,
        parents.join(", ")
    );

    let lines_saved = analysis.total_lines / analysis.units.len() * (analysis.units.len() - 1);

    let code_example = format!(
        "// Extract trait:\n\
         trait Has{} {{\n    \
             fn {}(&self);\n\
         }}\n\n\
         // Implement for each class:\n\
         impl Has{} for {} {{ ... }}",
        capitalize(method_name),
        method_name,
        capitalize(method_name),
        parents.first().unwrap_or(&"Type")
    );

    Some(
        RefactoringSuggestion::new(
            RefactoringKind::ExtractTrait,
            description,
            cluster.unit_ids.clone(),
            0.80,
            EffortLevel::Medium,
        )
        .with_lines_saved(lines_saved)
        .with_rationale(rationale)
        .with_code_example(code_example),
    )
}

/// Suggest making code generic when there are type differences.
fn suggest_for_type_differences(
    analysis: &ClusterAnalysis,
    cluster: &CloneCluster,
) -> Option<RefactoringSuggestion> {
    if analysis.type_differences.is_empty() {
        return None;
    }

    let type_count = analysis.type_differences.len();
    let first_diff = &analysis.type_differences[0];

    let description = format!(
        "Make generic over type (e.g., {} -> T)",
        first_diff.type_a
    );

    let rationale = format!(
        "These {} units have similar structure but use different types: {} vs {}. \
         Consider making the implementation generic.",
        cluster.unit_ids.len(),
        first_diff.type_a,
        first_diff.type_b
    );

    let lines_saved = analysis.total_lines / analysis.units.len() * (analysis.units.len() - 1);

    // Generics are harder to get right
    let confidence = if type_count == 1 { 0.75 } else { 0.60 };

    let code_example = format!(
        "// Before:\n\
         fn process_{}(item: {}) {{ ... }}\n\
         fn process_{}(item: {}) {{ ... }}\n\n\
         // After:\n\
         fn process<T>(item: T) {{ ... }}",
        first_diff.type_a.to_lowercase(),
        first_diff.type_a,
        first_diff.type_b.to_lowercase(),
        first_diff.type_b
    );

    Some(
        RefactoringSuggestion::new(
            RefactoringKind::MakeGeneric,
            description,
            cluster.unit_ids.clone(),
            confidence,
            EffortLevel::High,
        )
        .with_lines_saved(lines_saved)
        .with_rationale(rationale)
        .with_code_example(code_example),
    )
}

/// Suggest deleting duplicate files.
fn suggest_for_file_duplicates(
    analysis: &ClusterAnalysis,
    cluster: &CloneCluster,
) -> Option<RefactoringSuggestion> {
    if !analysis.is_file_duplicate {
        return None;
    }

    let files: Vec<&str> = analysis.unique_files.iter().copied().collect();
    let canonical = files.first()?;
    let duplicates: Vec<&str> = files[1..].to_vec();

    let description = format!(
        "Delete {} duplicate file(s), update imports to use '{}'",
        duplicates.len(),
        canonical
    );

    let rationale = format!(
        "These files appear to be duplicates. Keep '{}' and update all \
         imports to reference it instead of: {}",
        canonical,
        duplicates.join(", ")
    );

    Some(
        RefactoringSuggestion::new(
            RefactoringKind::DeleteDuplicateFile,
            description,
            cluster.unit_ids.clone(),
            0.90,
            EffortLevel::Low,
        )
        .with_lines_saved(analysis.total_lines / files.len() * duplicates.len())
        .with_rationale(rationale),
    )
}

/// Suggest applying Strategy pattern for algorithmic variations.
fn suggest_for_strategy_pattern(
    analysis: &ClusterAnalysis,
    cluster: &CloneCluster,
) -> Option<RefactoringSuggestion> {
    // Only suggest for medium similarity (not identical, but similar structure)
    if cluster.clone_type != SemanticCloneType::MediumSimilarity {
        return None;
    }

    // Need multiple units to make Strategy worthwhile
    if analysis.units.len() < 3 {
        return None;
    }

    // Check if units have similar names suggesting variants of same operation
    let names: Vec<&str> = analysis.units.iter().map(|u| u.name.as_str()).collect();
    if !names_suggest_variants(&names) {
        return None;
    }

    let description = "Apply Strategy pattern to extract varying algorithm implementations";

    let rationale = format!(
        "These {} units appear to be variants of the same operation. \
         Extract the common structure and use Strategy pattern for the varying behavior.",
        analysis.units.len()
    );

    let code_example =
        "// Extract strategy trait:\n\
         trait ProcessingStrategy {\n    \
             fn process(&self, data: &Data) -> Result;\n\
         }\n\n\
         // Implement variants:\n\
         struct FastStrategy;\n\
         struct ThoroughStrategy;\n\n\
         impl ProcessingStrategy for FastStrategy { ... }\n\
         impl ProcessingStrategy for ThoroughStrategy { ... }";

    Some(
        RefactoringSuggestion::new(
            RefactoringKind::ApplyStrategy,
            description,
            cluster.unit_ids.clone(),
            0.65,
            EffortLevel::High,
        )
        .with_rationale(rationale)
        .with_code_example(code_example),
    )
}

/// Generate suggestion for a single clone pair.
fn suggest_for_pair(
    unit_a: &EmbeddingUnit,
    unit_b: &EmbeddingUnit,
    similarity: f32,
) -> Option<RefactoringSuggestion> {
    let affected_units = vec![unit_a.id.clone(), unit_b.id.clone()];

    // Identical clones
    if similarity >= 0.98 {
        let description = format!(
            "Delete '{}', redirect callers to '{}'",
            unit_b.name, unit_a.name
        );
        return Some(RefactoringSuggestion::new(
            RefactoringKind::DeleteDuplicate,
            description,
            affected_units,
            0.95,
            EffortLevel::Low,
        ));
    }

    // High similarity - extract function
    if similarity >= 0.90 {
        let description = format!(
            "Extract common function from '{}' and '{}'",
            unit_a.name, unit_b.name
        );
        return Some(RefactoringSuggestion::new(
            RefactoringKind::ExtractFunction,
            description,
            affected_units,
            0.80,
            EffortLevel::Medium,
        ));
    }

    // Methods from different classes
    if unit_a.kind == UnitKind::Method
        && unit_b.kind == UnitKind::Method
        && unit_a.parent != unit_b.parent
    {
        let description = format!(
            "Extract trait for '{}' method shared by '{}' and '{}'",
            unit_a.name,
            unit_a.parent.as_deref().unwrap_or("?"),
            unit_b.parent.as_deref().unwrap_or("?")
        );
        return Some(RefactoringSuggestion::new(
            RefactoringKind::ExtractTrait,
            description,
            affected_units,
            0.75,
            EffortLevel::Medium,
        ));
    }

    None
}

// =============================================================================
// HELPERS
// =============================================================================

/// Check if function names suggest they are variants of the same operation.
fn names_suggest_variants(names: &[&str]) -> bool {
    if names.len() < 2 {
        return false;
    }

    // Find common prefix or suffix
    let first = names[0];

    // Check for common prefix (at least 3 chars)
    for prefix_len in (3..=first.len()).rev() {
        let prefix = &first[..prefix_len];
        if names.iter().all(|n| n.starts_with(prefix)) {
            return true;
        }
    }

    // Check for common suffix
    for suffix_len in (3..=first.len()).rev() {
        let suffix = &first[first.len() - suffix_len..];
        if names.iter().all(|n| n.ends_with(suffix)) {
            return true;
        }
    }

    false
}

/// Capitalize the first letter of a string.
fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
    }
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_test_unit(
        id: &str,
        name: &str,
        kind: UnitKind,
        file: &str,
        parent: Option<&str>,
    ) -> EmbeddingUnit {
        let mut unit = EmbeddingUnit::new(file, name, kind, "def test(): pass", 1, "python");
        unit.id = id.to_string();
        unit.parent = parent.map(String::from);
        unit.signature = format!("def {}(self, x: int, y: str):", name);
        unit.end_line = 10;
        unit
    }

    fn make_test_cluster(unit_ids: Vec<&str>, similarity: f32) -> CloneCluster {
        let clone_type = if similarity >= 0.98 {
            SemanticCloneType::Identical
        } else if similarity >= 0.90 {
            SemanticCloneType::HighSimilarity
        } else if similarity >= 0.80 {
            SemanticCloneType::MediumSimilarity
        } else {
            SemanticCloneType::LowSimilarity
        };

        CloneCluster {
            id: 1,
            unit_ids: unit_ids.iter().map(|s| s.to_string()).collect(),
            centroid: None,
            avg_similarity: similarity,
            min_similarity: similarity - 0.02,
            max_similarity: similarity + 0.01,
            clone_type,
            file_count: 2,
            files: vec!["a.py".to_string(), "b.py".to_string()],
            total_lines: 30,
        }
    }

    #[test]
    fn test_refactoring_kind_as_str() {
        assert_eq!(RefactoringKind::DeleteDuplicate.as_str(), "delete_duplicate");
        assert_eq!(RefactoringKind::ExtractFunction.as_str(), "extract_function");
        assert_eq!(RefactoringKind::ExtractTrait.as_str(), "extract_trait");
        assert_eq!(RefactoringKind::MakeGeneric.as_str(), "make_generic");
        assert_eq!(RefactoringKind::ApplyStrategy.as_str(), "apply_strategy");
        assert_eq!(RefactoringKind::DeleteDuplicateFile.as_str(), "delete_duplicate_file");
    }

    #[test]
    fn test_effort_level_ordering() {
        assert!(EffortLevel::Low < EffortLevel::Medium);
        assert!(EffortLevel::Medium < EffortLevel::High);
    }

    #[test]
    fn test_effort_level_estimated_hours() {
        let (low_min, low_max) = EffortLevel::Low.estimated_hours();
        let (med_min, med_max) = EffortLevel::Medium.estimated_hours();
        let (high_min, high_max) = EffortLevel::High.estimated_hours();

        assert!(low_max <= med_min);
        assert!(med_max <= high_min);
        assert!(low_min < low_max);
        assert!(high_min < high_max);
    }

    #[test]
    fn test_refactoring_suggestion_new() {
        let suggestion = RefactoringSuggestion::new(
            RefactoringKind::DeleteDuplicate,
            "Test description",
            vec!["unit1".to_string(), "unit2".to_string()],
            0.95,
            EffortLevel::Low,
        );

        assert_eq!(suggestion.kind, RefactoringKind::DeleteDuplicate);
        assert_eq!(suggestion.description, "Test description");
        assert_eq!(suggestion.affected_units.len(), 2);
        assert_eq!(suggestion.confidence, 0.95);
        assert_eq!(suggestion.effort, EffortLevel::Low);
        assert!(suggestion.code_example.is_none());
    }

    #[test]
    fn test_refactoring_suggestion_builders() {
        let suggestion = RefactoringSuggestion::new(
            RefactoringKind::ExtractFunction,
            "Extract function",
            vec!["a".to_string()],
            0.8,
            EffortLevel::Medium,
        )
        .with_code_example("fn common() {}")
        .with_lines_saved(50)
        .with_rationale("Because duplication");

        assert_eq!(suggestion.code_example, Some("fn common() {}".to_string()));
        assert_eq!(suggestion.lines_saved, 50);
        assert_eq!(suggestion.rationale, "Because duplication");
    }

    #[test]
    fn test_confidence_clamping() {
        let high = RefactoringSuggestion::new(
            RefactoringKind::DeleteDuplicate,
            "test",
            vec![],
            1.5,
            EffortLevel::Low,
        );
        assert_eq!(high.confidence, 1.0);

        let low = RefactoringSuggestion::new(
            RefactoringKind::DeleteDuplicate,
            "test",
            vec![],
            -0.5,
            EffortLevel::Low,
        );
        assert_eq!(low.confidence, 0.0);
    }

    #[test]
    fn test_generate_suggestions_empty_cluster() {
        let cluster = make_test_cluster(vec![], 0.99);
        let suggestions = generate_suggestions(&cluster, &[]);
        assert!(suggestions.is_empty());
    }

    #[test]
    fn test_generate_suggestions_single_unit() {
        let unit = make_test_unit("a", "func_a", UnitKind::Function, "a.py", None);
        let cluster = make_test_cluster(vec!["a"], 0.99);
        let suggestions = generate_suggestions(&cluster, &[unit]);
        assert!(suggestions.is_empty());
    }

    #[test]
    fn test_generate_suggestions_identical_clones() {
        let unit_a = make_test_unit("a", "func_a", UnitKind::Function, "a.py", None);
        let unit_b = make_test_unit("b", "func_b", UnitKind::Function, "b.py", None);
        let cluster = make_test_cluster(vec!["a", "b"], 0.99);

        let suggestions = generate_suggestions(&cluster, &[unit_a, unit_b]);

        assert!(!suggestions.is_empty());
        let delete_suggestion = suggestions
            .iter()
            .find(|s| s.kind == RefactoringKind::DeleteDuplicate);
        assert!(delete_suggestion.is_some());
        assert!(delete_suggestion.unwrap().confidence >= 0.90);
    }

    #[test]
    fn test_generate_suggestions_method_clones() {
        let unit_a = make_test_unit("a", "save", UnitKind::Method, "a.py", Some("UserModel"));
        let unit_b = make_test_unit("b", "save", UnitKind::Method, "b.py", Some("OrderModel"));
        let cluster = make_test_cluster(vec!["a", "b"], 0.92);

        let suggestions = generate_suggestions(&cluster, &[unit_a, unit_b]);

        let trait_suggestion = suggestions
            .iter()
            .find(|s| s.kind == RefactoringKind::ExtractTrait);
        assert!(trait_suggestion.is_some());
    }

    #[test]
    fn test_extract_parameters() {
        let params = extract_parameters("def process(x: int, y: String, z: MyType):");
        assert!(!params.is_empty());
    }

    #[test]
    fn test_extract_type_names() {
        let code = "let result: MyType = process(data as OtherType);";
        let types = extract_type_names(code);
        assert!(types.contains("MyType"));
        assert!(types.contains("OtherType"));
    }

    #[test]
    fn test_is_common_keyword() {
        assert!(is_common_keyword("None"));
        assert!(is_common_keyword("String"));
        assert!(is_common_keyword("Vec"));
        assert!(!is_common_keyword("MyCustomType"));
    }

    #[test]
    fn test_names_suggest_variants() {
        assert!(names_suggest_variants(&["process_fast", "process_slow", "process_parallel"]));
        assert!(names_suggest_variants(&["parse_json", "parse_xml", "parse_yaml"]));
        assert!(!names_suggest_variants(&["foo", "bar", "baz"]));
    }

    #[test]
    fn test_capitalize() {
        assert_eq!(capitalize("hello"), "Hello");
        assert_eq!(capitalize("HELLO"), "HELLO");
        assert_eq!(capitalize(""), "");
        assert_eq!(capitalize("a"), "A");
    }

    #[test]
    fn test_suggest_for_pair_identical() {
        let unit_a = make_test_unit("a", "func_a", UnitKind::Function, "a.py", None);
        let unit_b = make_test_unit("b", "func_b", UnitKind::Function, "b.py", None);

        let suggestion = suggest_for_pair(&unit_a, &unit_b, 0.99);
        assert!(suggestion.is_some());
        assert_eq!(suggestion.unwrap().kind, RefactoringKind::DeleteDuplicate);
    }

    #[test]
    fn test_suggest_for_pair_high_similarity() {
        let unit_a = make_test_unit("a", "func_a", UnitKind::Function, "a.py", None);
        let unit_b = make_test_unit("b", "func_b", UnitKind::Function, "b.py", None);

        let suggestion = suggest_for_pair(&unit_a, &unit_b, 0.92);
        assert!(suggestion.is_some());
        assert_eq!(suggestion.unwrap().kind, RefactoringKind::ExtractFunction);
    }

    #[test]
    fn test_suggest_for_pair_methods() {
        let unit_a = make_test_unit("a", "save", UnitKind::Method, "a.py", Some("User"));
        let unit_b = make_test_unit("b", "save", UnitKind::Method, "b.py", Some("Order"));

        let suggestion = suggest_for_pair(&unit_a, &unit_b, 0.85);
        assert!(suggestion.is_some());
        assert_eq!(suggestion.unwrap().kind, RefactoringKind::ExtractTrait);
    }

    #[test]
    fn test_generate_suggestions_for_pairs() {
        let unit_a = make_test_unit("a", "func_a", UnitKind::Function, "a.py", None);
        let unit_b = make_test_unit("b", "func_b", UnitKind::Function, "b.py", None);

        let pairs = vec![("a".to_string(), "b".to_string(), 0.99)];
        let suggestions = generate_suggestions_for_pairs(&pairs, &[unit_a, unit_b]);

        assert!(!suggestions.is_empty());
    }

    #[test]
    fn test_refactoring_suggestion_summary() {
        let suggestion = RefactoringSuggestion::new(
            RefactoringKind::DeleteDuplicate,
            "Delete duplicate code",
            vec!["a".to_string(), "b".to_string()],
            0.95,
            EffortLevel::Low,
        );

        let summary = suggestion.summary();
        assert!(summary.contains("low"));
        assert!(summary.contains("95%"));
        assert!(summary.contains("delete_duplicate"));
        assert!(summary.contains("2 units"));
    }
}
