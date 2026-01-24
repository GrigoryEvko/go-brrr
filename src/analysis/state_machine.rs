//! Implicit finite state machine extraction from code.
//!
//! This module extracts implicit state machines from code that manages state
//! through variables, enums, or string comparisons. It detects patterns like:
//!
//! - Variables named `state`, `status`, `phase`, `mode`
//! - String/enum comparisons in conditions
//! - Variable set to string literals/enum values
//! - Transitions guarded by current state
//!
//! # Example
//!
//! ```python
//! class Connection:
//!     def __init__(self):
//!         self.state = "disconnected"
//!
//!     def connect(self):
//!         if self.state == "disconnected":
//!             self.state = "connecting"
//!             # ... do connection
//!             self.state = "connected"
//!
//!     def disconnect(self):
//!         if self.state == "connected":
//!             self.state = "disconnected"
//! ```
//!
//! This would be extracted as a state machine with states:
//! `disconnected` -> `connecting` -> `connected` -> `disconnected`
//!
//! # Output Formats
//!
//! - DOT (Graphviz) for high-quality visualization
//! - Mermaid for documentation embedding
//! - JSON for tooling integration
//! - PlantUML for UML diagrams

use std::collections::{HashMap, HashSet};
use std::path::Path;

use serde::{Deserialize, Serialize};
use streaming_iterator::StreamingIterator;
use tree_sitter::{Node, Query, QueryCursor};

use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;

// =============================================================================
// TYPE DEFINITIONS
// =============================================================================

/// Unique identifier for a state within a state machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct StateId(pub usize);

impl std::fmt::Display for StateId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "S{}", self.0)
    }
}

/// Source code location for a state machine element.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Location {
    /// Source file path
    pub file: String,
    /// Start line (1-indexed)
    pub start_line: usize,
    /// End line (1-indexed)
    pub end_line: usize,
    /// Start column (0-indexed)
    pub start_col: usize,
    /// End column (0-indexed)
    pub end_col: usize,
}

impl Location {
    /// Create a new location from tree-sitter node.
    pub fn from_node(node: Node, file: &str) -> Self {
        Self {
            file: file.to_string(),
            start_line: node.start_position().row + 1,
            end_line: node.end_position().row + 1,
            start_col: node.start_position().column,
            end_col: node.end_position().column,
        }
    }
}

/// A state in the finite state machine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct State {
    /// Unique identifier for this state
    pub id: StateId,
    /// Human-readable state name (e.g., "connected", "disconnected")
    pub name: String,
    /// Actions executed when entering this state
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub entry_actions: Vec<String>,
    /// Actions executed when exiting this state
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub exit_actions: Vec<String>,
    /// Source locations where this state is referenced
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub locations: Vec<Location>,
    /// Whether this is a composite/hierarchical state
    #[serde(default)]
    pub is_composite: bool,
    /// Parent state for hierarchical state machines
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent: Option<StateId>,
    /// Child states for composite states
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub children: Vec<StateId>,
}

impl State {
    /// Create a new simple state.
    pub fn new(id: StateId, name: impl Into<String>) -> Self {
        Self {
            id,
            name: name.into(),
            entry_actions: Vec::new(),
            exit_actions: Vec::new(),
            locations: Vec::new(),
            is_composite: false,
            parent: None,
            children: Vec::new(),
        }
    }

    /// Add a source location reference.
    pub fn add_location(&mut self, location: Location) {
        self.locations.push(location);
    }
}

/// A transition between states in the state machine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transition {
    /// Source state
    pub from: StateId,
    /// Target state
    pub to: StateId,
    /// Event or method that triggers this transition
    pub trigger: String,
    /// Guard condition (optional)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub guard: Option<String>,
    /// Action executed during transition (optional)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub action: Option<String>,
    /// Source location of this transition
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<Location>,
    /// Whether this is an internal transition (no state change)
    #[serde(default)]
    pub is_internal: bool,
}

impl Transition {
    /// Create a new transition.
    pub fn new(from: StateId, to: StateId, trigger: impl Into<String>) -> Self {
        Self {
            from,
            to,
            trigger: trigger.into(),
            guard: None,
            action: None,
            location: None,
            is_internal: false,
        }
    }

    /// Add a guard condition.
    pub fn with_guard(mut self, guard: impl Into<String>) -> Self {
        self.guard = Some(guard.into());
        self
    }

    /// Add an action.
    pub fn with_action(mut self, action: impl Into<String>) -> Self {
        self.action = Some(action.into());
        self
    }

    /// Set the source location.
    pub fn with_location(mut self, location: Location) -> Self {
        self.location = Some(location);
        self
    }
}

/// A complete finite state machine extracted from code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateMachine {
    /// Name of the state machine (e.g., class name, module name)
    pub name: String,
    /// All states in the machine
    pub states: Vec<State>,
    /// All transitions between states
    pub transitions: Vec<Transition>,
    /// Initial state (entry point)
    pub initial_state: StateId,
    /// Final/accepting states
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub final_states: Vec<StateId>,
    /// Name of the variable tracking state
    pub state_variable: String,
    /// Source location of the state machine definition
    pub location: Location,
    /// State ID lookup by name
    #[serde(skip)]
    state_map: HashMap<String, StateId>,
}

impl StateMachine {
    /// Create a new state machine.
    pub fn new(
        name: impl Into<String>,
        state_variable: impl Into<String>,
        location: Location,
    ) -> Self {
        Self {
            name: name.into(),
            states: Vec::new(),
            transitions: Vec::new(),
            initial_state: StateId(0),
            final_states: Vec::new(),
            state_variable: state_variable.into(),
            location,
            state_map: HashMap::new(),
        }
    }

    /// Get or create a state by name.
    pub fn get_or_create_state(&mut self, name: &str) -> StateId {
        if let Some(&id) = self.state_map.get(name) {
            return id;
        }

        let id = StateId(self.states.len());
        self.states.push(State::new(id, name));
        self.state_map.insert(name.to_string(), id);
        id
    }

    /// Add a transition between states.
    pub fn add_transition(&mut self, transition: Transition) {
        self.transitions.push(transition);
    }

    /// Get a state by ID.
    pub fn get_state(&self, id: StateId) -> Option<&State> {
        self.states.get(id.0)
    }

    /// Get a mutable state by ID.
    pub fn get_state_mut(&mut self, id: StateId) -> Option<&mut State> {
        self.states.get_mut(id.0)
    }

    /// Set the initial state by name.
    pub fn set_initial_state(&mut self, name: &str) {
        self.initial_state = self.get_or_create_state(name);
    }

    /// Add a final state by name.
    pub fn add_final_state(&mut self, name: &str) {
        let id = self.get_or_create_state(name);
        if !self.final_states.contains(&id) {
            self.final_states.push(id);
        }
    }
}

// =============================================================================
// OUTPUT FORMATS
// =============================================================================

/// Output format for state machine visualization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OutputFormat {
    /// DOT (Graphviz) format
    #[default]
    Dot,
    /// Mermaid diagram format
    Mermaid,
    /// JSON format
    Json,
    /// PlantUML format
    PlantUml,
}

impl std::str::FromStr for OutputFormat {
    type Err = String;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "dot" | "graphviz" => Ok(OutputFormat::Dot),
            "mermaid" => Ok(OutputFormat::Mermaid),
            "json" => Ok(OutputFormat::Json),
            "plantuml" | "puml" | "uml" => Ok(OutputFormat::PlantUml),
            _ => Err(format!("Unknown output format: {}", s)),
        }
    }
}

impl StateMachine {
    /// Render the state machine to DOT (Graphviz) format.
    pub fn to_dot(&self) -> String {
        let mut out = format!("digraph {} {{\n", sanitize_id(&self.name));
        out.push_str("    rankdir=LR;\n");
        out.push_str("    node [shape=ellipse, fontname=\"Helvetica\"];\n");
        out.push_str("    edge [fontname=\"Helvetica\", fontsize=10];\n\n");

        // Initial state indicator
        out.push_str("    __start__ [shape=point, width=0.2];\n");
        if let Some(initial) = self.get_state(self.initial_state) {
            out.push_str(&format!(
                "    __start__ -> {} [label=\"\"];\n",
                sanitize_id(&initial.name)
            ));
        }

        // Final states
        for &final_id in &self.final_states {
            if let Some(final_state) = self.get_state(final_id) {
                out.push_str(&format!(
                    "    {} [peripheries=2];\n",
                    sanitize_id(&final_state.name)
                ));
            }
        }

        out.push('\n');

        // States
        for state in &self.states {
            let label = escape_dot(&state.name);
            out.push_str(&format!(
                "    {} [label=\"{}\"];\n",
                sanitize_id(&state.name),
                label
            ));
        }

        out.push('\n');

        // Transitions
        for trans in &self.transitions {
            let from_name = self.get_state(trans.from).map(|s| &s.name);
            let to_name = self.get_state(trans.to).map(|s| &s.name);

            if let (Some(from), Some(to)) = (from_name, to_name) {
                let mut label = escape_dot(&trans.trigger);
                if let Some(guard) = &trans.guard {
                    label = format!("{} [{}]", label, escape_dot(guard));
                }
                if let Some(action) = &trans.action {
                    label = format!("{} / {}", label, escape_dot(action));
                }

                out.push_str(&format!(
                    "    {} -> {} [label=\"{}\"];\n",
                    sanitize_id(from),
                    sanitize_id(to),
                    label
                ));
            }
        }

        out.push_str("}\n");
        out
    }

    /// Render the state machine to Mermaid format.
    pub fn to_mermaid(&self) -> String {
        let mut out = String::from("stateDiagram-v2\n");

        // Initial state
        if let Some(initial) = self.get_state(self.initial_state) {
            out.push_str(&format!("    [*] --> {}\n", escape_mermaid(&initial.name)));
        }

        // Transitions
        for trans in &self.transitions {
            let from_name = self.get_state(trans.from).map(|s| &s.name);
            let to_name = self.get_state(trans.to).map(|s| &s.name);

            if let (Some(from), Some(to)) = (from_name, to_name) {
                let mut label = escape_mermaid(&trans.trigger);
                if let Some(guard) = &trans.guard {
                    label = format!("{} [{}]", label, escape_mermaid(guard));
                }

                out.push_str(&format!(
                    "    {} --> {} : {}\n",
                    escape_mermaid(from),
                    escape_mermaid(to),
                    label
                ));
            }
        }

        // Final states
        for &final_id in &self.final_states {
            if let Some(final_state) = self.get_state(final_id) {
                out.push_str(&format!(
                    "    {} --> [*]\n",
                    escape_mermaid(&final_state.name)
                ));
            }
        }

        out
    }

    /// Render the state machine to JSON format.
    pub fn to_json(&self) -> std::result::Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Render the state machine to PlantUML format.
    pub fn to_plantuml(&self) -> String {
        let mut out = String::from("@startuml\n");
        out.push_str(&format!("title {}\n\n", self.name));

        // Initial state
        if let Some(initial) = self.get_state(self.initial_state) {
            out.push_str(&format!("[*] --> {}\n", initial.name));
        }

        // States with entry/exit actions
        for state in &self.states {
            if !state.entry_actions.is_empty() || !state.exit_actions.is_empty() {
                out.push_str(&format!("state {} {{\n", state.name));
                for action in &state.entry_actions {
                    out.push_str(&format!("    {} : entry / {}\n", state.name, action));
                }
                for action in &state.exit_actions {
                    out.push_str(&format!("    {} : exit / {}\n", state.name, action));
                }
                out.push_str("}\n");
            }
        }

        // Transitions
        for trans in &self.transitions {
            let from_name = self.get_state(trans.from).map(|s| &s.name);
            let to_name = self.get_state(trans.to).map(|s| &s.name);

            if let (Some(from), Some(to)) = (from_name, to_name) {
                let mut label = trans.trigger.clone();
                if let Some(guard) = &trans.guard {
                    label = format!("{} [{}]", label, guard);
                }
                if let Some(action) = &trans.action {
                    label = format!("{} / {}", label, action);
                }

                out.push_str(&format!("{} --> {} : {}\n", from, to, label));
            }
        }

        // Final states
        for &final_id in &self.final_states {
            if let Some(final_state) = self.get_state(final_id) {
                out.push_str(&format!("{} --> [*]\n", final_state.name));
            }
        }

        out.push_str("@enduml\n");
        out
    }

    /// Render to the specified format.
    pub fn render(&self, format: OutputFormat) -> std::result::Result<String, String> {
        match format {
            OutputFormat::Dot => Ok(self.to_dot()),
            OutputFormat::Mermaid => Ok(self.to_mermaid()),
            OutputFormat::Json => self.to_json().map_err(|e| e.to_string()),
            OutputFormat::PlantUml => Ok(self.to_plantuml()),
        }
    }
}

// =============================================================================
// VALIDATION
// =============================================================================

/// Validation issue severity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IssueSeverity {
    /// Informational finding
    Info,
    /// Warning - potential issue
    Warning,
    /// Error - definite problem
    Error,
}

/// A validation issue found in the state machine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationIssue {
    /// Severity of the issue
    pub severity: IssueSeverity,
    /// Type of issue
    pub issue_type: String,
    /// Human-readable message
    pub message: String,
    /// Related states (if applicable)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub states: Vec<String>,
    /// Related transitions (if applicable)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub transitions: Vec<(String, String)>,
}

/// Result of state machine validation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationResult {
    /// Whether the state machine is valid (no errors)
    pub is_valid: bool,
    /// List of issues found
    pub issues: Vec<ValidationIssue>,
}

impl StateMachine {
    /// Validate the state machine for common issues.
    ///
    /// Detects:
    /// - Unreachable states (not reachable from initial state)
    /// - Missing transitions (states with no outgoing transitions)
    /// - Non-deterministic transitions (same trigger from same state)
    /// - Dead-end states (non-final states with no outgoing transitions)
    pub fn validate(&self) -> ValidationResult {
        let mut issues = Vec::new();

        // Check for unreachable states
        let reachable = self.compute_reachable_states();
        for state in &self.states {
            if !reachable.contains(&state.id) && state.id != self.initial_state {
                issues.push(ValidationIssue {
                    severity: IssueSeverity::Warning,
                    issue_type: "unreachable_state".to_string(),
                    message: format!("State '{}' is not reachable from initial state", state.name),
                    states: vec![state.name.clone()],
                    transitions: Vec::new(),
                });
            }
        }

        // Check for dead-end states (non-final states without outgoing transitions)
        let outgoing: HashMap<StateId, Vec<&Transition>> = {
            let mut map: HashMap<StateId, Vec<&Transition>> = HashMap::new();
            for trans in &self.transitions {
                map.entry(trans.from).or_default().push(trans);
            }
            map
        };

        for state in &self.states {
            let has_outgoing = outgoing.get(&state.id).map_or(false, |t| !t.is_empty());
            let is_final = self.final_states.contains(&state.id);

            if !has_outgoing && !is_final && reachable.contains(&state.id) {
                issues.push(ValidationIssue {
                    severity: IssueSeverity::Warning,
                    issue_type: "dead_end_state".to_string(),
                    message: format!(
                        "State '{}' has no outgoing transitions and is not a final state",
                        state.name
                    ),
                    states: vec![state.name.clone()],
                    transitions: Vec::new(),
                });
            }
        }

        // Check for non-deterministic transitions
        for state in &self.states {
            if let Some(trans_list) = outgoing.get(&state.id) {
                let mut triggers: HashMap<&str, Vec<&Transition>> = HashMap::new();
                for trans in trans_list {
                    triggers.entry(&trans.trigger).or_default().push(trans);
                }

                for (trigger, trans_group) in &triggers {
                    // Check if there are multiple transitions with the same trigger and no guards
                    let unguarded: Vec<_> =
                        trans_group.iter().filter(|t| t.guard.is_none()).collect();

                    if unguarded.len() > 1 {
                        let targets: Vec<String> = unguarded
                            .iter()
                            .filter_map(|t| self.get_state(t.to).map(|s| s.name.clone()))
                            .collect();

                        issues.push(ValidationIssue {
                            severity: IssueSeverity::Error,
                            issue_type: "non_deterministic".to_string(),
                            message: format!(
                                "Non-deterministic transition: '{}' from '{}' leads to multiple states: {:?}",
                                trigger, state.name, targets
                            ),
                            states: vec![state.name.clone()],
                            transitions: targets
                                .iter()
                                .map(|t| (state.name.clone(), t.clone()))
                                .collect(),
                        });
                    }
                }
            }
        }

        // Check if initial state exists
        if self.get_state(self.initial_state).is_none() {
            issues.push(ValidationIssue {
                severity: IssueSeverity::Error,
                issue_type: "invalid_initial_state".to_string(),
                message: "Initial state does not exist".to_string(),
                states: Vec::new(),
                transitions: Vec::new(),
            });
        }

        let is_valid = !issues.iter().any(|i| i.severity == IssueSeverity::Error);

        ValidationResult { is_valid, issues }
    }

    /// Compute the set of states reachable from the initial state.
    fn compute_reachable_states(&self) -> HashSet<StateId> {
        let mut reachable = HashSet::new();
        let mut queue = vec![self.initial_state];

        // Build adjacency map
        let mut adjacency: HashMap<StateId, Vec<StateId>> = HashMap::new();
        for trans in &self.transitions {
            adjacency.entry(trans.from).or_default().push(trans.to);
        }

        while let Some(state_id) = queue.pop() {
            if reachable.insert(state_id) {
                if let Some(neighbors) = adjacency.get(&state_id) {
                    for &neighbor in neighbors {
                        if !reachable.contains(&neighbor) {
                            queue.push(neighbor);
                        }
                    }
                }
            }
        }

        reachable
    }
}

// =============================================================================
// EXTRACTION ERROR TYPES
// =============================================================================

/// Errors that can occur during state machine extraction.
#[derive(Debug, thiserror::Error)]
pub enum StateMachineError {
    /// No state machine patterns found in the code
    #[error("No state machine patterns found in the code")]
    NoStateMachineFound,

    /// Failed to parse source code
    #[error("Parse error: {0}")]
    ParseError(String),

    /// Unsupported language for state machine extraction
    #[error("Unsupported language: {0}")]
    UnsupportedLanguage(String),

    /// Internal extraction error
    #[error("Extraction error: {0}")]
    ExtractionError(String),
}

// =============================================================================
// STATE MACHINE EXTRACTOR
// =============================================================================

/// Configuration for state machine extraction.
#[derive(Debug, Clone, Default)]
pub struct ExtractorConfig {
    /// Variable names to consider as state variables
    pub state_variable_names: Vec<String>,
    /// Whether to extract from boolean flags as implicit states
    pub extract_boolean_states: bool,
    /// Whether to extract hierarchical state machines
    pub extract_hierarchical: bool,
    /// Maximum depth for nested state extraction
    pub max_depth: usize,
}

impl ExtractorConfig {
    /// Create a new config with default state variable names.
    pub fn new() -> Self {
        Self {
            state_variable_names: vec![
                "state".to_string(),
                "status".to_string(),
                "phase".to_string(),
                "mode".to_string(),
                "_state".to_string(),
                "current_state".to_string(),
                "currentState".to_string(),
            ],
            extract_boolean_states: true,
            extract_hierarchical: false,
            max_depth: 3,
        }
    }
}

/// Extracts state machines from source code.
pub struct StateMachineExtractor {
    config: ExtractorConfig,
}

impl Default for StateMachineExtractor {
    fn default() -> Self {
        Self::new()
    }
}

impl StateMachineExtractor {
    /// Create a new extractor with default configuration.
    pub fn new() -> Self {
        Self {
            config: ExtractorConfig::new(),
        }
    }

    /// Create an extractor with custom configuration.
    pub fn with_config(config: ExtractorConfig) -> Self {
        Self { config }
    }

    /// Extract state machines from a file.
    pub fn extract_from_file(&self, path: &Path) -> Result<Vec<StateMachine>> {
        let registry = LanguageRegistry::global();
        let lang = registry.detect_language(path).ok_or_else(|| {
            BrrrError::UnsupportedLanguage(
                path.extension()
                    .and_then(|e| e.to_str())
                    .unwrap_or("unknown")
                    .to_string(),
            )
        })?;

        let source = std::fs::read(path).map_err(|e| BrrrError::io_with_path(e, path))?;
        let mut parser = lang.parser_for_path(path)?;
        let tree = parser
            .parse(&source, None)
            .ok_or_else(|| BrrrError::Parse {
                file: path.display().to_string(),
                message: "Failed to parse file".to_string(),
            })?;

        self.extract_from_tree(&tree, &source, path.to_string_lossy().as_ref(), lang.name())
    }

    /// Extract state machines from source code string.
    pub fn extract_from_source(
        &self,
        source: &str,
        language: &str,
        file_name: &str,
    ) -> Result<Vec<StateMachine>> {
        let registry = LanguageRegistry::global();
        let lang = registry
            .get_by_name(language)
            .ok_or_else(|| BrrrError::UnsupportedLanguage(language.to_string()))?;

        let source_bytes = source.as_bytes();
        let mut parser = lang.parser()?;
        let tree = parser
            .parse(source_bytes, None)
            .ok_or_else(|| BrrrError::Parse {
                file: file_name.to_string(),
                message: "Failed to parse source".to_string(),
            })?;

        self.extract_from_tree(&tree, source_bytes, file_name, language)
    }

    /// Extract state machines from a parsed tree.
    fn extract_from_tree(
        &self,
        tree: &tree_sitter::Tree,
        source: &[u8],
        file_name: &str,
        language: &str,
    ) -> Result<Vec<StateMachine>> {
        let mut machines = Vec::new();

        match language {
            "python" => {
                machines.extend(self.extract_python_state_machines(tree, source, file_name)?);
            }
            "rust" => {
                machines.extend(self.extract_rust_state_machines(tree, source, file_name)?);
            }
            "typescript" | "javascript" | "tsx" | "jsx" => {
                machines.extend(self.extract_js_state_machines(tree, source, file_name)?);
            }
            "go" => {
                machines.extend(self.extract_go_state_machines(tree, source, file_name)?);
            }
            _ => {
                // Try generic extraction
                machines.extend(self.extract_generic_state_machines(tree, source, file_name)?);
            }
        }

        Ok(machines)
    }

    /// Extract Python state machines.
    fn extract_python_state_machines(
        &self,
        tree: &tree_sitter::Tree,
        source: &[u8],
        file_name: &str,
    ) -> Result<Vec<StateMachine>> {
        let mut machines = Vec::new();

        // Find classes with state variables
        let class_query = r#"
            (class_definition
                name: (identifier) @class_name
                body: (block) @body) @class
        "#;

        let ts_lang = tree.language();
        let query = Query::new(&ts_lang, class_query)
            .map_err(|e| BrrrError::TreeSitter(format!("Query error: {}", e)))?;

        let mut cursor = QueryCursor::new();
        let mut matches = cursor.matches(&query, tree.root_node(), source);

        let class_idx = query.capture_index_for_name("class");
        let name_idx = query.capture_index_for_name("class_name");
        let body_idx = query.capture_index_for_name("body");

        while let Some(match_) = matches.next() {
            let class_node = class_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| c.node)
            });
            let name_node = name_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| c.node)
            });
            let body_node = body_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| c.node)
            });

            if let (Some(class_node), Some(name_node), Some(body_node)) =
                (class_node, name_node, body_node)
            {
                let class_name = node_text(name_node, source);

                if let Some(sm) = self.extract_python_class_fsm(
                    class_node,
                    body_node,
                    &class_name,
                    source,
                    file_name,
                ) {
                    machines.push(sm);
                }
            }
        }

        // Also check for module-level state machines
        if let Some(sm) = self.extract_python_module_fsm(tree.root_node(), source, file_name) {
            machines.push(sm);
        }

        Ok(machines)
    }

    /// Extract state machine from a Python class.
    fn extract_python_class_fsm(
        &self,
        class_node: Node,
        body_node: Node,
        class_name: &str,
        source: &[u8],
        file_name: &str,
    ) -> Option<StateMachine> {
        // Look for state variable assignments in __init__ or at class level
        let mut state_var: Option<String> = None;
        let mut initial_state: Option<String> = None;

        // Find __init__ method and look for state variable
        let mut walker = body_node.walk();
        for child in body_node.children(&mut walker) {
            if child.kind() == "function_definition" {
                if let Some(name_child) = child.child_by_field_name("name") {
                    let method_name = node_text(name_child, source);
                    if method_name == "__init__" {
                        if let Some((var, init_state)) =
                            self.find_python_state_assignment(child, source)
                        {
                            state_var = Some(var);
                            initial_state = Some(init_state);
                            break;
                        }
                    }
                }
            }
        }

        let state_var = state_var?;

        let mut sm = StateMachine::new(
            class_name,
            &state_var,
            Location::from_node(class_node, file_name),
        );

        if let Some(init) = &initial_state {
            sm.set_initial_state(init);
        }

        // Extract transitions from methods
        let mut walker = body_node.walk();
        for child in body_node.children(&mut walker) {
            if child.kind() == "function_definition" {
                if let Some(name_child) = child.child_by_field_name("name") {
                    let method_name = node_text(name_child, source);
                    if method_name != "__init__" {
                        self.extract_python_method_transitions(
                            child,
                            &method_name,
                            &state_var,
                            &mut sm,
                            source,
                            file_name,
                        );
                    }
                }
            }
        }

        if sm.states.len() > 1 && !sm.transitions.is_empty() {
            Some(sm)
        } else {
            None
        }
    }

    /// Find state variable assignment in Python code.
    fn find_python_state_assignment(&self, node: Node, source: &[u8]) -> Option<(String, String)> {
        self.find_python_state_assignment_recursive(node, source)
    }

    fn find_python_state_assignment_recursive(
        &self,
        node: Node,
        source: &[u8],
    ) -> Option<(String, String)> {
        if node.kind() == "assignment" || node.kind() == "expression_statement" {
            let text = node_text(node, source);

            // Check for self.state = "..." pattern
            for var_name in &self.config.state_variable_names {
                let patterns = [
                    format!("self.{} = \"", var_name),
                    format!("self.{} = '", var_name),
                    format!("self.{} = State.", var_name),
                    format!("self._{} = \"", var_name),
                    format!("self._{} = '", var_name),
                ];

                for pattern in &patterns {
                    if text.contains(pattern) {
                        // Extract the initial state value
                        if let Some(value) = extract_string_value(&text) {
                            let full_var = if text.contains(&format!("self._{}", var_name)) {
                                format!("self._{}", var_name)
                            } else {
                                format!("self.{}", var_name)
                            };
                            return Some((full_var, value));
                        }
                    }
                }
            }
        }

        // Recurse into children
        let mut child_walker = node.walk();
        for child in node.children(&mut child_walker) {
            if let Some(result) = self.find_python_state_assignment_recursive(child, source) {
                return Some(result);
            }
        }

        None
    }

    /// Extract transitions from a Python method.
    fn extract_python_method_transitions(
        &self,
        method_node: Node,
        method_name: &str,
        state_var: &str,
        sm: &mut StateMachine,
        source: &[u8],
        file_name: &str,
    ) {
        self.extract_python_transitions_recursive(
            method_node,
            method_name,
            state_var,
            None,
            sm,
            source,
            file_name,
        );
    }

    fn extract_python_transitions_recursive(
        &self,
        node: Node,
        method_name: &str,
        state_var: &str,
        current_guard: Option<&str>,
        sm: &mut StateMachine,
        source: &[u8],
        file_name: &str,
    ) {
        match node.kind() {
            "if_statement" => {
                // Check if the condition is a state comparison
                if let Some(condition_node) = node.child_by_field_name("condition") {
                    let condition_text = node_text(condition_node, source);

                    // Check if this is a state guard
                    if condition_text.contains(state_var) {
                        // Extract the state being checked
                        if let Some(guard_state) = extract_state_from_comparison(&condition_text) {
                            // Look for state assignments in the consequence
                            if let Some(consequence) = node.child_by_field_name("consequence") {
                                self.extract_python_transitions_recursive(
                                    consequence,
                                    method_name,
                                    state_var,
                                    Some(&guard_state),
                                    sm,
                                    source,
                                    file_name,
                                );
                            }
                        }
                    }
                }

                // Process else clauses
                let mut walker = node.walk();
                for child in node.children(&mut walker) {
                    if child.kind() == "else_clause" || child.kind() == "elif_clause" {
                        self.extract_python_transitions_recursive(
                            child,
                            method_name,
                            state_var,
                            current_guard,
                            sm,
                            source,
                            file_name,
                        );
                    }
                }
            }
            "assignment" | "expression_statement" => {
                let text = node_text(node, source);

                // Check for state assignment: self.state = "new_state"
                if text.contains(state_var) && text.contains('=') {
                    if let Some(new_state) = extract_string_value(&text) {
                        if let Some(from_state) = current_guard {
                            let from_id = sm.get_or_create_state(from_state);
                            let to_id = sm.get_or_create_state(&new_state);

                            let mut transition = Transition::new(from_id, to_id, method_name);
                            transition.location = Some(Location::from_node(node, file_name));
                            sm.add_transition(transition);
                        } else {
                            // No guard - this might be initial state setting
                            sm.get_or_create_state(&new_state);
                        }
                    }
                }
            }
            _ => {
                // Recurse into children
                let mut walker = node.walk();
                for child in node.children(&mut walker) {
                    self.extract_python_transitions_recursive(
                        child,
                        method_name,
                        state_var,
                        current_guard,
                        sm,
                        source,
                        file_name,
                    );
                }
            }
        }
    }

    /// Extract module-level state machine from Python code.
    fn extract_python_module_fsm(
        &self,
        root: Node,
        source: &[u8],
        file_name: &str,
    ) -> Option<StateMachine> {
        // Look for module-level state variable
        let mut state_var: Option<String> = None;
        let mut initial_state: Option<String> = None;

        let mut walker = root.walk();
        for child in root.children(&mut walker) {
            if child.kind() == "expression_statement" || child.kind() == "assignment" {
                let text = node_text(child, source);
                for var_name in &self.config.state_variable_names {
                    if text.starts_with(var_name) && text.contains('=') {
                        if let Some(value) = extract_string_value(&text) {
                            state_var = Some(var_name.clone());
                            initial_state = Some(value);
                            break;
                        }
                    }
                }
            }
        }

        let state_var = state_var?;

        let mut sm = StateMachine::new("module", &state_var, Location::from_node(root, file_name));

        if let Some(init) = &initial_state {
            sm.set_initial_state(init);
        }

        // Extract transitions from functions
        let mut walker = root.walk();
        for child in root.children(&mut walker) {
            if child.kind() == "function_definition" {
                if let Some(name_child) = child.child_by_field_name("name") {
                    let func_name = node_text(name_child, source);
                    self.extract_python_method_transitions(
                        child, &func_name, &state_var, &mut sm, source, file_name,
                    );
                }
            }
        }

        if sm.states.len() > 1 && !sm.transitions.is_empty() {
            Some(sm)
        } else {
            None
        }
    }

    /// Extract Rust state machines (enum-based FSM pattern).
    fn extract_rust_state_machines(
        &self,
        tree: &tree_sitter::Tree,
        source: &[u8],
        file_name: &str,
    ) -> Result<Vec<StateMachine>> {
        let mut machines = Vec::new();

        // Look for enum definitions that look like state enums
        let enum_query = r#"
            (enum_item
                name: (type_identifier) @enum_name
                body: (enum_variant_list) @variants) @enum
        "#;

        let ts_lang = tree.language();
        let query = Query::new(&ts_lang, enum_query)
            .map_err(|e| BrrrError::TreeSitter(format!("Query error: {}", e)))?;

        let mut cursor = QueryCursor::new();
        let mut matches = cursor.matches(&query, tree.root_node(), source);

        let enum_idx = query.capture_index_for_name("enum");
        let name_idx = query.capture_index_for_name("enum_name");
        let variants_idx = query.capture_index_for_name("variants");

        while let Some(match_) = matches.next() {
            let enum_node = enum_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| c.node)
            });
            let name_node = name_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| c.node)
            });
            let variants_node = variants_idx.and_then(|idx| {
                match_
                    .captures
                    .iter()
                    .find(|c| c.index == idx)
                    .map(|c| c.node)
            });

            if let (Some(enum_node), Some(name_node), Some(variants_node)) =
                (enum_node, name_node, variants_node)
            {
                let enum_name = node_text(name_node, source);

                // Check if this looks like a state enum
                let name_lower = enum_name.to_lowercase();
                if name_lower.contains("state")
                    || name_lower.contains("status")
                    || name_lower.contains("phase")
                    || name_lower.contains("mode")
                {
                    if let Some(sm) = self.extract_rust_enum_fsm(
                        enum_node,
                        variants_node,
                        &enum_name,
                        tree,
                        source,
                        file_name,
                    ) {
                        machines.push(sm);
                    }
                }
            }
        }

        Ok(machines)
    }

    /// Extract state machine from a Rust enum.
    fn extract_rust_enum_fsm(
        &self,
        enum_node: Node,
        variants_node: Node,
        enum_name: &str,
        tree: &tree_sitter::Tree,
        source: &[u8],
        file_name: &str,
    ) -> Option<StateMachine> {
        let mut sm = StateMachine::new(
            enum_name,
            "state",
            Location::from_node(enum_node, file_name),
        );

        // Extract variants as states
        let mut walker = variants_node.walk();
        let mut first_variant = true;
        for child in variants_node.children(&mut walker) {
            if child.kind() == "enum_variant" {
                if let Some(name_child) = child.child_by_field_name("name") {
                    let variant_name = node_text(name_child, source);
                    let state_id = sm.get_or_create_state(&variant_name);
                    if first_variant {
                        sm.initial_state = state_id;
                        first_variant = false;
                    }
                }
            }
        }

        // Look for match expressions that use this enum
        self.extract_rust_match_transitions(
            tree.root_node(),
            enum_name,
            &mut sm,
            source,
            file_name,
        );

        if sm.states.len() > 1 && !sm.transitions.is_empty() {
            Some(sm)
        } else {
            None
        }
    }

    /// Extract transitions from Rust match expressions.
    fn extract_rust_match_transitions(
        &self,
        node: Node,
        enum_name: &str,
        sm: &mut StateMachine,
        source: &[u8],
        file_name: &str,
    ) {
        if node.kind() == "match_expression" {
            // Check if this match is on our state enum
            if let Some(value_node) = node.child_by_field_name("value") {
                let value_text = node_text(value_node, source);
                if value_text.contains("state") || value_text.contains("self.state") {
                    // Process match arms
                    if let Some(body_node) = node.child_by_field_name("body") {
                        let mut walker = body_node.walk();
                        for child in body_node.children(&mut walker) {
                            if child.kind() == "match_arm" {
                                self.extract_rust_match_arm_transition(
                                    child, enum_name, sm, source, file_name,
                                );
                            }
                        }
                    }
                }
            }
        }

        // Recurse
        let mut walker = node.walk();
        for child in node.children(&mut walker) {
            self.extract_rust_match_transitions(child, enum_name, sm, source, file_name);
        }
    }

    /// Extract transition from a Rust match arm.
    fn extract_rust_match_arm_transition(
        &self,
        arm_node: Node,
        enum_name: &str,
        sm: &mut StateMachine,
        source: &[u8],
        file_name: &str,
    ) {
        // Get the pattern (from state)
        if let Some(pattern_node) = arm_node.child_by_field_name("pattern") {
            let pattern_text = node_text(pattern_node, source);

            // Extract the variant name from patterns like "State::Idle" or "(State::Idle, Event::Start)"
            if let Some(from_state) = extract_rust_enum_variant(&pattern_text, enum_name) {
                // Look for state assignment in the body
                if let Some(value_node) = arm_node.child_by_field_name("value") {
                    self.find_rust_state_assignment(
                        value_node,
                        &from_state,
                        enum_name,
                        sm,
                        source,
                        file_name,
                    );
                }
            }
        }
    }

    /// Find state assignment in Rust code.
    fn find_rust_state_assignment(
        &self,
        node: Node,
        from_state: &str,
        enum_name: &str,
        sm: &mut StateMachine,
        source: &[u8],
        file_name: &str,
    ) {
        let text = node_text(node, source);

        // Look for self.state = State::NewState pattern
        if (text.contains("self.state =") || text.contains("state ="))
            && text.contains(&format!("{}::", enum_name))
        {
            if let Some(to_state) = extract_rust_enum_variant(&text, enum_name) {
                if from_state != to_state {
                    let from_id = sm.get_or_create_state(from_state);
                    let to_id = sm.get_or_create_state(&to_state);

                    let transition = Transition::new(from_id, to_id, "transition")
                        .with_location(Location::from_node(node, file_name));
                    sm.add_transition(transition);
                }
            }
        }

        // Recurse
        let mut walker = node.walk();
        for child in node.children(&mut walker) {
            self.find_rust_state_assignment(child, from_state, enum_name, sm, source, file_name);
        }
    }

    /// Extract JavaScript/TypeScript state machines.
    fn extract_js_state_machines(
        &self,
        tree: &tree_sitter::Tree,
        source: &[u8],
        file_name: &str,
    ) -> Result<Vec<StateMachine>> {
        let mut machines = Vec::new();

        // Look for classes with state properties
        // Note: TypeScript uses type_identifier, JavaScript uses identifier
        // Use _ to match any node type for name
        let class_query = r#"
            (class_declaration
                name: (_) @class_name
                body: (class_body) @body) @class
        "#;

        let ts_lang = tree.language();
        if let Ok(query) = Query::new(&ts_lang, class_query) {
            let mut cursor = QueryCursor::new();
            let mut matches = cursor.matches(&query, tree.root_node(), source);

            let class_idx = query.capture_index_for_name("class");
            let name_idx = query.capture_index_for_name("class_name");
            let body_idx = query.capture_index_for_name("body");

            while let Some(match_) = matches.next() {
                let class_node = class_idx.and_then(|idx| {
                    match_
                        .captures
                        .iter()
                        .find(|c| c.index == idx)
                        .map(|c| c.node)
                });
                let name_node = name_idx.and_then(|idx| {
                    match_
                        .captures
                        .iter()
                        .find(|c| c.index == idx)
                        .map(|c| c.node)
                });
                let body_node = body_idx.and_then(|idx| {
                    match_
                        .captures
                        .iter()
                        .find(|c| c.index == idx)
                        .map(|c| c.node)
                });

                if let (Some(class_node), Some(name_node), Some(body_node)) =
                    (class_node, name_node, body_node)
                {
                    let class_name = node_text(name_node, source);
                    if let Some(sm) = self.extract_js_class_fsm(
                        class_node,
                        body_node,
                        &class_name,
                        source,
                        file_name,
                    ) {
                        machines.push(sm);
                    }
                }
            }
        }

        Ok(machines)
    }

    /// Extract state machine from a JavaScript/TypeScript class.
    fn extract_js_class_fsm(
        &self,
        class_node: Node,
        body_node: Node,
        class_name: &str,
        source: &[u8],
        file_name: &str,
    ) -> Option<StateMachine> {
        // Look for constructor with state initialization
        let mut state_var: Option<String> = None;
        let mut initial_state: Option<String> = None;

        let mut walker = body_node.walk();
        for child in body_node.children(&mut walker) {
            if child.kind() == "method_definition" {
                if let Some(name_child) = child.child_by_field_name("name") {
                    let method_name = node_text(name_child, source);
                    if method_name == "constructor" {
                        if let Some((var, init)) = self.find_js_state_assignment(child, source) {
                            state_var = Some(var);
                            initial_state = Some(init);
                            break;
                        }
                    }
                }
            }
            // Also check for class field declarations
            if child.kind() == "field_definition" || child.kind() == "public_field_definition" {
                let text = node_text(child, source);
                for var_name in &self.config.state_variable_names {
                    if text.contains(var_name) && text.contains('=') {
                        if let Some(value) = extract_string_value(&text) {
                            state_var = Some(format!("this.{}", var_name));
                            initial_state = Some(value);
                            break;
                        }
                    }
                }
            }
        }

        let state_var = state_var?;

        let mut sm = StateMachine::new(
            class_name,
            &state_var,
            Location::from_node(class_node, file_name),
        );

        if let Some(init) = &initial_state {
            sm.set_initial_state(init);
        }

        // Extract transitions from methods
        let mut walker = body_node.walk();
        for child in body_node.children(&mut walker) {
            if child.kind() == "method_definition" {
                if let Some(name_child) = child.child_by_field_name("name") {
                    let method_name = node_text(name_child, source);
                    if method_name != "constructor" {
                        self.extract_js_method_transitions(
                            child,
                            &method_name,
                            &state_var,
                            &mut sm,
                            source,
                            file_name,
                        );
                    }
                }
            }
        }

        if sm.states.len() > 1 && !sm.transitions.is_empty() {
            Some(sm)
        } else {
            None
        }
    }

    /// Find state assignment in JavaScript/TypeScript code.
    fn find_js_state_assignment(&self, node: Node, source: &[u8]) -> Option<(String, String)> {
        self.find_js_state_assignment_recursive(node, source)
    }

    fn find_js_state_assignment_recursive(
        &self,
        node: Node,
        source: &[u8],
    ) -> Option<(String, String)> {
        let text = node_text(node, source);

        for var_name in &self.config.state_variable_names {
            let patterns = [
                format!("this.{} = \"", var_name),
                format!("this.{} = '", var_name),
                format!("this.{} = `", var_name),
            ];

            for pattern in &patterns {
                if text.contains(pattern) {
                    if let Some(value) = extract_string_value(&text) {
                        return Some((format!("this.{}", var_name), value));
                    }
                }
            }
        }

        // Recurse
        let mut walker = node.walk();
        for child in node.children(&mut walker) {
            if let Some(result) = self.find_js_state_assignment_recursive(child, source) {
                return Some(result);
            }
        }

        None
    }

    /// Extract transitions from a JavaScript/TypeScript method.
    fn extract_js_method_transitions(
        &self,
        method_node: Node,
        method_name: &str,
        state_var: &str,
        sm: &mut StateMachine,
        source: &[u8],
        file_name: &str,
    ) {
        self.extract_js_transitions_recursive(
            method_node,
            method_name,
            state_var,
            None,
            sm,
            source,
            file_name,
        );
    }

    fn extract_js_transitions_recursive(
        &self,
        node: Node,
        method_name: &str,
        state_var: &str,
        current_guard: Option<&str>,
        sm: &mut StateMachine,
        source: &[u8],
        file_name: &str,
    ) {
        match node.kind() {
            "if_statement" => {
                if let Some(condition_node) = node.child_by_field_name("condition") {
                    let condition_text = node_text(condition_node, source);

                    if condition_text.contains(state_var) || condition_text.contains("this.state") {
                        if let Some(guard_state) = extract_state_from_comparison(&condition_text) {
                            if let Some(consequence) = node.child_by_field_name("consequence") {
                                self.extract_js_transitions_recursive(
                                    consequence,
                                    method_name,
                                    state_var,
                                    Some(&guard_state),
                                    sm,
                                    source,
                                    file_name,
                                );
                            }
                        }
                    }
                }

                // Process else
                if let Some(alternative) = node.child_by_field_name("alternative") {
                    self.extract_js_transitions_recursive(
                        alternative,
                        method_name,
                        state_var,
                        current_guard,
                        sm,
                        source,
                        file_name,
                    );
                }
                // Return early - we've already processed all relevant parts
                return;
            }
            "switch_statement" => {
                if let Some(value_node) = node.child_by_field_name("value") {
                    let value_text = node_text(value_node, source);
                    if value_text.contains(state_var) || value_text.contains("this.state") {
                        if let Some(body_node) = node.child_by_field_name("body") {
                            let mut walker = body_node.walk();
                            for child in body_node.children(&mut walker) {
                                if child.kind() == "switch_case" {
                                    if let Some(case_value) = child.child_by_field_name("value") {
                                        let case_text = node_text(case_value, source);
                                        let from_state = case_text
                                            .trim_matches(|c| c == '"' || c == '\'' || c == '`')
                                            .to_string();

                                        self.extract_js_transitions_recursive(
                                            child,
                                            method_name,
                                            state_var,
                                            Some(&from_state),
                                            sm,
                                            source,
                                            file_name,
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
                // Return early - we've already processed all relevant parts
                return;
            }
            // Only match assignment_expression to avoid double-counting
            // (expression_statement contains assignment_expression as child)
            "assignment_expression" => {
                let text = node_text(node, source);

                if (text.contains(state_var) || text.contains("this.state")) && text.contains('=') {
                    if let Some(new_state) = extract_string_value(&text) {
                        if let Some(from_state) = current_guard {
                            let from_id = sm.get_or_create_state(from_state);
                            let to_id = sm.get_or_create_state(&new_state);

                            let transition = Transition::new(from_id, to_id, method_name)
                                .with_location(Location::from_node(node, file_name));
                            sm.add_transition(transition);
                        } else {
                            sm.get_or_create_state(&new_state);
                        }
                    }
                }
            }
            _ => {}
        }

        // Recurse into children
        let mut walker = node.walk();
        for child in node.children(&mut walker) {
            self.extract_js_transitions_recursive(
                child,
                method_name,
                state_var,
                current_guard,
                sm,
                source,
                file_name,
            );
        }
    }

    /// Extract Go state machines.
    fn extract_go_state_machines(
        &self,
        tree: &tree_sitter::Tree,
        source: &[u8],
        file_name: &str,
    ) -> Result<Vec<StateMachine>> {
        let mut machines = Vec::new();

        // Look for type definitions with state-like fields
        let type_query = r#"
            (type_declaration
                (type_spec
                    name: (type_identifier) @type_name
                    type: (struct_type) @struct_body)) @type_decl
        "#;

        let ts_lang = tree.language();
        if let Ok(query) = Query::new(&ts_lang, type_query) {
            let mut cursor = QueryCursor::new();
            let mut matches = cursor.matches(&query, tree.root_node(), source);

            let type_idx = query.capture_index_for_name("type_decl");
            let name_idx = query.capture_index_for_name("type_name");
            let body_idx = query.capture_index_for_name("struct_body");

            while let Some(match_) = matches.next() {
                let type_node = type_idx.and_then(|idx| {
                    match_
                        .captures
                        .iter()
                        .find(|c| c.index == idx)
                        .map(|c| c.node)
                });
                let name_node = name_idx.and_then(|idx| {
                    match_
                        .captures
                        .iter()
                        .find(|c| c.index == idx)
                        .map(|c| c.node)
                });
                let body_node = body_idx.and_then(|idx| {
                    match_
                        .captures
                        .iter()
                        .find(|c| c.index == idx)
                        .map(|c| c.node)
                });

                if let (Some(type_node), Some(name_node), Some(body_node)) =
                    (type_node, name_node, body_node)
                {
                    let type_name = node_text(name_node, source);
                    if let Some(sm) = self.extract_go_struct_fsm(
                        type_node, body_node, &type_name, tree, source, file_name,
                    ) {
                        machines.push(sm);
                    }
                }
            }
        }

        Ok(machines)
    }

    /// Extract state machine from a Go struct.
    fn extract_go_struct_fsm(
        &self,
        type_node: Node,
        struct_body: Node,
        type_name: &str,
        tree: &tree_sitter::Tree,
        source: &[u8],
        file_name: &str,
    ) -> Option<StateMachine> {
        // Check if struct has a state field
        let mut state_field: Option<String> = None;

        let mut walker = struct_body.walk();
        for child in struct_body.children(&mut walker) {
            if child.kind() == "field_declaration" {
                let text = node_text(child, source);
                for var_name in &self.config.state_variable_names {
                    if text.to_lowercase().contains(&var_name.to_lowercase()) {
                        state_field = Some(var_name.clone());
                        break;
                    }
                }
            }
        }

        let state_field = state_field?;

        let mut sm = StateMachine::new(
            type_name,
            &state_field,
            Location::from_node(type_node, file_name),
        );

        // Look for methods on this type that manipulate state
        self.extract_go_method_transitions(
            tree.root_node(),
            type_name,
            &state_field,
            &mut sm,
            source,
            file_name,
        );

        if sm.states.len() > 1 && !sm.transitions.is_empty() {
            Some(sm)
        } else {
            None
        }
    }

    /// Extract transitions from Go methods.
    fn extract_go_method_transitions(
        &self,
        node: Node,
        type_name: &str,
        state_field: &str,
        sm: &mut StateMachine,
        source: &[u8],
        file_name: &str,
    ) {
        if node.kind() == "method_declaration" {
            // Check if this is a method on our type
            if let Some(receiver) = node.child_by_field_name("receiver") {
                let receiver_text = node_text(receiver, source);
                if receiver_text.contains(type_name) {
                    if let Some(name_child) = node.child_by_field_name("name") {
                        let method_name = node_text(name_child, source);
                        if let Some(body) = node.child_by_field_name("body") {
                            self.extract_go_body_transitions(
                                body,
                                &method_name,
                                state_field,
                                None,
                                sm,
                                source,
                                file_name,
                            );
                        }
                    }
                }
            }
        }

        // Recurse
        let mut walker = node.walk();
        for child in node.children(&mut walker) {
            self.extract_go_method_transitions(
                child,
                type_name,
                state_field,
                sm,
                source,
                file_name,
            );
        }
    }

    fn extract_go_body_transitions(
        &self,
        node: Node,
        method_name: &str,
        state_field: &str,
        current_guard: Option<&str>,
        sm: &mut StateMachine,
        source: &[u8],
        file_name: &str,
    ) {
        match node.kind() {
            "if_statement" => {
                if let Some(condition_node) = node.child_by_field_name("condition") {
                    let condition_text = node_text(condition_node, source);

                    if condition_text.contains(state_field) {
                        if let Some(guard_state) = extract_state_from_comparison(&condition_text) {
                            if let Some(consequence) = node.child_by_field_name("consequence") {
                                self.extract_go_body_transitions(
                                    consequence,
                                    method_name,
                                    state_field,
                                    Some(&guard_state),
                                    sm,
                                    source,
                                    file_name,
                                );
                            }
                        }
                    }
                }
            }
            "switch_statement" => {
                if let Some(value_node) = node.child_by_field_name("value") {
                    let value_text = node_text(value_node, source);
                    if value_text.contains(state_field) {
                        let mut walker = node.walk();
                        for child in node.children(&mut walker) {
                            if child.kind() == "expression_case" {
                                if let Some(case_values) = child.child_by_field_name("value") {
                                    let case_text = node_text(case_values, source);
                                    let from_state = case_text.trim_matches('"').to_string();
                                    self.extract_go_body_transitions(
                                        child,
                                        method_name,
                                        state_field,
                                        Some(&from_state),
                                        sm,
                                        source,
                                        file_name,
                                    );
                                }
                            }
                        }
                    }
                }
            }
            "assignment_statement" | "short_var_declaration" => {
                let text = node_text(node, source);
                if text.contains(state_field) && text.contains('=') {
                    if let Some(new_state) = extract_string_value(&text) {
                        if let Some(from_state) = current_guard {
                            let from_id = sm.get_or_create_state(from_state);
                            let to_id = sm.get_or_create_state(&new_state);

                            let transition = Transition::new(from_id, to_id, method_name)
                                .with_location(Location::from_node(node, file_name));
                            sm.add_transition(transition);
                        } else {
                            sm.get_or_create_state(&new_state);
                        }
                    }
                }
            }
            _ => {}
        }

        // Recurse
        let mut walker = node.walk();
        for child in node.children(&mut walker) {
            self.extract_go_body_transitions(
                child,
                method_name,
                state_field,
                current_guard,
                sm,
                source,
                file_name,
            );
        }
    }

    /// Generic state machine extraction for unsupported languages.
    fn extract_generic_state_machines(
        &self,
        _tree: &tree_sitter::Tree,
        _source: &[u8],
        _file_name: &str,
    ) -> Result<Vec<StateMachine>> {
        // For unsupported languages, return empty
        Ok(Vec::new())
    }
}

// =============================================================================
// HELPER FUNCTIONS
// =============================================================================

/// Get text content of a node.
fn node_text(node: Node, source: &[u8]) -> String {
    std::str::from_utf8(&source[node.start_byte()..node.end_byte()])
        .unwrap_or("")
        .to_string()
}

/// Extract string value from an assignment expression.
fn extract_string_value(text: &str) -> Option<String> {
    // Look for quoted strings
    let patterns = ['"', '\'', '`'];
    for quote in patterns {
        if let Some(start) = text.find(quote) {
            if let Some(end) = text[start + 1..].find(quote) {
                return Some(text[start + 1..start + 1 + end].to_string());
            }
        }
    }

    // Look for enum-like values: State.Value or State::Value
    if let Some(dot_pos) = text.rfind('.').or_else(|| text.rfind("::")) {
        let value_start = if text[dot_pos..].starts_with("::") {
            dot_pos + 2
        } else {
            dot_pos + 1
        };
        let value = text[value_start..]
            .split(|c: char| !c.is_alphanumeric() && c != '_')
            .next()?
            .trim();
        if !value.is_empty() {
            return Some(value.to_string());
        }
    }

    None
}

/// Extract state value from a comparison expression.
fn extract_state_from_comparison(text: &str) -> Option<String> {
    // Look for == or === comparison with string
    if text.contains("==") || text.contains("===") {
        return extract_string_value(text);
    }
    None
}

/// Extract Rust enum variant name from a pattern.
fn extract_rust_enum_variant(text: &str, enum_name: &str) -> Option<String> {
    let pattern = format!("{}::", enum_name);
    if let Some(pos) = text.find(&pattern) {
        let start = pos + pattern.len();
        let variant = text[start..]
            .split(|c: char| !c.is_alphanumeric() && c != '_')
            .next()?
            .trim();
        if !variant.is_empty() {
            return Some(variant.to_string());
        }
    }
    None
}

/// Sanitize string for use as DOT identifier.
fn sanitize_id(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        if c.is_alphanumeric() || c == '_' {
            result.push(c);
        } else {
            result.push('_');
        }
    }
    if result.starts_with(|c: char| c.is_ascii_digit()) {
        result.insert(0, '_');
    }
    if result.is_empty() {
        result.push_str("_anonymous");
    }
    result
}

/// Escape special characters for DOT labels.
fn escape_dot(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "")
}

/// Escape special characters for Mermaid labels.
fn escape_mermaid(s: &str) -> String {
    s.replace('"', "'")
        .replace('\n', " ")
        .replace('\r', "")
        .replace('[', "(")
        .replace(']', ")")
        .replace('{', "(")
        .replace('}', ")")
}

// =============================================================================
// PUBLIC API
// =============================================================================

/// Extract state machines from a file.
///
/// This is the main entry point for state machine extraction.
///
/// # Arguments
/// * `path` - Path to the source file
///
/// # Returns
/// * `Result<Vec<StateMachine>>` - List of extracted state machines
///
/// # Example
/// ```ignore
/// let machines = extract_state_machines("src/connection.py")?;
/// for sm in machines {
///     println!("{}", sm.to_mermaid());
/// }
/// ```
pub fn extract_state_machines(path: &Path) -> Result<Vec<StateMachine>> {
    StateMachineExtractor::new().extract_from_file(path)
}

/// Extract state machines from source code string.
///
/// # Arguments
/// * `source` - Source code string
/// * `language` - Language name (e.g., "python", "rust")
/// * `file_name` - Virtual file name for location tracking
///
/// # Returns
/// * `Result<Vec<StateMachine>>` - List of extracted state machines
pub fn extract_state_machines_from_source(
    source: &str,
    language: &str,
    file_name: &str,
) -> Result<Vec<StateMachine>> {
    StateMachineExtractor::new().extract_from_source(source, language, file_name)
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_python_fsm() {
        let source = r#"
class Connection:
    def __init__(self):
        self.state = "disconnected"

    def connect(self):
        if self.state == "disconnected":
            self.state = "connecting"
            self.state = "connected"

    def disconnect(self):
        if self.state == "connected":
            self.state = "disconnected"
"#;

        let machines = extract_state_machines_from_source(source, "python", "test.py").unwrap();

        assert_eq!(machines.len(), 1, "Should find exactly one state machine");
        let sm = &machines[0];

        assert_eq!(sm.name, "Connection");
        assert_eq!(sm.state_variable, "self.state");

        // Should have 3 states: disconnected, connecting, connected
        assert!(sm.states.len() >= 3, "Should have at least 3 states");

        // Should have transitions
        assert!(!sm.transitions.is_empty(), "Should have transitions");

        // Initial state should be disconnected
        let initial = sm.get_state(sm.initial_state).unwrap();
        assert_eq!(initial.name, "disconnected");
    }

    #[test]
    fn test_rust_enum_fsm() {
        let source = r#"
enum State {
    Idle,
    Running,
    Paused,
    Stopped,
}

impl Machine {
    fn handle_event(&mut self, event: Event) {
        match self.state {
            State::Idle => {
                self.state = State::Running;
            }
            State::Running => {
                self.state = State::Paused;
            }
            State::Paused => {
                self.state = State::Stopped;
            }
            _ => {}
        }
    }
}
"#;

        let machines = extract_state_machines_from_source(source, "rust", "test.rs").unwrap();

        assert!(!machines.is_empty(), "Should find state machine");
        let sm = &machines[0];

        assert_eq!(sm.name, "State");

        // Should have 4 states
        assert_eq!(sm.states.len(), 4, "Should have 4 states");
    }

    #[test]
    fn test_typescript_fsm() {
        let source = r#"
class TrafficLight {
    constructor() {
        this.state = "red";
    }

    next() {
        if (this.state === "red") {
            this.state = "green";
        } else if (this.state === "green") {
            this.state = "yellow";
        } else if (this.state === "yellow") {
            this.state = "red";
        }
    }
}
"#;

        let machines = extract_state_machines_from_source(source, "typescript", "test.ts").unwrap();

        assert_eq!(machines.len(), 1, "Should find exactly one state machine");
        let sm = &machines[0];

        assert_eq!(sm.name, "TrafficLight");

        // Should have 3 states: red, green, yellow
        assert_eq!(sm.states.len(), 3, "Should have 3 states");

        // Should have 3 transitions forming a cycle
        assert_eq!(sm.transitions.len(), 3, "Should have 3 transitions");
    }

    #[test]
    fn test_validation_unreachable_states() {
        let mut sm = StateMachine::new(
            "Test",
            "state",
            Location {
                file: "test.py".to_string(),
                start_line: 1,
                end_line: 10,
                start_col: 0,
                end_col: 0,
            },
        );

        let idle_id = sm.get_or_create_state("idle");
        let running_id = sm.get_or_create_state("running");
        let _unreachable_id = sm.get_or_create_state("unreachable");

        sm.initial_state = idle_id;
        sm.add_transition(Transition::new(idle_id, running_id, "start"));

        let result = sm.validate();

        assert!(!result.issues.is_empty(), "Should have validation issues");
        assert!(
            result
                .issues
                .iter()
                .any(|i| i.issue_type == "unreachable_state"),
            "Should detect unreachable state"
        );
    }

    #[test]
    fn test_validation_dead_end_states() {
        let mut sm = StateMachine::new(
            "Test",
            "state",
            Location {
                file: "test.py".to_string(),
                start_line: 1,
                end_line: 10,
                start_col: 0,
                end_col: 0,
            },
        );

        let idle_id = sm.get_or_create_state("idle");
        let dead_end_id = sm.get_or_create_state("dead_end");

        sm.initial_state = idle_id;
        sm.add_transition(Transition::new(idle_id, dead_end_id, "go"));
        // dead_end has no outgoing transitions and is not final

        let result = sm.validate();

        assert!(
            result
                .issues
                .iter()
                .any(|i| i.issue_type == "dead_end_state"),
            "Should detect dead-end state"
        );
    }

    #[test]
    fn test_validation_non_deterministic() {
        let mut sm = StateMachine::new(
            "Test",
            "state",
            Location {
                file: "test.py".to_string(),
                start_line: 1,
                end_line: 10,
                start_col: 0,
                end_col: 0,
            },
        );

        let idle_id = sm.get_or_create_state("idle");
        let state_a = sm.get_or_create_state("state_a");
        let state_b = sm.get_or_create_state("state_b");

        sm.initial_state = idle_id;
        // Two transitions with same trigger from idle
        sm.add_transition(Transition::new(idle_id, state_a, "go"));
        sm.add_transition(Transition::new(idle_id, state_b, "go"));

        let result = sm.validate();

        assert!(!result.is_valid, "Should be invalid");
        assert!(
            result
                .issues
                .iter()
                .any(|i| i.issue_type == "non_deterministic"),
            "Should detect non-deterministic transitions"
        );
    }

    #[test]
    fn test_mermaid_output() {
        let mut sm = StateMachine::new(
            "Test",
            "state",
            Location {
                file: "test.py".to_string(),
                start_line: 1,
                end_line: 10,
                start_col: 0,
                end_col: 0,
            },
        );

        let idle_id = sm.get_or_create_state("idle");
        let running_id = sm.get_or_create_state("running");

        sm.initial_state = idle_id;
        sm.add_transition(Transition::new(idle_id, running_id, "start"));

        let mermaid = sm.to_mermaid();

        assert!(mermaid.contains("stateDiagram-v2"));
        assert!(mermaid.contains("[*] --> idle"));
        assert!(mermaid.contains("idle --> running"));
    }

    #[test]
    fn test_dot_output() {
        let mut sm = StateMachine::new(
            "Test",
            "state",
            Location {
                file: "test.py".to_string(),
                start_line: 1,
                end_line: 10,
                start_col: 0,
                end_col: 0,
            },
        );

        let idle_id = sm.get_or_create_state("idle");
        let running_id = sm.get_or_create_state("running");

        sm.initial_state = idle_id;
        sm.add_transition(Transition::new(idle_id, running_id, "start"));

        let dot = sm.to_dot();

        assert!(dot.contains("digraph Test"));
        assert!(dot.contains("idle"));
        assert!(dot.contains("running"));
        assert!(dot.contains("->"));
    }

    #[test]
    fn test_plantuml_output() {
        let mut sm = StateMachine::new(
            "Test",
            "state",
            Location {
                file: "test.py".to_string(),
                start_line: 1,
                end_line: 10,
                start_col: 0,
                end_col: 0,
            },
        );

        let idle_id = sm.get_or_create_state("idle");
        let running_id = sm.get_or_create_state("running");

        sm.initial_state = idle_id;
        sm.add_transition(Transition::new(idle_id, running_id, "start"));

        let puml = sm.to_plantuml();

        assert!(puml.contains("@startuml"));
        assert!(puml.contains("@enduml"));
        assert!(puml.contains("[*] --> idle"));
        assert!(puml.contains("idle --> running"));
    }

    #[test]
    fn test_json_output() {
        let mut sm = StateMachine::new(
            "Test",
            "state",
            Location {
                file: "test.py".to_string(),
                start_line: 1,
                end_line: 10,
                start_col: 0,
                end_col: 0,
            },
        );

        let idle_id = sm.get_or_create_state("idle");
        let running_id = sm.get_or_create_state("running");

        sm.initial_state = idle_id;
        sm.add_transition(Transition::new(idle_id, running_id, "start"));

        let json = sm.to_json().unwrap();

        assert!(json.contains("\"name\": \"Test\""));
        assert!(json.contains("\"states\""));
        assert!(json.contains("\"transitions\""));
    }

    #[test]
    fn test_multiple_fsms_in_file() {
        let source = r#"
class Connection:
    def __init__(self):
        self.state = "disconnected"

    def connect(self):
        if self.state == "disconnected":
            self.state = "connected"

class Player:
    def __init__(self):
        self.status = "idle"

    def play(self):
        if self.status == "idle":
            self.status = "playing"

    def stop(self):
        if self.status == "playing":
            self.status = "idle"
"#;

        let machines = extract_state_machines_from_source(source, "python", "test.py").unwrap();

        assert_eq!(machines.len(), 2, "Should find two state machines");

        let names: Vec<_> = machines.iter().map(|m| m.name.as_str()).collect();
        assert!(names.contains(&"Connection"));
        assert!(names.contains(&"Player"));
    }

    #[test]
    fn test_guard_with_transitions() {
        let source = r#"
class Door:
    def __init__(self):
        self.state = "closed"

    def open(self, has_key):
        if self.state == "closed":
            if has_key:
                self.state = "open"

    def close(self):
        if self.state == "open":
            self.state = "closed"
"#;

        let machines = extract_state_machines_from_source(source, "python", "test.py").unwrap();

        assert_eq!(machines.len(), 1);
        let sm = &machines[0];

        // Should detect states
        assert!(sm.states.len() >= 2);
    }

    #[test]
    fn test_output_format_parsing() {
        assert_eq!("dot".parse::<OutputFormat>().unwrap(), OutputFormat::Dot);
        assert_eq!(
            "mermaid".parse::<OutputFormat>().unwrap(),
            OutputFormat::Mermaid
        );
        assert_eq!("json".parse::<OutputFormat>().unwrap(), OutputFormat::Json);
        assert_eq!(
            "plantuml".parse::<OutputFormat>().unwrap(),
            OutputFormat::PlantUml
        );
        assert_eq!(
            "puml".parse::<OutputFormat>().unwrap(),
            OutputFormat::PlantUml
        );

        assert!("invalid".parse::<OutputFormat>().is_err());
    }
}
