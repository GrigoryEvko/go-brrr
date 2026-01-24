//! Design pattern detection module.
//!
//! Detects common design patterns in source code using AST analysis and heuristics.
//!
//! # Supported Patterns
//!
//! **Creational:**
//! - **Singleton**: Private constructor, static instance, `getInstance()`
//! - **Factory**: Methods returning interface types, `*Factory` naming, `create*` methods
//! - **Builder**: Method chaining (`return self`), `build()` method
//!
//! **Structural:**
//! - **Adapter**: Wraps another class, implements interface
//! - **Decorator**: Wraps same interface, delegates to wrapped object
//! - **Proxy**: Same interface as subject, controls access
//!
//! **Behavioral:**
//! - **Observer**: Subscribe/notify pattern, listener collections
//! - **Strategy**: Interface with multiple implementations, injected via constructor
//! - **Command**: `execute()` method, encapsulates action
//!
//! # Language Considerations
//!
//! The detector accounts for language-specific idioms:
//! - **Python**: `__new__` for singleton, no explicit interfaces
//! - **Rust**: Traits for interfaces, no classes
//! - **Go**: Implicit interfaces, struct embedding
//! - **Java/TypeScript**: Standard OOP patterns
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::patterns::{detect_patterns, PatternConfig, DesignPattern};
//!
//! let result = detect_patterns("./src", None, None)?;
//! for pattern_match in &result.patterns {
//!     println!("{}: {} (confidence: {:.1}%)",
//!         pattern_match.pattern.name(),
//!         pattern_match.primary_location().map(|l| l.file.display().to_string())
//!             .unwrap_or_default(),
//!         pattern_match.confidence * 100.0);
//! }
//! ```

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use fxhash::FxHashMap;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use tracing::{debug, trace};

use crate::ast::{ClassInfo, FunctionInfo, ModuleInfo};
use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::Result;
use crate::lang::LanguageRegistry;

// =============================================================================
// DESIGN PATTERN TYPES
// =============================================================================

/// Categories of design patterns.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PatternCategory {
    /// Patterns dealing with object creation mechanisms.
    Creational,
    /// Patterns dealing with object composition.
    Structural,
    /// Patterns dealing with object interaction.
    Behavioral,
}

impl std::fmt::Display for PatternCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Creational => write!(f, "Creational"),
            Self::Structural => write!(f, "Structural"),
            Self::Behavioral => write!(f, "Behavioral"),
        }
    }
}

/// Detected design pattern with associated metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum DesignPattern {
    /// Singleton pattern: ensures a class has only one instance.
    ///
    /// Heuristics:
    /// - Private/protected constructor
    /// - Static instance field
    /// - Static getter method (getInstance, instance, shared, etc.)
    Singleton {
        /// The singleton class name.
        class: String,
        /// Method name for getting the instance.
        instance_method: String,
        /// Instance field name (if detected).
        instance_field: Option<String>,
        /// Whether constructor is private.
        private_constructor: bool,
    },

    /// Factory pattern: creates objects without specifying exact class.
    ///
    /// Heuristics:
    /// - Method returns interface/abstract type
    /// - Creates different concrete types based on input
    /// - Named *Factory or has create* methods
    Factory {
        /// The factory class name.
        class: String,
        /// Factory method name(s).
        create_methods: Vec<String>,
        /// Product types that can be created.
        products: Vec<String>,
        /// Whether it's an abstract factory.
        is_abstract: bool,
    },

    /// Builder pattern: constructs complex objects step by step.
    ///
    /// Heuristics:
    /// - Method chaining (methods return self/Self)
    /// - Has build() or create() method
    /// - Setter-like methods
    Builder {
        /// The builder class name.
        class: String,
        /// The build/create method name.
        build_method: String,
        /// Setter/configuration methods.
        setters: Vec<String>,
        /// Target type being built (if detected).
        target_type: Option<String>,
    },

    /// Adapter pattern: allows incompatible interfaces to work together.
    ///
    /// Heuristics:
    /// - Wraps another class
    /// - Implements different interface than wrapped class
    /// - Delegates to wrapped object
    Adapter {
        /// The adapter class name.
        class: String,
        /// The adapted (wrapped) class.
        adaptee: String,
        /// Interface being adapted to.
        target_interface: Option<String>,
    },

    /// Decorator pattern: adds behavior to objects dynamically.
    ///
    /// Heuristics:
    /// - Implements same interface as decorated object
    /// - Has reference to decorated object
    /// - Delegates most calls to decorated object
    Decorator {
        /// The decorator class name.
        class: String,
        /// Base interface/class being decorated.
        base_interface: String,
        /// The decorated component field.
        component_field: Option<String>,
    },

    /// Proxy pattern: provides a surrogate for another object.
    ///
    /// Heuristics:
    /// - Same interface as real subject
    /// - Controls access to real subject
    /// - May add lazy loading, access control, logging
    Proxy {
        /// The proxy class name.
        class: String,
        /// The real subject class.
        subject: String,
        /// Type of proxy (lazy, protection, remote, etc.).
        proxy_type: Option<String>,
    },

    /// Observer pattern: defines one-to-many dependency.
    ///
    /// Heuristics:
    /// - Has collection of listeners/observers
    /// - Methods like add/remove/notify
    /// - Callback invocation pattern
    Observer {
        /// The subject (observable) class.
        subject: String,
        /// Observer interface or types.
        observers: Vec<String>,
        /// Method for notifying observers.
        notify_method: String,
        /// Methods for subscribing/unsubscribing.
        subscribe_methods: Vec<String>,
    },

    /// Strategy pattern: defines family of interchangeable algorithms.
    ///
    /// Heuristics:
    /// - Interface with multiple implementations
    /// - Strategy injected via constructor or setter
    /// - Context class uses strategy
    Strategy {
        /// The strategy interface name.
        interface: String,
        /// Concrete strategy implementations.
        implementations: Vec<String>,
        /// Context class using the strategy.
        context: Option<String>,
    },

    /// Command pattern: encapsulates request as an object.
    ///
    /// Heuristics:
    /// - Has execute() or similar method
    /// - Encapsulates all info needed for action
    /// - Often with undo() support
    Command {
        /// The command interface name.
        interface: String,
        /// Concrete command implementations.
        commands: Vec<String>,
        /// Execute method name.
        execute_method: String,
        /// Whether undo is supported.
        has_undo: bool,
    },

    /// Dependency Injection pattern (modern alternative to many patterns).
    ///
    /// Heuristics:
    /// - Dependencies passed via constructor
    /// - Interface-typed parameters
    /// - No internal instantiation of dependencies
    DependencyInjection {
        /// Class using dependency injection.
        class: String,
        /// Injected dependencies (field name -> type).
        dependencies: Vec<(String, String)>,
    },

    /// Repository pattern: abstracts data access logic.
    ///
    /// Heuristics:
    /// - Named *Repository
    /// - Has CRUD-like methods (find, save, delete)
    /// - Works with entity types
    Repository {
        /// The repository class name.
        class: String,
        /// Entity type managed.
        entity_type: Option<String>,
        /// CRUD methods present.
        methods: Vec<String>,
    },
}

impl DesignPattern {
    /// Get the human-readable name of the pattern.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::Singleton { .. } => "Singleton",
            Self::Factory { .. } => "Factory",
            Self::Builder { .. } => "Builder",
            Self::Adapter { .. } => "Adapter",
            Self::Decorator { .. } => "Decorator",
            Self::Proxy { .. } => "Proxy",
            Self::Observer { .. } => "Observer",
            Self::Strategy { .. } => "Strategy",
            Self::Command { .. } => "Command",
            Self::DependencyInjection { .. } => "Dependency Injection",
            Self::Repository { .. } => "Repository",
        }
    }

    /// Get the category of this pattern.
    #[must_use]
    pub fn category(&self) -> PatternCategory {
        match self {
            Self::Singleton { .. } | Self::Factory { .. } | Self::Builder { .. } => {
                PatternCategory::Creational
            }
            Self::Adapter { .. } | Self::Decorator { .. } | Self::Proxy { .. } => {
                PatternCategory::Structural
            }
            Self::Observer { .. }
            | Self::Strategy { .. }
            | Self::Command { .. }
            | Self::DependencyInjection { .. }
            | Self::Repository { .. } => PatternCategory::Behavioral,
        }
    }

    /// Get the primary class/type name associated with this pattern.
    #[must_use]
    pub fn primary_class(&self) -> &str {
        match self {
            Self::Singleton { class, .. }
            | Self::Factory { class, .. }
            | Self::Builder { class, .. }
            | Self::Adapter { class, .. }
            | Self::Decorator { class, .. }
            | Self::Proxy { class, .. }
            | Self::Observer { subject: class, .. }
            | Self::DependencyInjection { class, .. }
            | Self::Repository { class, .. } => class,
            Self::Strategy { interface, .. } | Self::Command { interface, .. } => interface,
        }
    }
}

/// Source code location for a pattern element.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Location {
    /// File containing the pattern element.
    pub file: PathBuf,
    /// Starting line number (1-indexed).
    pub line: usize,
    /// Ending line number (1-indexed, optional).
    pub end_line: Option<usize>,
    /// Element name (class, method, etc.).
    pub name: String,
    /// Element kind (class, method, field, etc.).
    pub kind: String,
}

impl Location {
    /// Create a new location for a class.
    #[must_use]
    pub fn for_class(file: PathBuf, class: &ClassInfo) -> Self {
        Self {
            file,
            line: class.line_number,
            end_line: class.end_line_number,
            name: class.name.clone(),
            kind: "class".to_string(),
        }
    }

    /// Create a new location for a function.
    #[must_use]
    pub fn for_function(file: PathBuf, func: &FunctionInfo) -> Self {
        Self {
            file,
            line: func.line_number,
            end_line: func.end_line_number,
            name: func.name.clone(),
            kind: if func.is_method { "method" } else { "function" }.to_string(),
        }
    }
}

/// A detected pattern match with confidence score.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PatternMatch {
    /// The detected pattern.
    pub pattern: DesignPattern,
    /// Confidence score (0.0 to 1.0).
    /// - 1.0: Very high confidence (explicit implementation)
    /// - 0.7-0.9: High confidence (strong heuristic match)
    /// - 0.5-0.7: Medium confidence (partial match)
    /// - 0.3-0.5: Low confidence (weak signals)
    pub confidence: f64,
    /// Locations of pattern elements.
    pub locations: Vec<Location>,
    /// Additional notes about the detection.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
    /// Evidence supporting the detection.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub evidence: Vec<String>,
}

impl PatternMatch {
    /// Create a new pattern match.
    #[must_use]
    pub fn new(pattern: DesignPattern, confidence: f64) -> Self {
        Self {
            pattern,
            confidence,
            locations: Vec::new(),
            note: None,
            evidence: Vec::new(),
        }
    }

    /// Add a location to this match.
    #[must_use]
    pub fn with_location(mut self, location: Location) -> Self {
        self.locations.push(location);
        self
    }

    /// Add multiple locations.
    #[must_use]
    pub fn with_locations(mut self, locations: Vec<Location>) -> Self {
        self.locations.extend(locations);
        self
    }

    /// Add a note about the detection.
    #[must_use]
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.note = Some(note.into());
        self
    }

    /// Add evidence supporting the detection.
    #[must_use]
    pub fn with_evidence(mut self, evidence: Vec<String>) -> Self {
        self.evidence = evidence;
        self
    }

    /// Get the primary location (first location if any).
    #[must_use]
    pub fn primary_location(&self) -> Option<&Location> {
        self.locations.first()
    }
}

// =============================================================================
// CONFIGURATION
// =============================================================================

/// Configuration for pattern detection.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PatternConfig {
    /// Minimum confidence threshold for reporting patterns.
    /// Default: 0.5 (medium confidence).
    pub min_confidence: f64,

    /// Patterns to detect (empty = all patterns).
    pub patterns: Vec<String>,

    /// Language filter (None = auto-detect).
    pub language: Option<String>,

    /// Maximum file size to process (bytes).
    pub max_file_size: u64,

    /// Include test files in detection.
    pub include_tests: bool,

    /// Include generated code in detection.
    pub include_generated: bool,

    /// Detect modern patterns (DI, Repository).
    pub detect_modern_patterns: bool,

    /// Language-specific pattern detection.
    pub language_specific: bool,
}

impl Default for PatternConfig {
    fn default() -> Self {
        Self {
            min_confidence: 0.5,
            patterns: Vec::new(),
            language: None,
            max_file_size: 1024 * 1024, // 1MB
            include_tests: false,
            include_generated: false,
            detect_modern_patterns: true,
            language_specific: true,
        }
    }
}

impl PatternConfig {
    /// Create a configuration for a specific pattern.
    #[must_use]
    pub fn for_pattern(pattern: impl Into<String>) -> Self {
        Self {
            patterns: vec![pattern.into()],
            ..Default::default()
        }
    }

    /// Set minimum confidence threshold.
    #[must_use]
    pub fn with_min_confidence(mut self, confidence: f64) -> Self {
        self.min_confidence = confidence.clamp(0.0, 1.0);
        self
    }

    /// Set language filter.
    #[must_use]
    pub fn with_language(mut self, lang: impl Into<String>) -> Self {
        self.language = Some(lang.into());
        self
    }

    /// Enable/disable modern pattern detection.
    #[must_use]
    pub fn with_modern_patterns(mut self, enable: bool) -> Self {
        self.detect_modern_patterns = enable;
        self
    }
}

// =============================================================================
// STATISTICS
// =============================================================================

/// Statistics about pattern detection.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PatternStats {
    /// Total files scanned.
    pub files_scanned: usize,
    /// Files with patterns detected.
    pub files_with_patterns: usize,
    /// Total patterns detected.
    pub patterns_detected: usize,
    /// Patterns by category.
    pub by_category: HashMap<String, usize>,
    /// Patterns by type.
    pub by_type: HashMap<String, usize>,
    /// Average confidence of detections.
    pub average_confidence: f64,
    /// Files skipped (size/exclusion).
    pub files_skipped: usize,
}

// =============================================================================
// ANALYSIS RESULT
// =============================================================================

/// Result of pattern detection analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PatternAnalysis {
    /// Path analyzed.
    pub path: PathBuf,
    /// Detected patterns.
    pub patterns: Vec<PatternMatch>,
    /// Detection statistics.
    pub stats: PatternStats,
    /// Errors encountered (non-fatal).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<String>,
}

impl PatternAnalysis {
    /// Create a new analysis result.
    #[must_use]
    pub fn new(path: PathBuf) -> Self {
        Self {
            path,
            patterns: Vec::new(),
            stats: PatternStats::default(),
            errors: Vec::new(),
        }
    }

    /// Get patterns of a specific type.
    #[must_use]
    pub fn patterns_of_type(&self, pattern_name: &str) -> Vec<&PatternMatch> {
        self.patterns
            .iter()
            .filter(|p| p.pattern.name().eq_ignore_ascii_case(pattern_name))
            .collect()
    }

    /// Get patterns in a category.
    #[must_use]
    pub fn patterns_in_category(&self, category: PatternCategory) -> Vec<&PatternMatch> {
        self.patterns
            .iter()
            .filter(|p| p.pattern.category() == category)
            .collect()
    }

    /// Get high-confidence patterns (>= 0.7).
    #[must_use]
    pub fn high_confidence_patterns(&self) -> Vec<&PatternMatch> {
        self.patterns
            .iter()
            .filter(|p| p.confidence >= 0.7)
            .collect()
    }
}

// =============================================================================
// ERROR TYPE
// =============================================================================

/// Error during pattern detection.
#[derive(Debug, Clone, thiserror::Error)]
pub enum PatternError {
    /// Failed to scan project files.
    #[error("Failed to scan project: {0}")]
    ScanError(String),

    /// Failed to parse a file.
    #[error("Failed to parse file {path}: {message}")]
    ParseError { path: PathBuf, message: String },

    /// Invalid configuration.
    #[error("Invalid configuration: {0}")]
    ConfigError(String),

    /// IO error.
    #[error("IO error: {0}")]
    IoError(String),
}

impl From<std::io::Error> for PatternError {
    fn from(e: std::io::Error) -> Self {
        Self::IoError(e.to_string())
    }
}

// =============================================================================
// PATTERN DETECTOR
// =============================================================================

/// Design pattern detector using AST analysis.
pub struct PatternDetector {
    config: PatternConfig,
}

impl PatternDetector {
    /// Create a new pattern detector with the given configuration.
    #[must_use]
    pub fn new(config: PatternConfig) -> Self {
        Self { config }
    }

    /// Detect patterns in a file or directory.
    pub fn detect(&self, path: impl AsRef<Path>) -> Result<PatternAnalysis> {
        let path = path.as_ref();
        let abs_path = if path.is_absolute() {
            path.to_path_buf()
        } else {
            std::env::current_dir()?.join(path)
        };

        let mut analysis = PatternAnalysis::new(abs_path.clone());

        if abs_path.is_file() {
            self.detect_in_file(&abs_path, &mut analysis)?;
        } else {
            self.detect_in_directory(&abs_path, &mut analysis)?;
        }

        // Calculate statistics.
        self.calculate_stats(&mut analysis);

        // Filter by minimum confidence.
        analysis
            .patterns
            .retain(|p| p.confidence >= self.config.min_confidence);

        // Filter by requested patterns if specified.
        if !self.config.patterns.is_empty() {
            let patterns_lower: Vec<String> = self
                .config
                .patterns
                .iter()
                .map(|p| p.to_lowercase())
                .collect();
            analysis.patterns.retain(|p| {
                patterns_lower
                    .iter()
                    .any(|name| p.pattern.name().to_lowercase().contains(name))
            });
        }

        // Sort by confidence (highest first).
        analysis.patterns.sort_by(|a, b| {
            b.confidence
                .partial_cmp(&a.confidence)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        Ok(analysis)
    }

    /// Detect patterns in a directory.
    fn detect_in_directory(&self, path: &Path, analysis: &mut PatternAnalysis) -> Result<()> {
        let path_str = path.to_str().ok_or_else(|| {
            crate::error::BrrrError::InvalidArgument("Invalid path encoding".to_string())
        })?;

        let scanner = ProjectScanner::new(path_str)?;

        let scan_config = if let Some(ref lang) = self.config.language {
            ScanConfig::for_language(lang)
        } else {
            ScanConfig::default()
        };

        let scan_result = scanner.scan_with_config(&scan_config)?;

        let patterns: Mutex<Vec<PatternMatch>> = Mutex::new(Vec::new());
        let errors: Mutex<Vec<String>> = Mutex::new(Vec::new());
        let files_scanned: Mutex<usize> = Mutex::new(0);
        let files_skipped: Mutex<usize> = Mutex::new(0);

        scan_result.files.par_iter().for_each(|file| {
            // Skip based on size (if metadata was collected).
            if !scan_result.metadata.is_empty() {
                if let Some(file_meta) = scan_result.metadata.iter().find(|m| m.path == *file) {
                    if file_meta.size > self.config.max_file_size {
                        let mut skipped = files_skipped.lock().unwrap();
                        *skipped += 1;
                        return;
                    }
                }
            }

            // Skip test files if configured.
            if !self.config.include_tests && is_test_file(file) {
                let mut skipped = files_skipped.lock().unwrap();
                *skipped += 1;
                return;
            }

            // Skip generated files if configured.
            if !self.config.include_generated && is_generated_file(file) {
                let mut skipped = files_skipped.lock().unwrap();
                *skipped += 1;
                return;
            }

            let mut file_analysis = PatternAnalysis::new(file.clone());
            match self.detect_in_file(file, &mut file_analysis) {
                Ok(()) => {
                    let mut p = patterns.lock().unwrap();
                    p.extend(file_analysis.patterns);
                    let mut scanned = files_scanned.lock().unwrap();
                    *scanned += 1;
                }
                Err(e) => {
                    let mut errs = errors.lock().unwrap();
                    errs.push(format!("{}: {}", file.display(), e));
                }
            }
        });

        analysis.patterns = patterns.into_inner().unwrap();
        analysis.errors = errors.into_inner().unwrap();
        analysis.stats.files_scanned = *files_scanned.lock().unwrap();
        analysis.stats.files_skipped = *files_skipped.lock().unwrap();

        Ok(())
    }

    /// Detect patterns in a single file.
    fn detect_in_file(&self, path: &Path, analysis: &mut PatternAnalysis) -> Result<()> {
        let registry = LanguageRegistry::global();
        let lang = registry.detect_language(path).or_else(|| {
            self.config
                .language
                .as_ref()
                .and_then(|l| registry.get_by_name(l))
        });

        if lang.is_none() {
            trace!("Unsupported language for file: {}", path.display());
            return Ok(());
        }

        // Extract module info using AST.
        let module = match crate::ast::AstExtractor::extract_file(path) {
            Ok(m) => m,
            Err(e) => {
                debug!("Failed to extract AST from {}: {}", path.display(), e);
                return Ok(());
            }
        };

        // Detect patterns in the module.
        self.detect_in_module(&module, path, analysis);

        Ok(())
    }

    /// Detect patterns in a parsed module.
    fn detect_in_module(&self, module: &ModuleInfo, path: &Path, analysis: &mut PatternAnalysis) {
        let lang = module.language.as_str();

        // Detect Singleton pattern.
        for class in &module.classes {
            if let Some(pattern_match) = self.detect_singleton(class, path, lang) {
                analysis.patterns.push(pattern_match);
            }

            // Detect Builder pattern.
            if let Some(pattern_match) = self.detect_builder(class, path, lang) {
                analysis.patterns.push(pattern_match);
            }

            // Detect Factory pattern.
            if let Some(pattern_match) = self.detect_factory(class, &module.classes, path, lang) {
                analysis.patterns.push(pattern_match);
            }

            // Detect Observer pattern.
            if let Some(pattern_match) = self.detect_observer(class, path, lang) {
                analysis.patterns.push(pattern_match);
            }

            // Detect Decorator pattern.
            if let Some(pattern_match) = self.detect_decorator(class, &module.classes, path, lang) {
                analysis.patterns.push(pattern_match);
            }

            // Detect Adapter pattern.
            if let Some(pattern_match) = self.detect_adapter(class, path, lang) {
                analysis.patterns.push(pattern_match);
            }

            // Detect Proxy pattern.
            if let Some(pattern_match) = self.detect_proxy(class, path, lang) {
                analysis.patterns.push(pattern_match);
            }

            // Detect Command pattern.
            if let Some(pattern_match) = self.detect_command(class, &module.classes, path, lang) {
                analysis.patterns.push(pattern_match);
            }

            // Detect modern patterns.
            if self.config.detect_modern_patterns {
                // Detect Dependency Injection.
                if let Some(pattern_match) = self.detect_dependency_injection(class, path, lang) {
                    analysis.patterns.push(pattern_match);
                }

                // Detect Repository pattern.
                if let Some(pattern_match) = self.detect_repository(class, path, lang) {
                    analysis.patterns.push(pattern_match);
                }
            }
        }

        // Detect Strategy pattern (needs interface analysis across classes).
        let strategies = self.detect_strategy(&module.classes, path, lang);
        analysis.patterns.extend(strategies);
    }

    /// Detect Singleton pattern.
    fn detect_singleton(&self, class: &ClassInfo, path: &Path, lang: &str) -> Option<PatternMatch> {
        let mut confidence: f64 = 0.0;
        let mut evidence = Vec::new();
        let mut instance_method = String::new();
        let mut instance_field = None;
        let mut private_constructor = false;

        let class_name_lower = class.name.to_lowercase();

        // Check for singleton naming patterns.
        if class_name_lower.contains("singleton") {
            confidence += 0.3;
            evidence.push("Class name contains 'singleton'".to_string());
        }

        // Check for private constructor.
        let private_ctor = class.methods.iter().find(|m| {
            let name = m.name.to_lowercase();
            (name == "__init__"
                || name == "new"
                || name == class_name_lower
                || name == "init"
                || name == "constructor")
                && m.decorators.iter().any(|d| d.contains("private"))
                || matches!(lang, "java" | "typescript" | "csharp")
                    && !m
                        .params
                        .iter()
                        .any(|p| !p.contains("self") && !p.contains("this"))
        });

        // Check for Python __new__ singleton pattern.
        let python_new = class.methods.iter().find(|m| m.name == "__new__");
        if python_new.is_some() && lang == "python" {
            confidence += 0.2;
            evidence.push("Has __new__ method (Python singleton idiom)".to_string());
        }

        if private_ctor.is_some() {
            confidence += 0.2;
            evidence.push("Has private constructor".to_string());
            private_constructor = true;
        }

        // Check for static instance field.
        let instance_field_names = [
            "_instance",
            "instance",
            "_singleton",
            "singleton",
            "INSTANCE",
            "_INSTANCE",
            "shared",
            "sharedInstance",
        ];
        for field in &class.fields {
            if instance_field_names
                .iter()
                .any(|n| field.name.eq_ignore_ascii_case(n))
            {
                if field.is_static {
                    confidence += 0.25;
                    evidence.push(format!("Has static instance field: {}", field.name));
                    instance_field = Some(field.name.clone());
                } else {
                    confidence += 0.1;
                    evidence.push(format!("Has instance field (non-static): {}", field.name));
                    instance_field = Some(field.name.clone());
                }
            }
        }

        // Check for getInstance() or similar method.
        let getter_patterns = [
            "getinstance",
            "get_instance",
            "instance",
            "shared",
            "sharedinstance",
            "default",
            "current",
            "singleton",
        ];
        for method in &class.methods {
            let method_lower = method.name.to_lowercase();
            if getter_patterns
                .iter()
                .any(|p| method_lower == *p || method_lower.contains(p))
            {
                // Check if it returns the class type or has static marker.
                let is_static = method
                    .decorators
                    .iter()
                    .any(|d| d.contains("static") || d.contains("classmethod"))
                    || !method.params.iter().any(|p| p.contains("self"));

                if is_static {
                    confidence += 0.3;
                    evidence.push(format!("Has static getter method: {}", method.name));
                    instance_method = method.name.clone();
                } else {
                    confidence += 0.1;
                    evidence.push(format!("Has getter method (non-static): {}", method.name));
                    if instance_method.is_empty() {
                        instance_method = method.name.clone();
                    }
                }
            }
        }

        // Rust-specific: Check for lazy_static or once_cell patterns.
        if lang == "rust" {
            for field in &class.fields {
                let field_type = field.field_type.as_deref().unwrap_or("");
                if field_type.contains("Lazy")
                    || field_type.contains("OnceCell")
                    || field_type.contains("LazyLock")
                {
                    confidence += 0.3;
                    evidence.push(format!("Uses lazy initialization: {}", field_type));
                }
            }
        }

        if confidence >= 0.4 {
            if instance_method.is_empty() {
                instance_method = "getInstance".to_string();
            }

            let pattern = DesignPattern::Singleton {
                class: class.name.clone(),
                instance_method,
                instance_field,
                private_constructor,
            };

            let note = if confidence < 0.7 {
                Some("Partial singleton implementation detected".to_string())
            } else {
                None
            };

            Some(
                PatternMatch::new(pattern, confidence.min(1.0))
                    .with_location(Location::for_class(path.to_path_buf(), class))
                    .with_note(note.unwrap_or_default())
                    .with_evidence(evidence),
            )
        } else {
            None
        }
    }

    /// Detect Builder pattern.
    fn detect_builder(&self, class: &ClassInfo, path: &Path, _lang: &str) -> Option<PatternMatch> {
        let mut confidence: f64 = 0.0;
        let mut evidence = Vec::new();
        let mut build_method = String::new();
        let mut setters = Vec::new();
        let mut target_type = None;

        let class_name_lower = class.name.to_lowercase();

        // Check for builder naming.
        if class_name_lower.ends_with("builder") {
            confidence += 0.35;
            evidence.push("Class name ends with 'Builder'".to_string());
            // Infer target type from class name.
            let target = class
                .name
                .strip_suffix("Builder")
                .or_else(|| class.name.strip_suffix("builder"));
            if let Some(t) = target {
                if !t.is_empty() {
                    target_type = Some(t.to_string());
                }
            }
        }

        // Check for build() method.
        let build_methods = [
            "build",
            "create",
            "make",
            "construct",
            "get_result",
            "getResult",
        ];
        for method in &class.methods {
            let method_lower = method.name.to_lowercase();
            if build_methods.iter().any(|b| method_lower == *b) {
                confidence += 0.25;
                evidence.push(format!("Has build method: {}", method.name));
                build_method = method.name.clone();

                // Check return type for target type.
                if let Some(ref ret) = method.return_type {
                    if !ret.contains("Self") && !ret.contains(&class.name) {
                        target_type = Some(ret.clone());
                    }
                }
            }
        }

        // Check for fluent setter methods (return Self).
        let setter_prefixes = ["with_", "set_", "add_", "set", "with", "add"];
        for method in &class.methods {
            let method_lower = method.name.to_lowercase();
            let is_setter = setter_prefixes.iter().any(|p| method_lower.starts_with(p));

            // Check if method returns Self (fluent interface).
            let returns_self = method
                .return_type
                .as_ref()
                .map(|r| r.contains("Self") || r.contains(&class.name) || r == "&mut Self")
                .unwrap_or(false);

            if is_setter && returns_self {
                confidence += 0.05;
                setters.push(method.name.clone());
            } else if is_setter {
                // Non-fluent setter still counts.
                setters.push(method.name.clone());
            }
        }

        // Bonus for multiple fluent setters.
        if setters.len() >= 3 {
            confidence += 0.15;
            evidence.push(format!(
                "Has {} setter/configuration methods",
                setters.len()
            ));
        }

        // Check for step builder pattern (interfaces).
        if class
            .bases
            .iter()
            .any(|b| b.to_lowercase().contains("step"))
        {
            confidence += 0.1;
            evidence.push("Implements step builder interface".to_string());
        }

        if confidence >= 0.4 && !setters.is_empty() {
            if build_method.is_empty() {
                build_method = "build".to_string();
            }

            let pattern = DesignPattern::Builder {
                class: class.name.clone(),
                build_method,
                setters,
                target_type,
            };

            Some(
                PatternMatch::new(pattern, confidence.min(1.0))
                    .with_location(Location::for_class(path.to_path_buf(), class))
                    .with_evidence(evidence),
            )
        } else {
            None
        }
    }

    /// Detect Factory pattern.
    fn detect_factory(
        &self,
        class: &ClassInfo,
        all_classes: &[ClassInfo],
        path: &Path,
        _lang: &str,
    ) -> Option<PatternMatch> {
        let mut confidence: f64 = 0.0;
        let mut evidence = Vec::new();
        let mut create_methods = Vec::new();
        let mut products = Vec::new();
        let is_abstract = class.decorators.iter().any(|d| d.contains("abstract"))
            || class
                .bases
                .iter()
                .any(|b| b.contains("ABC") || b.contains("Abstract"));

        let class_name_lower = class.name.to_lowercase();

        // Check for factory naming.
        if class_name_lower.ends_with("factory") {
            confidence += 0.35;
            evidence.push("Class name ends with 'Factory'".to_string());
        }

        // Check for create* methods.
        let factory_prefixes = [
            "create",
            "make",
            "build",
            "new",
            "get",
            "produce",
            "manufacture",
        ];
        for method in &class.methods {
            let method_lower = method.name.to_lowercase();
            if factory_prefixes.iter().any(|p| method_lower.starts_with(p)) {
                // Check if return type is abstract or interface.
                if let Some(ref ret_type) = method.return_type {
                    let ret_lower = ret_type.to_lowercase();
                    // Check if return type is a known class.
                    let returns_concrete = all_classes
                        .iter()
                        .any(|c| c.name.eq_ignore_ascii_case(ret_type));

                    if !returns_concrete
                        || ret_lower.contains("interface")
                        || ret_lower.contains("abstract")
                        || ret_lower.contains("protocol")
                    {
                        confidence += 0.15;
                        create_methods.push(method.name.clone());
                        if !products.contains(ret_type) {
                            products.push(ret_type.clone());
                        }
                    }
                }

                // Even without return type, factory-named methods count.
                if !create_methods.contains(&method.name) {
                    create_methods.push(method.name.clone());
                    confidence += 0.05;
                }
            }
        }

        evidence.push(format!("Has {} factory methods", create_methods.len()));

        // Check for abstract factory pattern (returns abstract products).
        if is_abstract && !create_methods.is_empty() {
            confidence += 0.2;
            evidence.push("Abstract factory (abstract class with factory methods)".to_string());
        }

        // Check for parameterized factory.
        let has_type_param = class.methods.iter().any(|m| {
            m.params.iter().any(|p| {
                let p_lower = p.to_lowercase();
                p_lower.contains("type") || p_lower.contains("kind") || p_lower.contains("variant")
            })
        });
        if has_type_param {
            confidence += 0.1;
            evidence.push("Has type/kind parameter (parameterized factory)".to_string());
        }

        if confidence >= 0.4 && !create_methods.is_empty() {
            let pattern = DesignPattern::Factory {
                class: class.name.clone(),
                create_methods,
                products,
                is_abstract,
            };

            Some(
                PatternMatch::new(pattern, confidence.min(1.0))
                    .with_location(Location::for_class(path.to_path_buf(), class))
                    .with_evidence(evidence),
            )
        } else {
            None
        }
    }

    /// Detect Observer pattern.
    fn detect_observer(&self, class: &ClassInfo, path: &Path, _lang: &str) -> Option<PatternMatch> {
        let mut confidence: f64 = 0.0;
        let mut evidence = Vec::new();
        let mut observers = Vec::new();
        let mut notify_method = String::new();
        let mut subscribe_methods = Vec::new();

        let class_name_lower = class.name.to_lowercase();

        // Check for observable/subject naming.
        if class_name_lower.contains("observable")
            || class_name_lower.contains("subject")
            || class_name_lower.contains("publisher")
            || class_name_lower.contains("emitter")
        {
            confidence += 0.25;
            evidence.push("Class name suggests observable pattern".to_string());
        }

        // Check for listener/observer collection fields.
        let collection_patterns = ["listener", "observer", "subscriber", "handler", "callback"];
        for field in &class.fields {
            let field_lower = field.name.to_lowercase();
            let type_lower = field
                .field_type
                .as_ref()
                .map(|t| t.to_lowercase())
                .unwrap_or_default();

            if collection_patterns.iter().any(|p| field_lower.contains(p))
                || (type_lower.contains("list")
                    || type_lower.contains("vec")
                    || type_lower.contains("set")
                    || type_lower.contains("array"))
                    && collection_patterns.iter().any(|p| type_lower.contains(p))
            {
                confidence += 0.2;
                evidence.push(format!("Has observer collection: {}", field.name));

                // Try to extract observer type.
                if let Some(ref ft) = field.field_type {
                    // Extract type from generic like List<Observer>.
                    if let Some(start) = ft.find('<') {
                        if let Some(end) = ft.find('>') {
                            let inner = &ft[start + 1..end];
                            if !observers.contains(&inner.to_string()) {
                                observers.push(inner.to_string());
                            }
                        }
                    }
                }
            }
        }

        // Check for subscribe/unsubscribe methods.
        let subscribe_patterns = ["add", "register", "subscribe", "attach", "on"];
        let unsubscribe_patterns = ["remove", "unregister", "unsubscribe", "detach", "off"];

        for method in &class.methods {
            let method_lower = method.name.to_lowercase();

            if subscribe_patterns.iter().any(|p| method_lower.contains(p))
                && collection_patterns.iter().any(|p| method_lower.contains(p))
            {
                confidence += 0.15;
                subscribe_methods.push(method.name.clone());
                evidence.push(format!("Has subscribe method: {}", method.name));
            }

            if unsubscribe_patterns
                .iter()
                .any(|p| method_lower.contains(p))
                && collection_patterns.iter().any(|p| method_lower.contains(p))
            {
                confidence += 0.1;
                subscribe_methods.push(method.name.clone());
            }
        }

        // Check for notify method.
        let notify_patterns = [
            "notify",
            "emit",
            "fire",
            "trigger",
            "dispatch",
            "publish",
            "broadcast",
        ];
        for method in &class.methods {
            let method_lower = method.name.to_lowercase();
            if notify_patterns.iter().any(|p| method_lower.contains(p)) {
                confidence += 0.2;
                evidence.push(format!("Has notify method: {}", method.name));
                notify_method = method.name.clone();
            }
        }

        if confidence >= 0.4 && !notify_method.is_empty() {
            let pattern = DesignPattern::Observer {
                subject: class.name.clone(),
                observers,
                notify_method,
                subscribe_methods,
            };

            Some(
                PatternMatch::new(pattern, confidence.min(1.0))
                    .with_location(Location::for_class(path.to_path_buf(), class))
                    .with_evidence(evidence),
            )
        } else {
            None
        }
    }

    /// Detect Decorator pattern.
    fn detect_decorator(
        &self,
        class: &ClassInfo,
        all_classes: &[ClassInfo],
        path: &Path,
        _lang: &str,
    ) -> Option<PatternMatch> {
        let mut confidence: f64 = 0.0;
        let mut evidence = Vec::new();
        let mut base_interface = String::new();
        let mut component_field = None;

        let class_name_lower = class.name.to_lowercase();

        // Check for decorator naming.
        if class_name_lower.contains("decorator") || class_name_lower.contains("wrapper") {
            confidence += 0.25;
            evidence.push("Class name suggests decorator pattern".to_string());
        }

        // Check if class implements an interface and has a field of the same interface type.
        for base in &class.bases {
            // Check if any field has the same type as a base class.
            for field in &class.fields {
                if let Some(ref field_type) = field.field_type {
                    if field_type == base || field_type.contains(base) || base.contains(field_type)
                    {
                        confidence += 0.35;
                        evidence.push(format!(
                            "Has wrapped component field: {} of type {}",
                            field.name, field_type
                        ));
                        base_interface = base.clone();
                        component_field = Some(field.name.clone());
                        break;
                    }
                }
            }

            // Check constructor parameters for component injection.
            for method in &class.methods {
                let is_ctor = method.name == "__init__"
                    || method.name == "new"
                    || method.name.to_lowercase() == class_name_lower
                    || method.name == "constructor";
                if is_ctor {
                    for param in &method.params {
                        if param.contains(base) {
                            confidence += 0.2;
                            evidence.push(format!("Constructor accepts base type: {}", base));
                        }
                    }
                }
            }
        }

        // Check for delegation (methods that call same method on wrapped object).
        // This is a heuristic based on method matching.
        if !base_interface.is_empty() {
            if let Some(base_class) = all_classes.iter().find(|c| c.name == base_interface) {
                let base_method_names: HashSet<_> =
                    base_class.methods.iter().map(|m| m.name.as_str()).collect();
                let class_method_names: HashSet<_> =
                    class.methods.iter().map(|m| m.name.as_str()).collect();

                let shared_methods: usize =
                    base_method_names.intersection(&class_method_names).count();
                if shared_methods >= 2 {
                    confidence += 0.1;
                    evidence.push(format!(
                        "Shares {} methods with base interface",
                        shared_methods
                    ));
                }
            }
        }

        if confidence >= 0.4 && !base_interface.is_empty() {
            let pattern = DesignPattern::Decorator {
                class: class.name.clone(),
                base_interface,
                component_field,
            };

            Some(
                PatternMatch::new(pattern, confidence.min(1.0))
                    .with_location(Location::for_class(path.to_path_buf(), class))
                    .with_evidence(evidence),
            )
        } else {
            None
        }
    }

    /// Detect Adapter pattern.
    fn detect_adapter(&self, class: &ClassInfo, path: &Path, _lang: &str) -> Option<PatternMatch> {
        let mut confidence: f64 = 0.0;
        let mut evidence = Vec::new();
        let mut adaptee = String::new();
        let mut target_interface = None;

        let class_name_lower = class.name.to_lowercase();

        // Check for adapter naming.
        if class_name_lower.contains("adapter") {
            confidence += 0.3;
            evidence.push("Class name contains 'Adapter'".to_string());
        }

        // Check for wrapping a different type than implemented interface.
        // Adapter: implements Interface A, wraps Class B (different from A).
        for field in &class.fields {
            if let Some(ref field_type) = field.field_type {
                let field_type_lower = field_type.to_lowercase();

                // Check if field type is different from all base classes.
                let is_different_from_bases = class
                    .bases
                    .iter()
                    .all(|b| !field_type.contains(b) && !b.contains(field_type));

                if is_different_from_bases && !class.bases.is_empty() {
                    confidence += 0.25;
                    evidence.push(format!(
                        "Wraps {} while implementing different interface",
                        field_type
                    ));
                    adaptee = field_type.clone();
                    target_interface = class.bases.first().cloned();
                }

                // Common adaptee naming patterns.
                if field_type_lower.contains("adaptee")
                    || field.name.to_lowercase().contains("adaptee")
                    || field.name.to_lowercase().contains("wrapped")
                {
                    confidence += 0.2;
                    evidence.push(format!("Has adaptee field: {}", field.name));
                    adaptee = field_type.clone();
                }
            }
        }

        if confidence >= 0.4 && !adaptee.is_empty() {
            let pattern = DesignPattern::Adapter {
                class: class.name.clone(),
                adaptee,
                target_interface,
            };

            Some(
                PatternMatch::new(pattern, confidence.min(1.0))
                    .with_location(Location::for_class(path.to_path_buf(), class))
                    .with_evidence(evidence),
            )
        } else {
            None
        }
    }

    /// Detect Proxy pattern.
    fn detect_proxy(&self, class: &ClassInfo, path: &Path, _lang: &str) -> Option<PatternMatch> {
        let mut confidence: f64 = 0.0;
        let mut evidence = Vec::new();
        let mut subject = String::new();
        let mut proxy_type = None;

        let class_name_lower = class.name.to_lowercase();

        // Check for proxy naming.
        if class_name_lower.contains("proxy") {
            confidence += 0.3;
            evidence.push("Class name contains 'Proxy'".to_string());
        }

        // Detect specific proxy types.
        if class_name_lower.contains("lazy") {
            proxy_type = Some("lazy".to_string());
            confidence += 0.1;
        } else if class_name_lower.contains("remote") {
            proxy_type = Some("remote".to_string());
            confidence += 0.1;
        } else if class_name_lower.contains("protection") || class_name_lower.contains("secure") {
            proxy_type = Some("protection".to_string());
            confidence += 0.1;
        } else if class_name_lower.contains("cache") || class_name_lower.contains("cached") {
            proxy_type = Some("caching".to_string());
            confidence += 0.1;
        } else if class_name_lower.contains("virtual") {
            proxy_type = Some("virtual".to_string());
            confidence += 0.1;
        }

        // Check for subject field of same type as base interface.
        for field in &class.fields {
            if let Some(ref field_type) = field.field_type {
                // Check if field type matches any base class.
                for base in &class.bases {
                    if field_type == base || field_type.contains(base) {
                        confidence += 0.3;
                        evidence.push(format!(
                            "Has subject field: {} of type {}",
                            field.name, field_type
                        ));
                        subject = field_type.clone();
                        break;
                    }
                }
            }

            // Check for subject/real naming.
            let field_lower = field.name.to_lowercase();
            if field_lower.contains("subject")
                || field_lower.contains("real")
                || field_lower.contains("target")
                || field_lower.contains("wrapped")
            {
                confidence += 0.15;
                if let Some(ref ft) = field.field_type {
                    subject = ft.clone();
                }
            }
        }

        // Check for lazy loading indicators.
        let has_lazy = class.methods.iter().any(|m| {
            let name_lower = m.name.to_lowercase();
            name_lower.contains("lazy")
                || name_lower.contains("ensure")
                || name_lower.contains("initialize")
                || name_lower.contains("load")
        });
        if has_lazy {
            confidence += 0.1;
            if proxy_type.is_none() {
                proxy_type = Some("lazy".to_string());
            }
        }

        // Check for access control methods.
        let has_access_control = class.methods.iter().any(|m| {
            let name_lower = m.name.to_lowercase();
            name_lower.contains("check")
                || name_lower.contains("authorize")
                || name_lower.contains("validate")
                || name_lower.contains("permission")
        });
        if has_access_control {
            confidence += 0.1;
            if proxy_type.is_none() {
                proxy_type = Some("protection".to_string());
            }
        }

        if confidence >= 0.4 && !subject.is_empty() {
            let pattern = DesignPattern::Proxy {
                class: class.name.clone(),
                subject,
                proxy_type,
            };

            Some(
                PatternMatch::new(pattern, confidence.min(1.0))
                    .with_location(Location::for_class(path.to_path_buf(), class))
                    .with_evidence(evidence),
            )
        } else {
            None
        }
    }

    /// Detect Command pattern.
    fn detect_command(
        &self,
        class: &ClassInfo,
        all_classes: &[ClassInfo],
        path: &Path,
        _lang: &str,
    ) -> Option<PatternMatch> {
        let mut confidence: f64 = 0.0;
        let mut evidence = Vec::new();
        let mut execute_method = String::new();
        let mut has_undo = false;

        let class_name_lower = class.name.to_lowercase();

        // Check for command naming.
        if class_name_lower.ends_with("command")
            || class_name_lower.ends_with("action")
            || class_name_lower.ends_with("handler")
        {
            confidence += 0.25;
            evidence.push("Class name suggests command pattern".to_string());
        }

        // Check for execute method.
        let execute_patterns = [
            "execute", "run", "invoke", "call", "handle", "perform", "do",
        ];
        for method in &class.methods {
            let method_lower = method.name.to_lowercase();
            if execute_patterns
                .iter()
                .any(|p| method_lower == *p || method_lower.starts_with(p))
            {
                confidence += 0.25;
                evidence.push(format!("Has execute method: {}", method.name));
                execute_method = method.name.clone();
            }

            // Check for undo support.
            if method_lower == "undo" || method_lower == "revert" || method_lower == "rollback" {
                has_undo = true;
                confidence += 0.15;
                evidence.push(format!("Has undo method: {}", method.name));
            }
        }

        // Check for receiver field (command encapsulates receiver).
        let has_receiver = class.fields.iter().any(|f| {
            let name_lower = f.name.to_lowercase();
            name_lower.contains("receiver")
                || name_lower.contains("target")
                || name_lower.contains("handler")
        });
        if has_receiver {
            confidence += 0.1;
            evidence.push("Has receiver field".to_string());
        }

        // Check if class implements Command interface.
        let implements_command = class.bases.iter().any(|b| {
            let b_lower = b.to_lowercase();
            b_lower.contains("command") || b_lower.contains("handler") || b_lower.contains("action")
        });
        if implements_command {
            confidence += 0.2;
            evidence.push(format!("Implements command interface: {:?}", class.bases));
        }

        if confidence >= 0.4 && !execute_method.is_empty() {
            // Try to find command interface and other implementations.
            let interface = class
                .bases
                .first()
                .cloned()
                .unwrap_or_else(|| "Command".to_string());
            let commands: Vec<String> = all_classes
                .iter()
                .filter(|c| c.name != class.name && c.bases.contains(&interface))
                .map(|c| c.name.clone())
                .collect();

            let pattern = DesignPattern::Command {
                interface,
                commands,
                execute_method,
                has_undo,
            };

            Some(
                PatternMatch::new(pattern, confidence.min(1.0))
                    .with_location(Location::for_class(path.to_path_buf(), class))
                    .with_evidence(evidence),
            )
        } else {
            None
        }
    }

    /// Detect Strategy pattern (multiple implementations of an interface).
    fn detect_strategy(
        &self,
        classes: &[ClassInfo],
        path: &Path,
        _lang: &str,
    ) -> Vec<PatternMatch> {
        let mut patterns = Vec::new();

        // Group classes by base interface.
        let mut interface_impls: FxHashMap<String, Vec<&ClassInfo>> = FxHashMap::default();
        for class in classes {
            for base in &class.bases {
                interface_impls.entry(base.clone()).or_default().push(class);
            }
        }

        // Find interfaces with multiple implementations.
        for (interface, implementations) in interface_impls {
            if implementations.len() < 2 {
                continue;
            }

            let mut confidence: f64 = 0.0;
            let mut evidence = Vec::new();

            // Check if interface name suggests strategy.
            let interface_lower = interface.to_lowercase();
            if interface_lower.contains("strategy")
                || interface_lower.contains("policy")
                || interface_lower.contains("algorithm")
                || interface_lower.contains("handler")
            {
                confidence += 0.3;
                evidence.push("Interface name suggests strategy pattern".to_string());
            }

            // Multiple implementations is a strong signal.
            confidence += 0.1 * (implementations.len().min(5) as f64);
            evidence.push(format!("{} implementations found", implementations.len()));

            // Check if implementations have similar method signatures.
            if implementations.len() >= 2 {
                let first_methods: HashSet<_> = implementations[0]
                    .methods
                    .iter()
                    .map(|m| m.name.as_str())
                    .collect();
                let all_have_same_methods = implementations.iter().skip(1).all(|impl_class| {
                    let impl_methods: HashSet<_> =
                        impl_class.methods.iter().map(|m| m.name.as_str()).collect();
                    !first_methods.is_disjoint(&impl_methods)
                });
                if all_have_same_methods {
                    confidence += 0.2;
                    evidence.push("Implementations share method signatures".to_string());
                }
            }

            // Check for context class that uses the interface.
            let context = classes.iter().find(|c| {
                c.fields.iter().any(|f| {
                    f.field_type
                        .as_ref()
                        .map(|t| t == &interface)
                        .unwrap_or(false)
                }) || c
                    .methods
                    .iter()
                    .any(|m| m.params.iter().any(|p| p.contains(&interface)))
            });

            if context.is_some() {
                confidence += 0.15;
                evidence.push("Found context class using strategy".to_string());
            }

            if confidence >= 0.4 {
                let impl_names: Vec<String> =
                    implementations.iter().map(|c| c.name.clone()).collect();

                let pattern = DesignPattern::Strategy {
                    interface: interface.clone(),
                    implementations: impl_names,
                    context: context.map(|c| c.name.clone()),
                };

                let mut locations = Vec::new();
                for impl_class in &implementations {
                    locations.push(Location::for_class(path.to_path_buf(), impl_class));
                }

                patterns.push(
                    PatternMatch::new(pattern, confidence.min(1.0))
                        .with_locations(locations)
                        .with_evidence(evidence),
                );
            }
        }

        patterns
    }

    /// Detect Dependency Injection pattern.
    fn detect_dependency_injection(
        &self,
        class: &ClassInfo,
        path: &Path,
        _lang: &str,
    ) -> Option<PatternMatch> {
        let mut confidence: f64 = 0.0;
        let mut evidence = Vec::new();
        let mut dependencies: Vec<(String, String)> = Vec::new();

        // Find constructor.
        let constructor = class.methods.iter().find(|m| {
            let name = m.name.to_lowercase();
            name == "__init__"
                || name == "new"
                || name == "constructor"
                || name == class.name.to_lowercase()
        });

        if let Some(ctor) = constructor {
            // Check for interface-typed parameters (excluding self/this).
            let meaningful_params: Vec<_> = ctor
                .params
                .iter()
                .filter(|p| !p.contains("self") && !p.contains("this"))
                .collect();

            for param in &meaningful_params {
                // Try to extract type from parameter.
                // Common formats: "name: Type", "Type name", "name"
                let parts: Vec<&str> = param.split(':').collect();
                let (name, type_hint) = if parts.len() >= 2 {
                    (
                        parts[0].trim().to_string(),
                        Some(parts[1].trim().to_string()),
                    )
                } else {
                    (param.trim().to_string(), None)
                };

                if let Some(ref t) = type_hint {
                    // Check if type looks like an interface (not primitive).
                    let t_lower = t.to_lowercase();
                    let is_primitive = [
                        "int", "str", "string", "bool", "boolean", "float", "double", "void",
                        "none", "null",
                    ]
                    .iter()
                    .any(|p| t_lower == *p);

                    if !is_primitive && !t.starts_with(char::is_lowercase) {
                        dependencies.push((name, t.clone()));
                        confidence += 0.15;
                    }
                }
            }
        }

        // Check for DI decorators/annotations.
        let di_decorators = [
            "inject",
            "autowired",
            "autowire",
            "dependency",
            "injectable",
        ];
        for decorator in &class.decorators {
            let dec_lower = decorator.to_lowercase();
            if di_decorators.iter().any(|d| dec_lower.contains(d)) {
                confidence += 0.25;
                evidence.push(format!("Has DI decorator: {}", decorator));
            }
        }

        // Check for method injection via setters.
        let setter_injection = class
            .methods
            .iter()
            .filter(|m| {
                let name_lower = m.name.to_lowercase();
                (name_lower.starts_with("set_") || name_lower.starts_with("inject_"))
                    && m.params.len() >= 2 // self + injected dependency
            })
            .count();

        if setter_injection > 0 {
            confidence += 0.1 * setter_injection as f64;
            evidence.push(format!("{} setter injection methods", setter_injection));
        }

        // Check for field-based injection.
        for field in &class.fields {
            for annotation in &field.annotations {
                let ann_lower = annotation.to_lowercase();
                if di_decorators.iter().any(|d| ann_lower.contains(d)) {
                    confidence += 0.2;
                    if let Some(ref ft) = field.field_type {
                        dependencies.push((field.name.clone(), ft.clone()));
                    }
                }
            }
        }

        evidence.push(format!("{} dependencies detected", dependencies.len()));

        if confidence >= 0.4 && !dependencies.is_empty() {
            let pattern = DesignPattern::DependencyInjection {
                class: class.name.clone(),
                dependencies,
            };

            Some(
                PatternMatch::new(pattern, confidence.min(1.0))
                    .with_location(Location::for_class(path.to_path_buf(), class))
                    .with_evidence(evidence),
            )
        } else {
            None
        }
    }

    /// Detect Repository pattern.
    fn detect_repository(
        &self,
        class: &ClassInfo,
        path: &Path,
        _lang: &str,
    ) -> Option<PatternMatch> {
        let mut confidence: f64 = 0.0;
        let mut evidence = Vec::new();
        let mut entity_type = None;
        let mut crud_methods = Vec::new();

        let class_name_lower = class.name.to_lowercase();

        // Check for repository naming.
        if class_name_lower.ends_with("repository") || class_name_lower.ends_with("repo") {
            confidence += 0.35;
            evidence.push("Class name suggests repository pattern".to_string());

            // Try to extract entity type from name.
            let entity = class_name_lower
                .strip_suffix("repository")
                .or_else(|| class_name_lower.strip_suffix("repo"));
            if let Some(e) = entity {
                if !e.is_empty() {
                    // Capitalize first letter.
                    let mut chars = e.chars();
                    if let Some(first) = chars.next() {
                        entity_type = Some(format!(
                            "{}{}",
                            first.to_uppercase(),
                            chars.collect::<String>()
                        ));
                    }
                }
            }
        }

        // Check for DAO naming.
        if class_name_lower.ends_with("dao") {
            confidence += 0.25;
            evidence.push("Class name ends with 'DAO'".to_string());
        }

        // Check for CRUD methods.
        let crud_patterns = [
            ("find", "read"),
            ("get", "read"),
            ("fetch", "read"),
            ("load", "read"),
            ("save", "write"),
            ("create", "write"),
            ("add", "write"),
            ("insert", "write"),
            ("update", "write"),
            ("modify", "write"),
            ("delete", "write"),
            ("remove", "write"),
            ("list", "read"),
            ("all", "read"),
            ("count", "read"),
        ];

        for method in &class.methods {
            let method_lower = method.name.to_lowercase();
            for (pattern, _op_type) in &crud_patterns {
                if method_lower.contains(pattern) {
                    crud_methods.push(method.name.clone());
                    confidence += 0.05;
                    break;
                }
            }
        }

        // Higher confidence for having multiple CRUD operations.
        let unique_operations: HashSet<_> = crud_methods
            .iter()
            .filter_map(|m| {
                let m_lower = m.to_lowercase();
                if m_lower.contains("find") || m_lower.contains("get") || m_lower.contains("load") {
                    Some("read")
                } else if m_lower.contains("save")
                    || m_lower.contains("create")
                    || m_lower.contains("insert")
                {
                    Some("create")
                } else if m_lower.contains("update") || m_lower.contains("modify") {
                    Some("update")
                } else if m_lower.contains("delete") || m_lower.contains("remove") {
                    Some("delete")
                } else {
                    None
                }
            })
            .collect();

        if unique_operations.len() >= 3 {
            confidence += 0.2;
            evidence.push(format!(
                "Has {} CRUD operations: {:?}",
                unique_operations.len(),
                unique_operations
            ));
        }

        // Check for entity type in methods or fields.
        if entity_type.is_none() {
            for method in &class.methods {
                if let Some(ref ret) = method.return_type {
                    let ret_lower = ret.to_lowercase();
                    if !ret_lower.contains("list")
                        && !ret_lower.contains("vec")
                        && !ret_lower.contains("option")
                        && ret.starts_with(char::is_uppercase)
                    {
                        entity_type = Some(ret.clone());
                        break;
                    }
                }
            }
        }

        if confidence >= 0.4 && !crud_methods.is_empty() {
            let pattern = DesignPattern::Repository {
                class: class.name.clone(),
                entity_type,
                methods: crud_methods,
            };

            Some(
                PatternMatch::new(pattern, confidence.min(1.0))
                    .with_location(Location::for_class(path.to_path_buf(), class))
                    .with_evidence(evidence),
            )
        } else {
            None
        }
    }

    /// Calculate and update statistics.
    fn calculate_stats(&self, analysis: &mut PatternAnalysis) {
        let mut by_category: HashMap<String, usize> = HashMap::new();
        let mut by_type: HashMap<String, usize> = HashMap::new();
        let mut total_confidence = 0.0;
        let mut files_with_patterns: HashSet<&Path> = HashSet::new();

        for pattern_match in &analysis.patterns {
            let category = pattern_match.pattern.category().to_string();
            *by_category.entry(category).or_insert(0) += 1;

            let pattern_name = pattern_match.pattern.name().to_string();
            *by_type.entry(pattern_name).or_insert(0) += 1;

            total_confidence += pattern_match.confidence;

            for loc in &pattern_match.locations {
                files_with_patterns.insert(&loc.file);
            }
        }

        analysis.stats.patterns_detected = analysis.patterns.len();
        analysis.stats.files_with_patterns = files_with_patterns.len();
        analysis.stats.by_category = by_category;
        analysis.stats.by_type = by_type;
        analysis.stats.average_confidence = if analysis.patterns.is_empty() {
            0.0
        } else {
            total_confidence / analysis.patterns.len() as f64
        };
    }
}

// =============================================================================
// HELPER FUNCTIONS
// =============================================================================

/// Check if a file is a test file based on path patterns.
fn is_test_file(path: &Path) -> bool {
    let path_str = path.to_string_lossy().to_lowercase();
    path_str.contains("/test/")
        || path_str.contains("/tests/")
        || path_str.contains("_test.")
        || path_str.contains("_spec.")
        || path_str.contains(".test.")
        || path_str.contains(".spec.")
        || path_str.contains("/test_")
        || path_str.contains("/__tests__/")
}

/// Check if a file is generated based on path patterns.
fn is_generated_file(path: &Path) -> bool {
    let path_str = path.to_string_lossy().to_lowercase();
    path_str.contains("/generated/")
        || path_str.contains("/gen/")
        || path_str.contains(".generated.")
        || path_str.contains(".g.")
        || path_str.contains("_generated")
        || path_str.contains("/build/")
        || path_str.contains("/dist/")
        || path_str.contains("/node_modules/")
        || path_str.contains("__pycache__")
}

// =============================================================================
// PUBLIC API
// =============================================================================

/// Detect design patterns in a file or directory.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `pattern_filter` - Optional pattern name to filter (e.g., "singleton", "factory")
/// * `config` - Optional configuration (uses defaults if None)
///
/// # Returns
///
/// Analysis result with detected patterns and statistics.
///
/// # Example
///
/// ```ignore
/// use go_brrr::patterns::detect_patterns;
///
/// // Detect all patterns with default config
/// let result = detect_patterns("./src", None, None)?;
///
/// // Detect only singletons with high confidence
/// let config = PatternConfig::default().with_min_confidence(0.7);
/// let singletons = detect_patterns("./src", Some("singleton"), Some(config))?;
/// ```
pub fn detect_patterns(
    path: impl AsRef<Path>,
    pattern_filter: Option<&str>,
    config: Option<PatternConfig>,
) -> Result<PatternAnalysis> {
    let mut config = config.unwrap_or_default();
    if let Some(filter) = pattern_filter {
        config.patterns = vec![filter.to_string()];
    }

    let detector = PatternDetector::new(config);
    detector.detect(path)
}

/// Format a pattern analysis as a human-readable summary.
pub fn format_pattern_summary(analysis: &PatternAnalysis) -> String {
    let mut output = String::new();

    output.push_str(&format!(
        "Design Pattern Analysis: {}\n",
        analysis.path.display()
    ));
    output.push_str(&format!(
        "Files scanned: {}\n",
        analysis.stats.files_scanned
    ));
    output.push_str(&format!(
        "Files with patterns: {}\n",
        analysis.stats.files_with_patterns
    ));
    output.push_str(&format!(
        "Total patterns detected: {}\n",
        analysis.stats.patterns_detected
    ));
    output.push_str(&format!(
        "Average confidence: {:.1}%\n\n",
        analysis.stats.average_confidence * 100.0
    ));

    if !analysis.stats.by_category.is_empty() {
        output.push_str("By Category:\n");
        for (category, count) in &analysis.stats.by_category {
            output.push_str(&format!("  {}: {}\n", category, count));
        }
        output.push('\n');
    }

    if !analysis.stats.by_type.is_empty() {
        output.push_str("By Pattern Type:\n");
        for (pattern_type, count) in &analysis.stats.by_type {
            output.push_str(&format!("  {}: {}\n", pattern_type, count));
        }
        output.push('\n');
    }

    output.push_str("Detected Patterns:\n");
    for pattern_match in &analysis.patterns {
        output.push_str(&format!(
            "\n  {} (confidence: {:.1}%)\n",
            pattern_match.pattern.name(),
            pattern_match.confidence * 100.0
        ));

        output.push_str(&format!(
            "    Category: {}\n",
            pattern_match.pattern.category()
        ));
        output.push_str(&format!(
            "    Primary class: {}\n",
            pattern_match.pattern.primary_class()
        ));

        if let Some(loc) = pattern_match.primary_location() {
            output.push_str(&format!(
                "    Location: {}:{}\n",
                loc.file.display(),
                loc.line
            ));
        }

        if let Some(ref note) = pattern_match.note {
            if !note.is_empty() {
                output.push_str(&format!("    Note: {}\n", note));
            }
        }

        if !pattern_match.evidence.is_empty() {
            output.push_str("    Evidence:\n");
            for ev in &pattern_match.evidence {
                output.push_str(&format!("      - {}\n", ev));
            }
        }
    }

    if !analysis.errors.is_empty() {
        output.push_str("\nErrors:\n");
        for error in &analysis.errors {
            output.push_str(&format!("  - {}\n", error));
        }
    }

    output
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::FieldInfo;

    #[test]
    fn test_pattern_category_display() {
        assert_eq!(PatternCategory::Creational.to_string(), "Creational");
        assert_eq!(PatternCategory::Structural.to_string(), "Structural");
        assert_eq!(PatternCategory::Behavioral.to_string(), "Behavioral");
    }

    #[test]
    fn test_design_pattern_name() {
        let singleton = DesignPattern::Singleton {
            class: "Config".to_string(),
            instance_method: "getInstance".to_string(),
            instance_field: None,
            private_constructor: true,
        };
        assert_eq!(singleton.name(), "Singleton");
        assert_eq!(singleton.category(), PatternCategory::Creational);
        assert_eq!(singleton.primary_class(), "Config");
    }

    #[test]
    fn test_pattern_match_builder() {
        let pattern = DesignPattern::Builder {
            class: "RequestBuilder".to_string(),
            build_method: "build".to_string(),
            setters: vec!["with_url".to_string(), "with_headers".to_string()],
            target_type: Some("Request".to_string()),
        };

        let match_ = PatternMatch::new(pattern, 0.85)
            .with_location(Location {
                file: PathBuf::from("/src/builder.rs"),
                line: 10,
                end_line: Some(50),
                name: "RequestBuilder".to_string(),
                kind: "class".to_string(),
            })
            .with_evidence(vec!["Has build method".to_string()]);

        assert_eq!(match_.confidence, 0.85);
        assert!(match_.primary_location().is_some());
        assert_eq!(match_.evidence.len(), 1);
    }

    #[test]
    fn test_pattern_config_defaults() {
        let config = PatternConfig::default();
        assert_eq!(config.min_confidence, 0.5);
        assert!(config.patterns.is_empty());
        assert!(config.language.is_none());
        assert!(config.detect_modern_patterns);
    }

    #[test]
    fn test_pattern_config_builder() {
        let config = PatternConfig::for_pattern("singleton")
            .with_min_confidence(0.8)
            .with_language("rust")
            .with_modern_patterns(false);

        assert_eq!(config.patterns, vec!["singleton"]);
        assert_eq!(config.min_confidence, 0.8);
        assert_eq!(config.language, Some("rust".to_string()));
        assert!(!config.detect_modern_patterns);
    }

    #[test]
    fn test_is_test_file() {
        assert!(is_test_file(Path::new("/src/tests/test_foo.py")));
        assert!(is_test_file(Path::new("/src/foo_test.go")));
        assert!(is_test_file(Path::new("/src/foo.spec.ts")));
        assert!(is_test_file(Path::new("/src/__tests__/foo.js")));
        assert!(!is_test_file(Path::new("/src/foo.py")));
    }

    #[test]
    fn test_is_generated_file() {
        assert!(is_generated_file(Path::new("/generated/foo.rs")));
        assert!(is_generated_file(Path::new("/src/foo.generated.ts")));
        assert!(is_generated_file(Path::new("/node_modules/foo/index.js")));
        assert!(is_generated_file(Path::new("/__pycache__/foo.pyc")));
        assert!(!is_generated_file(Path::new("/src/foo.rs")));
    }

    #[test]
    fn test_pattern_analysis_filters() {
        let mut analysis = PatternAnalysis::new(PathBuf::from("."));

        analysis.patterns.push(PatternMatch::new(
            DesignPattern::Singleton {
                class: "Config".to_string(),
                instance_method: "getInstance".to_string(),
                instance_field: None,
                private_constructor: true,
            },
            0.9,
        ));

        analysis.patterns.push(PatternMatch::new(
            DesignPattern::Factory {
                class: "CarFactory".to_string(),
                create_methods: vec!["createCar".to_string()],
                products: vec!["Car".to_string()],
                is_abstract: false,
            },
            0.5,
        ));

        assert_eq!(analysis.patterns_of_type("singleton").len(), 1);
        assert_eq!(
            analysis
                .patterns_in_category(PatternCategory::Creational)
                .len(),
            2
        );
        assert_eq!(analysis.high_confidence_patterns().len(), 1);
    }

    #[test]
    fn test_singleton_detection_heuristics() {
        // Test class with singleton indicators.
        let class = ClassInfo {
            name: "DatabaseConnection".to_string(),
            methods: vec![
                FunctionInfo {
                    name: "__init__".to_string(),
                    params: vec!["self".to_string()],
                    decorators: vec!["@private".to_string()],
                    ..Default::default()
                },
                FunctionInfo {
                    name: "get_instance".to_string(),
                    params: vec![],
                    decorators: vec!["@staticmethod".to_string()],
                    return_type: Some("DatabaseConnection".to_string()),
                    ..Default::default()
                },
            ],
            fields: vec![FieldInfo {
                name: "_instance".to_string(),
                is_static: true,
                field_type: Some("DatabaseConnection".to_string()),
                ..Default::default()
            }],
            language: "python".to_string(),
            ..Default::default()
        };

        let detector = PatternDetector::new(PatternConfig::default());
        let result = detector.detect_singleton(&class, Path::new("/test.py"), "python");

        assert!(result.is_some());
        let pattern_match = result.unwrap();
        assert!(pattern_match.confidence >= 0.5);
        assert!(matches!(
            pattern_match.pattern,
            DesignPattern::Singleton { .. }
        ));
    }

    #[test]
    fn test_builder_detection_heuristics() {
        // Test class with builder pattern indicators.
        let class = ClassInfo {
            name: "RequestBuilder".to_string(),
            methods: vec![
                FunctionInfo {
                    name: "with_url".to_string(),
                    params: vec!["self".to_string(), "url: str".to_string()],
                    return_type: Some("Self".to_string()),
                    ..Default::default()
                },
                FunctionInfo {
                    name: "with_headers".to_string(),
                    params: vec!["self".to_string(), "headers: dict".to_string()],
                    return_type: Some("Self".to_string()),
                    ..Default::default()
                },
                FunctionInfo {
                    name: "build".to_string(),
                    params: vec!["self".to_string()],
                    return_type: Some("Request".to_string()),
                    ..Default::default()
                },
            ],
            language: "python".to_string(),
            ..Default::default()
        };

        let detector = PatternDetector::new(PatternConfig::default());
        let result = detector.detect_builder(&class, Path::new("/test.py"), "python");

        assert!(result.is_some());
        let pattern_match = result.unwrap();
        assert!(pattern_match.confidence >= 0.5);
        if let DesignPattern::Builder {
            setters,
            build_method,
            ..
        } = &pattern_match.pattern
        {
            assert_eq!(*build_method, "build");
            assert!(setters.contains(&"with_url".to_string()));
            assert!(setters.contains(&"with_headers".to_string()));
        } else {
            panic!("Expected Builder pattern");
        }
    }

    #[test]
    fn test_observer_detection_heuristics() {
        let class = ClassInfo {
            name: "EventEmitter".to_string(),
            methods: vec![
                FunctionInfo {
                    name: "add_listener".to_string(),
                    params: vec!["self".to_string(), "listener: Listener".to_string()],
                    ..Default::default()
                },
                FunctionInfo {
                    name: "remove_listener".to_string(),
                    params: vec!["self".to_string(), "listener: Listener".to_string()],
                    ..Default::default()
                },
                FunctionInfo {
                    name: "notify_all".to_string(),
                    params: vec!["self".to_string()],
                    ..Default::default()
                },
            ],
            fields: vec![FieldInfo {
                name: "listeners".to_string(),
                field_type: Some("List<Listener>".to_string()),
                ..Default::default()
            }],
            language: "python".to_string(),
            ..Default::default()
        };

        let detector = PatternDetector::new(PatternConfig::default());
        let result = detector.detect_observer(&class, Path::new("/test.py"), "python");

        assert!(result.is_some());
        let pattern_match = result.unwrap();
        assert!(pattern_match.confidence >= 0.5);
        assert!(matches!(
            pattern_match.pattern,
            DesignPattern::Observer { .. }
        ));
    }

    #[test]
    fn test_repository_detection_heuristics() {
        let class = ClassInfo {
            name: "UserRepository".to_string(),
            methods: vec![
                FunctionInfo {
                    name: "find_by_id".to_string(),
                    params: vec!["self".to_string(), "id: int".to_string()],
                    return_type: Some("User".to_string()),
                    ..Default::default()
                },
                FunctionInfo {
                    name: "save".to_string(),
                    params: vec!["self".to_string(), "user: User".to_string()],
                    ..Default::default()
                },
                FunctionInfo {
                    name: "delete".to_string(),
                    params: vec!["self".to_string(), "id: int".to_string()],
                    ..Default::default()
                },
                FunctionInfo {
                    name: "find_all".to_string(),
                    params: vec!["self".to_string()],
                    return_type: Some("List<User>".to_string()),
                    ..Default::default()
                },
            ],
            language: "python".to_string(),
            ..Default::default()
        };

        let detector = PatternDetector::new(PatternConfig::default());
        let result = detector.detect_repository(&class, Path::new("/test.py"), "python");

        assert!(result.is_some());
        let pattern_match = result.unwrap();
        assert!(pattern_match.confidence >= 0.5);
        if let DesignPattern::Repository {
            entity_type,
            methods,
            ..
        } = &pattern_match.pattern
        {
            assert_eq!(*entity_type, Some("User".to_string()));
            assert!(methods.len() >= 3);
        } else {
            panic!("Expected Repository pattern");
        }
    }

    #[test]
    fn test_format_pattern_summary() {
        let mut analysis = PatternAnalysis::new(PathBuf::from("/test"));
        analysis.stats.files_scanned = 10;
        analysis.stats.patterns_detected = 2;
        analysis.stats.average_confidence = 0.75;

        analysis.patterns.push(
            PatternMatch::new(
                DesignPattern::Singleton {
                    class: "Config".to_string(),
                    instance_method: "getInstance".to_string(),
                    instance_field: None,
                    private_constructor: true,
                },
                0.9,
            )
            .with_location(Location {
                file: PathBuf::from("/test/config.py"),
                line: 10,
                end_line: Some(30),
                name: "Config".to_string(),
                kind: "class".to_string(),
            }),
        );

        let summary = format_pattern_summary(&analysis);
        assert!(summary.contains("Singleton"));
        assert!(summary.contains("Config"));
        assert!(summary.contains("90.0%"));
    }
}
