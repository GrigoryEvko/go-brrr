//! Design pattern detection module.
//!
//! Provides automatic detection of common design patterns in source code.
//!
//! # Supported Patterns
//!
//! **Creational Patterns:**
//! - **Singleton**: Single instance with global access
//! - **Factory**: Object creation without specifying exact class
//! - **Builder**: Step-by-step object construction
//!
//! **Structural Patterns:**
//! - **Adapter**: Interface compatibility layer
//! - **Decorator**: Dynamic behavior addition
//! - **Proxy**: Surrogate for another object
//!
//! **Behavioral Patterns:**
//! - **Observer**: Publish-subscribe mechanism
//! - **Strategy**: Interchangeable algorithms
//! - **Command**: Encapsulated action
//! - **Dependency Injection**: Modern DI pattern
//! - **Repository**: Data access abstraction
//!
//! # Example
//!
//! ```ignore
//! use brrr::patterns::{detect_patterns, PatternConfig, DesignPattern};
//!
//! // Detect all patterns with default settings
//! let result = detect_patterns("./src", None, None)?;
//!
//! for pattern_match in &result.patterns {
//!     println!("{}: confidence {:.0}%",
//!         pattern_match.pattern.name(),
//!         pattern_match.confidence * 100.0);
//! }
//!
//! // Detect only singleton patterns with high confidence
//! let config = PatternConfig::default().with_min_confidence(0.8);
//! let singletons = detect_patterns("./src", Some("singleton"), Some(config))?;
//! ```
//!
//! # Language Support
//!
//! Pattern detection works across all languages supported by the AST extractor:
//! - Python, Rust, Go, TypeScript/JavaScript, Java, C, C++
//!
//! Language-specific idioms are recognized:
//! - Python: `__new__` for singleton
//! - Rust: Traits for interfaces, `lazy_static`/`OnceCell` for singleton
//! - Go: Implicit interfaces
//! - Java/TypeScript: Standard OOP patterns
//!
//! # CLI Usage
//!
//! ```bash
//! # Detect all patterns
//! brrr patterns ./src
//!
//! # Detect specific pattern
//! brrr patterns ./src --pattern singleton
//!
//! # High confidence only
//! brrr patterns ./src --min-confidence 0.8
//! ```

pub mod design_patterns;

// Re-export main types for convenience.
pub use design_patterns::{
    // Main API
    detect_patterns, format_pattern_summary,
    // Configuration
    PatternConfig,
    // Types
    DesignPattern, Location, PatternAnalysis, PatternCategory, PatternDetector, PatternError,
    PatternMatch, PatternStats,
};
