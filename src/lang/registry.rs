//! Language registry for extension-to-language mapping.
//!
//! Provides a singleton registry that maps file extensions to their
//! corresponding [`Language`] implementations.
//!
//! # Aliases
//!
//! The registry supports language name aliases for API compatibility.
//! For example, "javascript" is an alias for "typescript" since both
//! use the same tree-sitter parser. This ensures that callers using
//! `get_by_name("javascript")` get the correct handler.

use std::collections::HashMap;
use std::path::Path;
use std::sync::OnceLock;

use crate::lang::traits::{BoxedLanguage, Language};
use crate::lang::{c, cpp, go, java, python, rust_lang, typescript};

static REGISTRY: OnceLock<LanguageRegistry> = OnceLock::new();

/// Registry mapping file extensions to language implementations.
///
/// The registry maintains three mappings:
/// - `by_name`: Language name to implementation (e.g., "typescript" -> TypeScript)
/// - `by_ext`: File extension to language name (e.g., ".ts" -> "typescript")
/// - `aliases`: Alternative names to canonical names (e.g., "javascript" -> "typescript")
pub struct LanguageRegistry {
    by_name: HashMap<&'static str, BoxedLanguage>,
    by_ext: HashMap<&'static str, &'static str>,
    aliases: HashMap<&'static str, &'static str>,
}

impl LanguageRegistry {
    /// Get the global language registry singleton.
    pub fn global() -> &'static Self {
        REGISTRY.get_or_init(Self::new)
    }

    /// Create a new registry with all supported languages.
    fn new() -> Self {
        let mut registry = Self {
            by_name: HashMap::new(),
            by_ext: HashMap::new(),
            aliases: HashMap::new(),
        };

        // Register all languages
        registry.register(Box::new(python::Python));

        // BUG #22 FIX: Register both TypeScript (for .ts/.js) and TSX (for .tsx/.jsx)
        // variants separately. This ensures that callers using extract_from_source()
        // with language="tsx" get the correct TSX grammar that supports JSX syntax.
        // Note: TSX is registered FIRST so its extensions (.tsx, .jsx) take precedence
        // in the by_ext map, then TypeScript is registered to claim .ts, .js, .mjs, .cjs.
        registry.register(Box::new(typescript::TypeScript::tsx()));
        registry.register(Box::new(typescript::TypeScript::new()));

        registry.register(Box::new(go::Go));
        registry.register(Box::new(rust_lang::Rust));
        registry.register(Box::new(java::Java));
        registry.register(Box::new(c::C));
        registry.register(Box::new(cpp::Cpp));

        // Register language aliases for API compatibility with Python implementation.
        // Python treats "javascript" and "typescript" as separate languages, but both
        // use the same tree-sitter-typescript grammar in Rust. These aliases ensure
        // that `get_by_name("javascript")` resolves to the TypeScript handler.
        registry.register_alias("javascript", "typescript");
        registry.register_alias("js", "typescript");
        registry.register_alias("ts", "typescript");
        registry.register_alias("jsx", "tsx");

        registry
    }

    /// Register an alias for a language name.
    ///
    /// Aliases allow alternative names to resolve to the same language handler.
    /// For example, "javascript" -> "typescript" means `get_by_name("javascript")`
    /// returns the TypeScript handler.
    ///
    /// # Arguments
    ///
    /// * `alias` - The alternative name (e.g., "javascript")
    /// * `target` - The canonical language name (e.g., "typescript")
    fn register_alias(&mut self, alias: &'static str, target: &'static str) {
        self.aliases.insert(alias, target);
    }

    /// Register a language implementation.
    fn register(&mut self, lang: BoxedLanguage) {
        let name = lang.name();
        for ext in lang.extensions() {
            self.by_ext.insert(*ext, name);
        }
        self.by_name.insert(name, lang);
    }

    /// Get a language by name (e.g., "python").
    ///
    /// This method first checks for aliases, then looks up the canonical name.
    /// For example, `get_by_name("javascript")` resolves the "javascript" alias
    /// to "typescript" and returns the TypeScript handler.
    pub fn get_by_name(&self, name: &str) -> Option<&dyn Language> {
        // Resolve alias if present, otherwise use the name directly
        let canonical_name = self.aliases.get(name).copied().unwrap_or(name);
        self.by_name.get(canonical_name).map(|b| b.as_ref())
    }

    /// Get a language by file extension (e.g., ".py").
    pub fn get_by_extension(&self, ext: &str) -> Option<&dyn Language> {
        self.by_ext.get(ext).and_then(|name| self.get_by_name(name))
    }

    /// Auto-detect language from file path extension.
    pub fn detect_language(&self, path: &Path) -> Option<&dyn Language> {
        path.extension()
            .and_then(|e| e.to_str())
            .map(|ext| format!(".{}", ext))
            .and_then(|ext| self.get_by_extension(&ext))
    }

    /// List all canonical language names (excludes aliases).
    ///
    /// Returns names like "python", "typescript", "tsx", etc.
    /// Use `supported_languages_with_aliases()` to include aliases.
    #[allow(dead_code)]
    pub fn supported_languages(&self) -> Vec<&'static str> {
        self.by_name.keys().copied().collect()
    }

    /// List all supported language names including aliases.
    ///
    /// Returns canonical names plus aliases like "javascript", "js", etc.
    /// This is useful for CLI help text and validation.
    #[allow(dead_code)]
    pub fn supported_languages_with_aliases(&self) -> Vec<&'static str> {
        let mut names: Vec<&'static str> = self.by_name.keys().copied().collect();
        names.extend(self.aliases.keys().copied());
        names.sort_unstable();
        names
    }

    /// Check if a language name is supported (including aliases).
    #[allow(dead_code)]
    pub fn is_supported(&self, name: &str) -> bool {
        self.by_name.contains_key(name) || self.aliases.contains_key(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_by_name_canonical() {
        let registry = LanguageRegistry::global();

        // Canonical names should work
        assert!(registry.get_by_name("python").is_some());
        assert!(registry.get_by_name("typescript").is_some());
        assert!(registry.get_by_name("tsx").is_some());
        assert!(registry.get_by_name("go").is_some());
        assert!(registry.get_by_name("rust").is_some());
    }

    #[test]
    fn test_get_by_name_javascript_alias() {
        let registry = LanguageRegistry::global();

        // "javascript" alias should resolve to TypeScript handler
        let js_lang = registry.get_by_name("javascript");
        assert!(js_lang.is_some(), "javascript alias should be supported");

        // Verify it returns the TypeScript handler
        let ts_lang = registry.get_by_name("typescript");
        assert!(ts_lang.is_some());

        // Both should point to the same handler (same name)
        assert_eq!(js_lang.unwrap().name(), ts_lang.unwrap().name());
    }

    #[test]
    fn test_get_by_name_shorthand_aliases() {
        let registry = LanguageRegistry::global();

        // Short aliases should work
        assert!(registry.get_by_name("js").is_some());
        assert!(registry.get_by_name("ts").is_some());
        assert!(registry.get_by_name("jsx").is_some());

        // "js" and "ts" should resolve to "typescript"
        assert_eq!(registry.get_by_name("js").unwrap().name(), "typescript");
        assert_eq!(registry.get_by_name("ts").unwrap().name(), "typescript");

        // "jsx" should resolve to "tsx"
        assert_eq!(registry.get_by_name("jsx").unwrap().name(), "tsx");
    }

    #[test]
    fn test_is_supported_includes_aliases() {
        let registry = LanguageRegistry::global();

        // Canonical names
        assert!(registry.is_supported("python"));
        assert!(registry.is_supported("typescript"));
        assert!(registry.is_supported("tsx"));

        // Aliases
        assert!(registry.is_supported("javascript"));
        assert!(registry.is_supported("js"));
        assert!(registry.is_supported("ts"));
        assert!(registry.is_supported("jsx"));

        // Non-existent
        assert!(!registry.is_supported("brainfuck"));
        assert!(!registry.is_supported("cobol"));
    }

    #[test]
    fn test_supported_languages_with_aliases() {
        let registry = LanguageRegistry::global();

        let all_names = registry.supported_languages_with_aliases();

        // Should include canonical names
        assert!(all_names.contains(&"python"));
        assert!(all_names.contains(&"typescript"));
        assert!(all_names.contains(&"tsx"));

        // Should include aliases
        assert!(all_names.contains(&"javascript"));
        assert!(all_names.contains(&"js"));
        assert!(all_names.contains(&"ts"));
        assert!(all_names.contains(&"jsx"));
    }

    #[test]
    fn test_supported_languages_excludes_aliases() {
        let registry = LanguageRegistry::global();

        let canonical_names = registry.supported_languages();

        // Should include canonical names
        assert!(canonical_names.contains(&"python"));
        assert!(canonical_names.contains(&"typescript"));
        assert!(canonical_names.contains(&"tsx"));

        // Should NOT include aliases
        assert!(!canonical_names.contains(&"javascript"));
        assert!(!canonical_names.contains(&"js"));
        assert!(!canonical_names.contains(&"ts"));
        assert!(!canonical_names.contains(&"jsx"));
    }

    #[test]
    fn test_get_by_extension_js() {
        let registry = LanguageRegistry::global();

        // .js files should be detected as TypeScript (same parser)
        let js_lang = registry.get_by_extension(".js");
        assert!(js_lang.is_some());
        assert_eq!(js_lang.unwrap().name(), "typescript");

        // .jsx files should be detected as TSX
        let jsx_lang = registry.get_by_extension(".jsx");
        assert!(jsx_lang.is_some());
        assert_eq!(jsx_lang.unwrap().name(), "tsx");
    }
}
