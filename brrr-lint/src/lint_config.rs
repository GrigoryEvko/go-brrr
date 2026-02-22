//! `.brrr-lint.toml` configuration file support.
//!
//! Provides deserialization, discovery (walk up to `.git` root), and merging
//! with CLI flags. CLI flags always take precedence over file config.
//!
//! # Example config
//!
//! ```toml
//! [rules]
//! select = ["FST001", "FST003", "FST004"]
//! exclude = ["FST014"]
//!
//! [rules.severity]
//! FST003 = "error"
//! FST013 = "hint"
//!
//! [rules.config.FST007]
//! max_z3rlimit = 100
//!
//! [files]
//! include = ["src/**/*.fst", "src/**/*.fsti"]
//! exclude = ["vendor/**", "generated/**"]
//!
//! [fix]
//! unsafe_fixes = false
//! backup = true
//! ```

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// Top-level `.brrr-lint.toml` configuration.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct LintFileConfig {
    /// Rule selection and severity overrides.
    #[serde(default)]
    pub rules: RulesConfig,

    /// File include/exclude patterns.
    #[serde(default)]
    pub files: FilesConfig,

    /// Fix behavior settings.
    #[serde(default)]
    pub fix: FixConfig,

    /// Output settings.
    #[serde(default)]
    pub output: OutputConfig,
}

/// Rule selection, severity overrides, and per-rule configuration.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct RulesConfig {
    /// Rules to enable. If empty/absent, all rules are enabled.
    /// Example: `["FST001", "FST003"]`
    #[serde(default)]
    pub select: Vec<String>,

    /// Rules to exclude (takes precedence over `select`).
    /// Example: `["FST014"]`
    #[serde(default)]
    pub exclude: Vec<String>,

    /// Per-rule severity overrides.
    /// Keys are rule codes (e.g., "FST003"), values are severity strings
    /// ("error", "warning", "info", "hint").
    #[serde(default)]
    pub severity: HashMap<String, String>,

    /// Per-rule configuration. Keys are rule codes, values are
    /// arbitrary key-value maps passed to the rule implementation.
    #[serde(default)]
    pub config: HashMap<String, toml::Value>,
}

/// File include/exclude glob patterns.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct FilesConfig {
    /// Glob patterns for files to include. If empty, all `.fst`/`.fsti` files
    /// are included (default behavior).
    /// Example: `["src/**/*.fst", "src/**/*.fsti"]`
    #[serde(default)]
    pub include: Vec<String>,

    /// Glob patterns for files to exclude.
    /// Example: `["vendor/**", "generated/**"]`
    #[serde(default)]
    pub exclude: Vec<String>,
}

/// Fix application settings.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct FixConfig {
    /// Allow unsafe fixes (equivalent to `--force`).
    #[serde(default)]
    pub unsafe_fixes: bool,

    /// Create backups before applying fixes (default: true).
    #[serde(default = "default_true")]
    pub backup: bool,
}

impl Default for FixConfig {
    fn default() -> Self {
        Self {
            unsafe_fixes: false,
            backup: true,
        }
    }
}

/// Output settings (can be overridden by CLI flags).
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct OutputConfig {
    /// Output format: "text", "concise", "json", "github", "sarif".
    #[serde(default)]
    pub format: Option<String>,

    /// Maximum diagnostics to show before stopping.
    #[serde(default)]
    pub max_diagnostics: Option<usize>,

    /// Quiet mode: suppress non-diagnostic output.
    #[serde(default)]
    pub quiet: bool,

    /// Verbose mode: show additional details.
    #[serde(default)]
    pub verbose: bool,
}

fn default_true() -> bool {
    true
}

// ---------------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------------

impl LintFileConfig {
    /// Parse a `.brrr-lint.toml` file from a string.
    pub fn parse(s: &str) -> Result<Self, ConfigError> {
        toml::from_str(s).map_err(ConfigError::Parse)
    }

    /// Load a `.brrr-lint.toml` file from disk.
    pub fn load(path: &Path) -> Result<Self, ConfigError> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| ConfigError::Io(path.to_path_buf(), e))?;
        let config = Self::parse(&content)?;
        config.validate()?;
        Ok(config)
    }

    /// Validate semantic constraints that TOML schema cannot express.
    pub fn validate(&self) -> Result<(), ConfigError> {
        // Validate rule codes in select/exclude.
        for code in &self.rules.select {
            if !is_valid_rule_code(code) {
                return Err(ConfigError::InvalidRuleCode(code.clone()));
            }
        }
        for code in &self.rules.exclude {
            if !is_valid_rule_code(code) {
                return Err(ConfigError::InvalidRuleCode(code.clone()));
            }
        }

        // Validate severity override keys and values.
        for (code, severity) in &self.rules.severity {
            if !is_valid_rule_code(code) {
                return Err(ConfigError::InvalidRuleCode(code.clone()));
            }
            if !is_valid_severity(severity) {
                return Err(ConfigError::InvalidSeverity {
                    rule: code.clone(),
                    severity: severity.clone(),
                });
            }
        }

        // Validate rule-specific config keys.
        for code in self.rules.config.keys() {
            if !is_valid_rule_code(code) {
                return Err(ConfigError::InvalidRuleCode(code.clone()));
            }
        }

        // Validate glob patterns compile.
        for pattern in &self.files.include {
            globset::Glob::new(pattern)
                .map_err(|e| ConfigError::InvalidGlob(pattern.clone(), e.to_string()))?;
        }
        for pattern in &self.files.exclude {
            globset::Glob::new(pattern)
                .map_err(|e| ConfigError::InvalidGlob(pattern.clone(), e.to_string()))?;
        }

        // Validate output format string if present.
        if let Some(ref fmt) = self.output.format {
            if !["text", "concise", "json", "github", "sarif"].contains(&fmt.as_str()) {
                return Err(ConfigError::InvalidFormat(fmt.clone()));
            }
        }

        // Validate max_diagnostics > 0 if set.
        if let Some(max) = self.output.max_diagnostics {
            if max == 0 {
                return Err(ConfigError::InvalidMaxDiagnostics);
            }
        }

        Ok(())
    }

    /// Generate a default `.brrr-lint.toml` config as a string.
    pub fn default_toml() -> &'static str {
        r#"# brrr-lint configuration file
# https://github.com/grigorye/brrr-lint

# Rule selection and severity overrides.
[rules]
# Enable specific rules only (empty = all rules enabled):
# select = ["FST001", "FST003", "FST004"]
#
# Exclude specific rules:
# exclude = ["FST014"]

# Override severity per rule (error, warning, info, hint):
# [rules.severity]
# FST003 = "error"
# FST013 = "hint"

# Per-rule configuration:
# [rules.config.FST007]
# max_z3rlimit = 100

# File include/exclude glob patterns.
[files]
# include = ["src/**/*.fst", "src/**/*.fsti"]
# exclude = ["vendor/**", "generated/**"]

# Fix behavior settings.
[fix]
unsafe_fixes = false
backup = true

# Output settings.
[output]
# format = "text"
# max_diagnostics = 200
# quiet = false
# verbose = false
"#
    }

    /// Build a compiled `GlobMatcher` from the file include/exclude patterns.
    pub fn build_file_matcher(&self) -> Result<FileMatcher, ConfigError> {
        FileMatcher::new(&self.files)
    }
}

// ---------------------------------------------------------------------------
// File matching
// ---------------------------------------------------------------------------

/// Compiled glob matcher for file include/exclude patterns.
pub struct FileMatcher {
    include: Option<globset::GlobSet>,
    exclude: Option<globset::GlobSet>,
}

impl FileMatcher {
    /// Build from a `FilesConfig`.
    pub fn new(files: &FilesConfig) -> Result<Self, ConfigError> {
        let include = if files.include.is_empty() {
            None
        } else {
            let mut builder = globset::GlobSetBuilder::new();
            for pattern in &files.include {
                builder.add(
                    globset::Glob::new(pattern)
                        .map_err(|e| ConfigError::InvalidGlob(pattern.clone(), e.to_string()))?,
                );
            }
            Some(
                builder
                    .build()
                    .map_err(|e| ConfigError::InvalidGlob("(build)".into(), e.to_string()))?,
            )
        };

        let exclude = if files.exclude.is_empty() {
            None
        } else {
            let mut builder = globset::GlobSetBuilder::new();
            for pattern in &files.exclude {
                builder.add(
                    globset::Glob::new(pattern)
                        .map_err(|e| ConfigError::InvalidGlob(pattern.clone(), e.to_string()))?,
                );
            }
            Some(
                builder
                    .build()
                    .map_err(|e| ConfigError::InvalidGlob("(build)".into(), e.to_string()))?,
            )
        };

        Ok(Self { include, exclude })
    }

    /// Check whether a file path should be linted.
    ///
    /// Logic:
    /// 1. If exclude patterns exist and path matches any, return false.
    /// 2. If include patterns exist and path matches none, return false.
    /// 3. Otherwise return true.
    pub fn is_included(&self, path: &Path) -> bool {
        if let Some(ref exclude) = self.exclude {
            if exclude.is_match(path) {
                return false;
            }
        }
        if let Some(ref include) = self.include {
            return include.is_match(path);
        }
        true
    }
}

// ---------------------------------------------------------------------------
// Config file discovery
// ---------------------------------------------------------------------------

/// Name of the config file.
pub const CONFIG_FILE_NAME: &str = ".brrr-lint.toml";

/// Discover a `.brrr-lint.toml` by walking up from `start_dir` to the
/// repository root (directory containing `.git`).
///
/// Returns `None` if no config file is found before reaching the filesystem
/// root or the `.git` boundary.
pub fn discover_config(start_dir: &Path) -> Option<PathBuf> {
    let mut current = if start_dir.is_file() {
        start_dir.parent()?.to_path_buf()
    } else {
        start_dir.to_path_buf()
    };

    loop {
        let candidate = current.join(CONFIG_FILE_NAME);
        if candidate.is_file() {
            return Some(candidate);
        }

        // Stop at .git root (the config should live at or below the repo root).
        if current.join(".git").exists() {
            return None;
        }

        match current.parent() {
            Some(parent) if parent != current => {
                current = parent.to_path_buf();
            }
            _ => return None,
        }
    }
}

/// Discover and load the config file, returning the parsed config and
/// its path. Returns `Ok(None)` if no config file is found.
pub fn discover_and_load_config(start_dir: &Path) -> Result<Option<(LintFileConfig, PathBuf)>, ConfigError> {
    match discover_config(start_dir) {
        Some(path) => {
            let config = LintFileConfig::load(&path)?;
            Ok(Some((config, path)))
        }
        None => Ok(None),
    }
}

// ---------------------------------------------------------------------------
// Validation helpers
// ---------------------------------------------------------------------------

/// Known rule code prefixes + numbers.
fn is_valid_rule_code(code: &str) -> bool {
    let upper = code.to_uppercase();
    if !upper.starts_with("FST") {
        return false;
    }
    let num_part = &upper[3..];
    if num_part.is_empty() {
        return false;
    }
    // Must be digits and within the known range.
    if let Ok(n) = num_part.parse::<u32>() {
        (1..=19).contains(&n)
    } else {
        false
    }
}

fn is_valid_severity(s: &str) -> bool {
    matches!(s.to_lowercase().as_str(), "error" | "warning" | "info" | "hint")
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from config file operations.
#[derive(Debug)]
pub enum ConfigError {
    /// I/O error reading the config file.
    Io(PathBuf, std::io::Error),
    /// TOML parse error.
    Parse(toml::de::Error),
    /// Unknown rule code in config.
    InvalidRuleCode(String),
    /// Invalid severity string.
    InvalidSeverity { rule: String, severity: String },
    /// Invalid glob pattern.
    InvalidGlob(String, String),
    /// Invalid output format string.
    InvalidFormat(String),
    /// max_diagnostics must be >= 1.
    InvalidMaxDiagnostics,
}

impl std::fmt::Display for ConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConfigError::Io(path, err) => {
                write!(f, "failed to read {}: {}", path.display(), err)
            }
            ConfigError::Parse(err) => write!(f, "TOML parse error: {}", err),
            ConfigError::InvalidRuleCode(code) => {
                write!(
                    f,
                    "unknown rule code '{}' in config (valid: FST001..FST019)",
                    code
                )
            }
            ConfigError::InvalidSeverity { rule, severity } => {
                write!(
                    f,
                    "invalid severity '{}' for rule {} (valid: error, warning, info, hint)",
                    severity, rule
                )
            }
            ConfigError::InvalidGlob(pattern, err) => {
                write!(f, "invalid glob pattern '{}': {}", pattern, err)
            }
            ConfigError::InvalidFormat(fmt) => {
                write!(
                    f,
                    "invalid output format '{}' (valid: text, concise, json, github, sarif)",
                    fmt
                )
            }
            ConfigError::InvalidMaxDiagnostics => {
                write!(f, "max_diagnostics must be >= 1")
            }
        }
    }
}

impl std::error::Error for ConfigError {}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_minimal_config() {
        let config = LintFileConfig::parse("").unwrap();
        assert_eq!(config, LintFileConfig::default());
    }

    #[test]
    fn parse_full_config() {
        let toml = r#"
[rules]
select = ["FST001", "FST003"]
exclude = ["FST014"]

[rules.severity]
FST003 = "error"
FST013 = "hint"

[files]
include = ["src/**/*.fst"]
exclude = ["vendor/**"]

[fix]
unsafe_fixes = true
backup = false

[output]
format = "json"
max_diagnostics = 100
quiet = true
verbose = false
"#;
        let config = LintFileConfig::parse(toml).unwrap();
        config.validate().unwrap();

        assert_eq!(config.rules.select, vec!["FST001", "FST003"]);
        assert_eq!(config.rules.exclude, vec!["FST014"]);
        assert_eq!(
            config.rules.severity.get("FST003"),
            Some(&"error".to_string())
        );
        assert_eq!(config.files.include, vec!["src/**/*.fst"]);
        assert_eq!(config.files.exclude, vec!["vendor/**"]);
        assert!(config.fix.unsafe_fixes);
        assert!(!config.fix.backup);
        assert_eq!(config.output.format, Some("json".to_string()));
        assert_eq!(config.output.max_diagnostics, Some(100));
        assert!(config.output.quiet);
    }

    #[test]
    fn invalid_rule_code_rejected() {
        let toml = r#"
[rules]
select = ["BOGUS"]
"#;
        let config = LintFileConfig::parse(toml).unwrap();
        let err = config.validate().unwrap_err();
        assert!(err.to_string().contains("unknown rule code 'BOGUS'"));
    }

    #[test]
    fn invalid_severity_rejected() {
        let toml = r#"
[rules.severity]
FST001 = "fatal"
"#;
        let config = LintFileConfig::parse(toml).unwrap();
        let err = config.validate().unwrap_err();
        assert!(err.to_string().contains("invalid severity 'fatal'"));
    }

    #[test]
    fn invalid_glob_rejected() {
        let toml = r#"
[files]
include = ["[invalid"]
"#;
        let config = LintFileConfig::parse(toml).unwrap();
        let err = config.validate().unwrap_err();
        assert!(err.to_string().contains("invalid glob pattern"));
    }

    #[test]
    fn invalid_format_rejected() {
        let toml = r#"
[output]
format = "xml"
"#;
        let config = LintFileConfig::parse(toml).unwrap();
        let err = config.validate().unwrap_err();
        assert!(err.to_string().contains("invalid output format 'xml'"));
    }

    #[test]
    fn max_diagnostics_zero_rejected() {
        let toml = r#"
[output]
max_diagnostics = 0
"#;
        let config = LintFileConfig::parse(toml).unwrap();
        let err = config.validate().unwrap_err();
        assert!(err.to_string().contains("max_diagnostics must be >= 1"));
    }

    #[test]
    fn unknown_key_rejected() {
        let toml = r#"
[rules]
bogus_key = true
"#;
        let err = LintFileConfig::parse(toml).unwrap_err();
        assert!(matches!(err, ConfigError::Parse(_)));
    }

    #[test]
    fn default_fix_config_has_backup_true() {
        let config = FixConfig::default();
        assert!(config.backup);
        assert!(!config.unsafe_fixes);
    }

    #[test]
    fn file_matcher_include_only() {
        let files = FilesConfig {
            include: vec!["src/**/*.fst".to_string()],
            exclude: vec![],
        };
        let matcher = FileMatcher::new(&files).unwrap();
        assert!(matcher.is_included(Path::new("src/core/Foo.fst")));
        assert!(!matcher.is_included(Path::new("vendor/Bar.fst")));
    }

    #[test]
    fn file_matcher_exclude_only() {
        let files = FilesConfig {
            include: vec![],
            exclude: vec!["vendor/**".to_string()],
        };
        let matcher = FileMatcher::new(&files).unwrap();
        assert!(matcher.is_included(Path::new("src/core/Foo.fst")));
        assert!(!matcher.is_included(Path::new("vendor/Bar.fst")));
    }

    #[test]
    fn file_matcher_include_and_exclude() {
        let files = FilesConfig {
            include: vec!["src/**/*.fst".to_string()],
            exclude: vec!["src/generated/**".to_string()],
        };
        let matcher = FileMatcher::new(&files).unwrap();
        assert!(matcher.is_included(Path::new("src/core/Foo.fst")));
        assert!(!matcher.is_included(Path::new("src/generated/Auto.fst")));
        assert!(!matcher.is_included(Path::new("vendor/Bar.fst")));
    }

    #[test]
    fn file_matcher_empty_passes_all() {
        let files = FilesConfig::default();
        let matcher = FileMatcher::new(&files).unwrap();
        assert!(matcher.is_included(Path::new("anything.fst")));
        assert!(matcher.is_included(Path::new("deep/nested/path.fsti")));
    }

    #[test]
    fn discover_config_finds_file_in_start_dir() {
        let tmp = tempfile::tempdir().unwrap();
        // Create .git so the search stops here.
        std::fs::create_dir(tmp.path().join(".git")).unwrap();
        std::fs::write(tmp.path().join(CONFIG_FILE_NAME), "").unwrap();

        let found = discover_config(tmp.path());
        assert!(found.is_some());
        assert_eq!(found.unwrap(), tmp.path().join(CONFIG_FILE_NAME));
    }

    #[test]
    fn discover_config_walks_up() {
        let tmp = tempfile::tempdir().unwrap();
        // Create .git at root.
        std::fs::create_dir(tmp.path().join(".git")).unwrap();
        std::fs::write(tmp.path().join(CONFIG_FILE_NAME), "").unwrap();

        // Create nested directory.
        let nested = tmp.path().join("src").join("core");
        std::fs::create_dir_all(&nested).unwrap();

        let found = discover_config(&nested);
        assert!(found.is_some());
        assert_eq!(found.unwrap(), tmp.path().join(CONFIG_FILE_NAME));
    }

    #[test]
    fn discover_config_stops_at_git_root() {
        let tmp = tempfile::tempdir().unwrap();
        // Create .git at root with no config file.
        std::fs::create_dir(tmp.path().join(".git")).unwrap();

        let nested = tmp.path().join("src");
        std::fs::create_dir_all(&nested).unwrap();

        let found = discover_config(&nested);
        assert!(found.is_none());
    }

    #[test]
    fn discover_and_load_returns_none_when_no_config() {
        let tmp = tempfile::tempdir().unwrap();
        std::fs::create_dir(tmp.path().join(".git")).unwrap();

        let result = discover_and_load_config(tmp.path()).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn discover_and_load_parses_valid_config() {
        let tmp = tempfile::tempdir().unwrap();
        std::fs::create_dir(tmp.path().join(".git")).unwrap();
        std::fs::write(
            tmp.path().join(CONFIG_FILE_NAME),
            "[rules]\nselect = [\"FST001\"]\n",
        )
        .unwrap();

        let result = discover_and_load_config(tmp.path()).unwrap();
        assert!(result.is_some());
        let (config, path) = result.unwrap();
        assert_eq!(config.rules.select, vec!["FST001"]);
        assert_eq!(path, tmp.path().join(CONFIG_FILE_NAME));
    }

    #[test]
    fn discover_and_load_rejects_invalid_config() {
        let tmp = tempfile::tempdir().unwrap();
        std::fs::create_dir(tmp.path().join(".git")).unwrap();
        std::fs::write(
            tmp.path().join(CONFIG_FILE_NAME),
            "[rules]\nselect = [\"BOGUS\"]\n",
        )
        .unwrap();

        let result = discover_and_load_config(tmp.path());
        assert!(result.is_err());
    }

    #[test]
    fn default_toml_is_valid() {
        let config = LintFileConfig::parse(LintFileConfig::default_toml()).unwrap();
        config.validate().unwrap();
    }

    #[test]
    fn rule_specific_config_parsed() {
        let toml = r#"
[rules.config.FST007]
max_z3rlimit = 100
warn_nonlinear = true
"#;
        let config = LintFileConfig::parse(toml).unwrap();
        config.validate().unwrap();

        let fst007 = config.rules.config.get("FST007").unwrap();
        assert!(fst007.is_table());
    }

    #[test]
    fn is_valid_rule_code_rejects_out_of_range() {
        assert!(!is_valid_rule_code("FST000"));
        assert!(!is_valid_rule_code("FST020"));
        assert!(!is_valid_rule_code("FST999"));
        assert!(!is_valid_rule_code("XYZ001"));
        assert!(!is_valid_rule_code("FST"));
        assert!(!is_valid_rule_code(""));
    }

    #[test]
    fn is_valid_rule_code_accepts_known_codes() {
        for i in 1..=19 {
            let code = format!("FST{:03}", i);
            assert!(is_valid_rule_code(&code), "expected {} to be valid", code);
        }
    }

    #[test]
    fn case_insensitive_rule_codes() {
        assert!(is_valid_rule_code("fst001"));
        assert!(is_valid_rule_code("Fst019"));
    }
}
