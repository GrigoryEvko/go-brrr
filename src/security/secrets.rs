//! Hardcoded secret and credential detection.
//!
//! Detects secrets embedded in source code including:
//! - API keys from major providers (AWS, GitHub, Slack, Stripe, Google, etc.)
//! - Private keys (RSA, EC, PGP)
//! - JWTs (JSON Web Tokens)
//! - Connection strings (database URLs with credentials)
//! - Generic patterns (password = "...", api_key = "...", etc.)
//! - High-entropy strings assigned to sensitive variables
//!
//! # False Positive Mitigation
//!
//! The detector ignores:
//! - Environment variable reads (`os.environ['API_KEY']`, `process.env.API_KEY`)
//! - Config file reads (`config.get('password')`)
//! - Placeholder values (`YOUR_API_KEY_HERE`, `changeme`, `xxx`, `TODO`)
//! - Test files (reduced severity)
//! - Example/documentation strings
//! - Empty or obviously fake values
//!
//! # Architecture
//!
//! The detector uses a multi-layer approach:
//! 1. **Provider Patterns**: High-confidence regex for known API key formats
//! 2. **Generic Patterns**: Assignment patterns for sensitive variable names
//! 3. **Entropy Analysis**: Shannon entropy for detecting random strings
//! 4. **Context Analysis**: AST context to filter false positives
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::security::secrets::{SecretsDetector, scan_secrets};
//!
//! // Scan a directory
//! let result = scan_secrets("./src", None)?;
//! for finding in result.findings {
//!     println!("[{}] {} at {}:{}",
//!         finding.severity,
//!         finding.secret_type,
//!         finding.location.file,
//!         finding.location.line
//!     );
//! }
//! ```

use std::collections::{HashMap, HashSet};
use std::path::Path;

use once_cell::sync::Lazy;
use regex::Regex;
use serde::{Deserialize, Serialize};

use crate::error::{BrrrError, Result};

// =============================================================================
// Types
// =============================================================================

/// Type of secret detected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SecretType {
    /// AWS Access Key ID (AKIA...)
    AwsAccessKey,
    /// AWS Secret Access Key
    AwsSecretKey,
    /// GitHub Personal Access Token (ghp_..., gho_..., ghu_..., ghs_..., ghr_...)
    GitHubToken,
    /// GitLab Personal Access Token (glpat-...)
    GitLabToken,
    /// Slack token (xox[baprs]-...)
    SlackToken,
    /// Stripe API key (sk_live_..., sk_test_..., rk_live_..., rk_test_...)
    StripeKey,
    /// Google API key (AIza...)
    GoogleApiKey,
    /// Google Cloud service account key (JSON with private_key)
    GoogleServiceAccount,
    /// Twilio API key or Auth token
    TwilioKey,
    /// SendGrid API key (SG....)
    SendGridKey,
    /// Mailgun API key
    MailgunKey,
    /// Heroku API key
    HerokuKey,
    /// npm token
    NpmToken,
    /// PyPI token
    PyPiToken,
    /// Discord token
    DiscordToken,
    /// Telegram Bot token
    TelegramToken,
    /// Firebase/FCM server key
    FirebaseKey,
    /// Azure storage/service key
    AzureKey,
    /// DigitalOcean token
    DigitalOceanToken,
    /// Datadog API key
    DatadogKey,
    /// OpenAI API key (sk-...)
    OpenAiKey,
    /// Anthropic API key (sk-ant-...)
    AnthropicKey,
    /// RSA/EC/DSA private key (-----BEGIN ... PRIVATE KEY-----)
    PrivateKey,
    /// PGP private key block
    PgpPrivateKey,
    /// SSH private key
    SshPrivateKey,
    /// JSON Web Token (eyJ...)
    Jwt,
    /// Database connection string with embedded credentials
    ConnectionString,
    /// Generic password assignment
    Password,
    /// Generic API key assignment
    ApiKey,
    /// Generic secret/token assignment
    GenericSecret,
    /// High-entropy string (potential secret)
    HighEntropyString,
}

impl std::fmt::Display for SecretType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SecretType::AwsAccessKey => write!(f, "AWS Access Key"),
            SecretType::AwsSecretKey => write!(f, "AWS Secret Access Key"),
            SecretType::GitHubToken => write!(f, "GitHub Token"),
            SecretType::GitLabToken => write!(f, "GitLab Token"),
            SecretType::SlackToken => write!(f, "Slack Token"),
            SecretType::StripeKey => write!(f, "Stripe API Key"),
            SecretType::GoogleApiKey => write!(f, "Google API Key"),
            SecretType::GoogleServiceAccount => write!(f, "Google Service Account Key"),
            SecretType::TwilioKey => write!(f, "Twilio Key"),
            SecretType::SendGridKey => write!(f, "SendGrid API Key"),
            SecretType::MailgunKey => write!(f, "Mailgun API Key"),
            SecretType::HerokuKey => write!(f, "Heroku API Key"),
            SecretType::NpmToken => write!(f, "npm Token"),
            SecretType::PyPiToken => write!(f, "PyPI Token"),
            SecretType::DiscordToken => write!(f, "Discord Token"),
            SecretType::TelegramToken => write!(f, "Telegram Bot Token"),
            SecretType::FirebaseKey => write!(f, "Firebase/FCM Key"),
            SecretType::AzureKey => write!(f, "Azure Key"),
            SecretType::DigitalOceanToken => write!(f, "DigitalOcean Token"),
            SecretType::DatadogKey => write!(f, "Datadog API Key"),
            SecretType::OpenAiKey => write!(f, "OpenAI API Key"),
            SecretType::AnthropicKey => write!(f, "Anthropic API Key"),
            SecretType::PrivateKey => write!(f, "Private Key"),
            SecretType::PgpPrivateKey => write!(f, "PGP Private Key"),
            SecretType::SshPrivateKey => write!(f, "SSH Private Key"),
            SecretType::Jwt => write!(f, "JSON Web Token"),
            SecretType::ConnectionString => write!(f, "Connection String"),
            SecretType::Password => write!(f, "Password"),
            SecretType::ApiKey => write!(f, "API Key"),
            SecretType::GenericSecret => write!(f, "Generic Secret"),
            SecretType::HighEntropyString => write!(f, "High-Entropy String"),
        }
    }
}

/// Severity level for secret findings.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Severity {
    /// Informational only (possible false positive)
    Info,
    /// Low severity (test files, examples, low entropy)
    Low,
    /// Medium severity (generic patterns, moderate confidence)
    Medium,
    /// High severity (provider-specific patterns, high confidence)
    High,
    /// Critical severity (private keys, production credentials)
    Critical,
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Severity::Info => write!(f, "INFO"),
            Severity::Low => write!(f, "LOW"),
            Severity::Medium => write!(f, "MEDIUM"),
            Severity::High => write!(f, "HIGH"),
            Severity::Critical => write!(f, "CRITICAL"),
        }
    }
}

/// Confidence level for the detection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Confidence {
    /// Low confidence (heuristic match, may be false positive)
    Low,
    /// Medium confidence (pattern match with some validation)
    Medium,
    /// High confidence (provider-specific pattern with format validation)
    High,
}

impl std::fmt::Display for Confidence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Confidence::Low => write!(f, "LOW"),
            Confidence::Medium => write!(f, "MEDIUM"),
            Confidence::High => write!(f, "HIGH"),
        }
    }
}

/// Location of a finding in source code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Location {
    /// File path
    pub file: String,
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed)
    pub column: usize,
    /// End line number (1-indexed)
    pub end_line: usize,
    /// End column number (1-indexed)
    pub end_column: usize,
}

/// A secret finding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecretFinding {
    /// Location in source code
    pub location: Location,
    /// Type of secret detected
    pub secret_type: SecretType,
    /// Severity level
    pub severity: Severity,
    /// Confidence level
    pub confidence: Confidence,
    /// Masked value (first and last few chars visible)
    pub masked_value: String,
    /// Variable name if detected via assignment
    pub variable_name: Option<String>,
    /// Human-readable description
    pub description: String,
    /// Suggested remediation
    pub remediation: String,
    /// Whether this is in a test file
    pub is_test_file: bool,
    /// Shannon entropy of the secret value
    pub entropy: Option<f64>,
}

/// Summary of secret scan results.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScanResult {
    /// All findings
    pub findings: Vec<SecretFinding>,
    /// Number of files scanned
    pub files_scanned: usize,
    /// Counts by secret type
    pub type_counts: HashMap<String, usize>,
    /// Counts by severity
    pub severity_counts: HashMap<String, usize>,
}

// =============================================================================
// Pattern Definitions
// =============================================================================

/// Provider-specific pattern with metadata.
struct ProviderPattern {
    regex: Regex,
    secret_type: SecretType,
    severity: Severity,
    confidence: Confidence,
    description: &'static str,
}

/// Generic assignment pattern.
struct GenericPattern {
    var_regex: Regex,
    secret_type: SecretType,
    min_value_length: usize,
    description: &'static str,
}

/// Compile provider-specific patterns.
static PROVIDER_PATTERNS: Lazy<Vec<ProviderPattern>> = Lazy::new(|| {
    vec![
        // AWS Access Key ID
        ProviderPattern {
            regex: Regex::new(r"(?i)\b(AKIA[0-9A-Z]{16})\b").expect("Invalid regex"),
            secret_type: SecretType::AwsAccessKey,
            severity: Severity::Critical,
            confidence: Confidence::High,
            description: "AWS Access Key ID detected",
        },
        // AWS Secret Access Key (40 chars, base64-like)
        ProviderPattern {
            regex: Regex::new(r#"(?i)(?:aws_secret_access_key|aws_secret_key|secret_access_key)\s*[=:]\s*["']?([A-Za-z0-9/+=]{40})["']?"#).expect("Invalid regex"),
            secret_type: SecretType::AwsSecretKey,
            severity: Severity::Critical,
            confidence: Confidence::High,
            description: "AWS Secret Access Key detected",
        },
        // GitHub tokens (multiple types)
        ProviderPattern {
            regex: Regex::new(r"\b(ghp_[a-zA-Z0-9]{36})\b").expect("Invalid regex"),
            secret_type: SecretType::GitHubToken,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "GitHub Personal Access Token (classic) detected",
        },
        ProviderPattern {
            regex: Regex::new(r"\b(gho_[a-zA-Z0-9]{36})\b").expect("Invalid regex"),
            secret_type: SecretType::GitHubToken,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "GitHub OAuth Access Token detected",
        },
        ProviderPattern {
            regex: Regex::new(r"\b(ghu_[a-zA-Z0-9]{36})\b").expect("Invalid regex"),
            secret_type: SecretType::GitHubToken,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "GitHub User-to-Server Token detected",
        },
        ProviderPattern {
            regex: Regex::new(r"\b(ghs_[a-zA-Z0-9]{36})\b").expect("Invalid regex"),
            secret_type: SecretType::GitHubToken,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "GitHub Server-to-Server Token detected",
        },
        ProviderPattern {
            regex: Regex::new(r"\b(ghr_[a-zA-Z0-9]{36})\b").expect("Invalid regex"),
            secret_type: SecretType::GitHubToken,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "GitHub Refresh Token detected",
        },
        ProviderPattern {
            regex: Regex::new(r"\b(github_pat_[a-zA-Z0-9]{22}_[a-zA-Z0-9]{59})\b").expect("Invalid regex"),
            secret_type: SecretType::GitHubToken,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "GitHub Fine-Grained Personal Access Token detected",
        },
        // GitLab tokens
        ProviderPattern {
            regex: Regex::new(r"\b(glpat-[a-zA-Z0-9_-]{20,})\b").expect("Invalid regex"),
            secret_type: SecretType::GitLabToken,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "GitLab Personal Access Token detected",
        },
        // Slack tokens
        ProviderPattern {
            regex: Regex::new(r"\b(xox[baprs]-[0-9a-zA-Z-]{10,})\b").expect("Invalid regex"),
            secret_type: SecretType::SlackToken,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "Slack Token detected",
        },
        // Stripe keys
        ProviderPattern {
            regex: Regex::new(r"\b(sk_live_[0-9a-zA-Z]{24,})\b").expect("Invalid regex"),
            secret_type: SecretType::StripeKey,
            severity: Severity::Critical,
            confidence: Confidence::High,
            description: "Stripe Live Secret Key detected",
        },
        ProviderPattern {
            regex: Regex::new(r"\b(sk_test_[0-9a-zA-Z]{24,})\b").expect("Invalid regex"),
            secret_type: SecretType::StripeKey,
            severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Stripe Test Secret Key detected",
        },
        ProviderPattern {
            regex: Regex::new(r"\b(rk_live_[0-9a-zA-Z]{24,})\b").expect("Invalid regex"),
            secret_type: SecretType::StripeKey,
            severity: Severity::Critical,
            confidence: Confidence::High,
            description: "Stripe Live Restricted Key detected",
        },
        // Google API key
        ProviderPattern {
            regex: Regex::new(r"\b(AIza[0-9A-Za-z_-]{35})\b").expect("Invalid regex"),
            secret_type: SecretType::GoogleApiKey,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "Google API Key detected",
        },
        // Twilio
        ProviderPattern {
            regex: Regex::new(r"\b(SK[0-9a-fA-F]{32})\b").expect("Invalid regex"),
            secret_type: SecretType::TwilioKey,
            severity: Severity::High,
            confidence: Confidence::Medium,
            description: "Twilio API Key detected",
        },
        // SendGrid
        ProviderPattern {
            regex: Regex::new(r"\b(SG\.[a-zA-Z0-9_-]{22}\.[a-zA-Z0-9_-]{43})\b").expect("Invalid regex"),
            secret_type: SecretType::SendGridKey,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "SendGrid API Key detected",
        },
        // npm tokens
        ProviderPattern {
            regex: Regex::new(r"\b(npm_[a-zA-Z0-9]{36})\b").expect("Invalid regex"),
            secret_type: SecretType::NpmToken,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "npm Access Token detected",
        },
        // PyPI tokens
        ProviderPattern {
            regex: Regex::new(r"\b(pypi-[a-zA-Z0-9_-]{50,})\b").expect("Invalid regex"),
            secret_type: SecretType::PyPiToken,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "PyPI API Token detected",
        },
        // Discord tokens (bot tokens and webhooks)
        ProviderPattern {
            regex: Regex::new(r"\b([MN][A-Za-z0-9]{23,}\.[A-Za-z0-9_-]{6}\.[A-Za-z0-9_-]{27,})\b").expect("Invalid regex"),
            secret_type: SecretType::DiscordToken,
            severity: Severity::High,
            confidence: Confidence::Medium,
            description: "Discord Bot Token detected",
        },
        // Telegram Bot tokens
        ProviderPattern {
            regex: Regex::new(r"\b(\d{8,10}:[a-zA-Z0-9_-]{35})\b").expect("Invalid regex"),
            secret_type: SecretType::TelegramToken,
            severity: Severity::High,
            confidence: Confidence::Medium,
            description: "Telegram Bot Token detected",
        },
        // Firebase/FCM
        ProviderPattern {
            regex: Regex::new(r"\b(AAAA[a-zA-Z0-9_-]{140,})\b").expect("Invalid regex"),
            secret_type: SecretType::FirebaseKey,
            severity: Severity::High,
            confidence: Confidence::Medium,
            description: "Firebase Cloud Messaging Server Key detected",
        },
        // Azure
        ProviderPattern {
            regex: Regex::new(r#"(?i)(?:AccountKey|SharedAccessKey)\s*=\s*([A-Za-z0-9+/=]{44,})"#).expect("Invalid regex"),
            secret_type: SecretType::AzureKey,
            severity: Severity::Critical,
            confidence: Confidence::High,
            description: "Azure Storage/Service Key detected",
        },
        // DigitalOcean
        ProviderPattern {
            regex: Regex::new(r"\b(dop_v1_[a-f0-9]{64})\b").expect("Invalid regex"),
            secret_type: SecretType::DigitalOceanToken,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "DigitalOcean Personal Access Token detected",
        },
        ProviderPattern {
            regex: Regex::new(r"\b(doo_v1_[a-f0-9]{64})\b").expect("Invalid regex"),
            secret_type: SecretType::DigitalOceanToken,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "DigitalOcean OAuth Token detected",
        },
        // Datadog
        ProviderPattern {
            regex: Regex::new(r"\b([a-f0-9]{32})\b").expect("Invalid regex"),
            secret_type: SecretType::DatadogKey,
            severity: Severity::Medium,
            confidence: Confidence::Low,
            description: "Possible Datadog API Key detected (32-char hex)",
        },
        // OpenAI
        ProviderPattern {
            regex: Regex::new(r"\b(sk-[a-zA-Z0-9]{20}T3BlbkFJ[a-zA-Z0-9]{20})\b").expect("Invalid regex"),
            secret_type: SecretType::OpenAiKey,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "OpenAI API Key detected",
        },
        ProviderPattern {
            regex: Regex::new(r"\b(sk-proj-[a-zA-Z0-9_-]{40,})\b").expect("Invalid regex"),
            secret_type: SecretType::OpenAiKey,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "OpenAI Project API Key detected",
        },
        // Anthropic
        ProviderPattern {
            regex: Regex::new(r"\b(sk-ant-api[0-9]{2}-[a-zA-Z0-9_-]{90,})\b").expect("Invalid regex"),
            secret_type: SecretType::AnthropicKey,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "Anthropic API Key detected",
        },
        // Heroku
        ProviderPattern {
            regex: Regex::new(r#"(?i)heroku[a-z_-]*\s*[=:]\s*["']?([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})["']?"#).expect("Invalid regex"),
            secret_type: SecretType::HerokuKey,
            severity: Severity::High,
            confidence: Confidence::Medium,
            description: "Heroku API Key detected",
        },
        // Private keys (RSA, EC, DSA, etc.)
        ProviderPattern {
            regex: Regex::new(r"-----BEGIN\s+(?:RSA\s+)?PRIVATE\s+KEY-----").expect("Invalid regex"),
            secret_type: SecretType::PrivateKey,
            severity: Severity::Critical,
            confidence: Confidence::High,
            description: "RSA Private Key detected",
        },
        ProviderPattern {
            regex: Regex::new(r"-----BEGIN\s+EC\s+PRIVATE\s+KEY-----").expect("Invalid regex"),
            secret_type: SecretType::PrivateKey,
            severity: Severity::Critical,
            confidence: Confidence::High,
            description: "EC Private Key detected",
        },
        ProviderPattern {
            regex: Regex::new(r"-----BEGIN\s+DSA\s+PRIVATE\s+KEY-----").expect("Invalid regex"),
            secret_type: SecretType::PrivateKey,
            severity: Severity::Critical,
            confidence: Confidence::High,
            description: "DSA Private Key detected",
        },
        ProviderPattern {
            regex: Regex::new(r"-----BEGIN\s+ENCRYPTED\s+PRIVATE\s+KEY-----").expect("Invalid regex"),
            secret_type: SecretType::PrivateKey,
            severity: Severity::High,
            confidence: Confidence::High,
            description: "Encrypted Private Key detected (still sensitive)",
        },
        ProviderPattern {
            regex: Regex::new(r"-----BEGIN\s+OPENSSH\s+PRIVATE\s+KEY-----").expect("Invalid regex"),
            secret_type: SecretType::SshPrivateKey,
            severity: Severity::Critical,
            confidence: Confidence::High,
            description: "OpenSSH Private Key detected",
        },
        // PGP private key
        ProviderPattern {
            regex: Regex::new(r"-----BEGIN\s+PGP\s+PRIVATE\s+KEY\s+BLOCK-----").expect("Invalid regex"),
            secret_type: SecretType::PgpPrivateKey,
            severity: Severity::Critical,
            confidence: Confidence::High,
            description: "PGP Private Key Block detected",
        },
        // JWT (three base64url-encoded parts separated by dots)
        ProviderPattern {
            regex: Regex::new(r"\b(eyJ[A-Za-z0-9_-]{10,}\.eyJ[A-Za-z0-9_-]{10,}\.[A-Za-z0-9_-]+)\b").expect("Invalid regex"),
            secret_type: SecretType::Jwt,
            severity: Severity::Medium,
            confidence: Confidence::High,
            description: "JSON Web Token detected",
        },
        // Connection strings with credentials
        ProviderPattern {
            regex: Regex::new(r##"(?i)(postgres(?:ql)?|mysql|mongodb(?:\+srv)?|redis|amqp)://[^:]+:[^@]+@[^\s"'`]+"##).expect("Invalid regex"),
            secret_type: SecretType::ConnectionString,
            severity: Severity::Critical,
            confidence: Confidence::High,
            description: "Database connection string with embedded credentials detected",
        },
    ]
});

/// Compile generic assignment patterns.
static GENERIC_PATTERNS: Lazy<Vec<GenericPattern>> = Lazy::new(|| {
    vec![
        GenericPattern {
            var_regex: Regex::new(r#"(?i)(?:^|[^a-zA-Z0-9_])(?:password|passwd|pwd)\s*[=:]\s*["']([^"']+)["']"#).expect("Invalid regex"),
            secret_type: SecretType::Password,
            min_value_length: 4,
            description: "Hardcoded password detected",
        },
        GenericPattern {
            var_regex: Regex::new(r#"(?i)(?:^|[^a-zA-Z0-9_])(?:api_?key|apikey|api_?token)\s*[=:]\s*["']([^"']+)["']"#).expect("Invalid regex"),
            secret_type: SecretType::ApiKey,
            min_value_length: 8,
            description: "Hardcoded API key detected",
        },
        GenericPattern {
            var_regex: Regex::new(r#"(?i)(?:^|[^a-zA-Z0-9_])(?:secret|secret_?key|private_?key|auth_?key|access_?key)\s*[=:]\s*["']([^"']+)["']"#).expect("Invalid regex"),
            secret_type: SecretType::GenericSecret,
            min_value_length: 8,
            description: "Hardcoded secret detected",
        },
        GenericPattern {
            var_regex: Regex::new(r#"(?i)(?:^|[^a-zA-Z0-9_])(?:token|auth_?token|access_?token|bearer_?token)\s*[=:]\s*["']([^"']+)["']"#).expect("Invalid regex"),
            secret_type: SecretType::GenericSecret,
            min_value_length: 8,
            description: "Hardcoded token detected",
        },
        GenericPattern {
            var_regex: Regex::new(r#"(?i)(?:^|[^a-zA-Z0-9_])(?:credentials?|creds?)\s*[=:]\s*["']([^"']+)["']"#).expect("Invalid regex"),
            secret_type: SecretType::GenericSecret,
            min_value_length: 6,
            description: "Hardcoded credentials detected",
        },
    ]
});

/// Placeholder values that should be ignored.
static PLACEHOLDER_PATTERNS: Lazy<Vec<Regex>> = Lazy::new(|| {
    vec![
        // Explicit placeholders
        Regex::new(r"(?i)^(your[_-]?api[_-]?key|your[_-]?secret|your[_-]?token|your[_-]?password)").expect("Invalid regex"),
        Regex::new(r"(?i)(changeme|change[_-]?me|replace[_-]?me|insert[_-]?here|put[_-]?here|add[_-]?here)").expect("Invalid regex"),
        Regex::new(r"(?i)^(xxx+|placeholder|dummy|fake|test|example|sample|demo)").expect("Invalid regex"),
        Regex::new(r"(?i)(todo|fixme|tbd|none|null|undefined|empty)").expect("Invalid regex"),
        // Common example patterns
        Regex::new(r"(?i)^<[^>]+>$").expect("Invalid regex"),  // <your-api-key>
        Regex::new(r"(?i)^\$\{[^}]+\}$").expect("Invalid regex"),  // ${API_KEY}
        Regex::new(r"(?i)^\{\{[^}]+\}\}$").expect("Invalid regex"),  // {{api_key}}
        Regex::new(r"(?i)^%[^%]+%$").expect("Invalid regex"),  // %API_KEY%
        // Repeating characters (detected via entropy check in is_placeholder)
        // Note: backreferences not supported in Rust regex, handled programmatically
        // Obvious fakes
        Regex::new(r"^(1234|abcd|pass|password|secret|token|key)").expect("Invalid regex"),
    ]
});

/// Patterns indicating environment variable reads (not hardcoded secrets).
static ENV_VAR_PATTERNS: Lazy<Vec<Regex>> = Lazy::new(|| {
    vec![
        // Python
        Regex::new(r#"os\.environ\s*\["#).expect("Invalid regex"),
        Regex::new(r#"os\.environ\.get\s*\("#).expect("Invalid regex"),
        Regex::new(r#"os\.getenv\s*\("#).expect("Invalid regex"),
        Regex::new(r#"environ\s*\["#).expect("Invalid regex"),
        // JavaScript/TypeScript
        Regex::new(r#"process\.env\."#).expect("Invalid regex"),
        Regex::new(r#"process\.env\["#).expect("Invalid regex"),
        Regex::new(r#"Deno\.env\.get\("#).expect("Invalid regex"),
        Regex::new(r#"import\.meta\.env\."#).expect("Invalid regex"),
        // Go
        Regex::new(r#"os\.Getenv\s*\("#).expect("Invalid regex"),
        Regex::new(r#"os\.LookupEnv\s*\("#).expect("Invalid regex"),
        // Rust
        Regex::new(r#"std::env::var\s*\("#).expect("Invalid regex"),
        Regex::new(r#"env::var\s*\("#).expect("Invalid regex"),
        Regex::new(r#"env!\s*\("#).expect("Invalid regex"),
        // Java
        Regex::new(r#"System\.getenv\s*\("#).expect("Invalid regex"),
        Regex::new(r#"System\.getProperty\s*\("#).expect("Invalid regex"),
        // Ruby
        Regex::new(r#"ENV\s*\["#).expect("Invalid regex"),
        Regex::new(r#"ENV\.fetch\s*\("#).expect("Invalid regex"),
        // C/C++
        Regex::new(r#"getenv\s*\("#).expect("Invalid regex"),
        // .NET
        Regex::new(r#"Environment\.GetEnvironmentVariable\s*\("#).expect("Invalid regex"),
    ]
});

/// Patterns indicating config file reads.
static CONFIG_READ_PATTERNS: Lazy<Vec<Regex>> = Lazy::new(|| {
    vec![
        Regex::new(r#"config\s*\.\s*get\s*\("#).expect("Invalid regex"),
        Regex::new(r#"config\s*\["#).expect("Invalid regex"),
        Regex::new(r#"settings\s*\.\s*get\s*\("#).expect("Invalid regex"),
        Regex::new(r#"settings\s*\["#).expect("Invalid regex"),
        Regex::new(r#"\.config\("#).expect("Invalid regex"),
        Regex::new(r#"viper\.Get"#).expect("Invalid regex"),
        Regex::new(r#"configuration\."#).expect("Invalid regex"),
    ]
});

// =============================================================================
// Entropy Calculation
// =============================================================================

/// Calculate Shannon entropy of a string using SIMD-optimized byte histogram.
///
/// Entropy is a measure of randomness. High entropy strings (> 4.5 bits/char)
/// are likely to be secrets like API keys or passwords.
///
/// # Algorithm
///
/// Uses a 256-element byte histogram for O(1) frequency lookups instead of HashMap.
/// On x86_64 with AVX2, uses SIMD to accelerate histogram building by processing
/// 32 bytes at a time with vectorized comparisons.
fn calculate_entropy(s: &str) -> f64 {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return 0.0;
    }

    // Build byte histogram using SIMD when available
    let histogram = build_byte_histogram(bytes);

    // Calculate entropy from histogram
    let len = bytes.len() as f64;
    let mut entropy = 0.0;

    for &count in &histogram {
        if count > 0 {
            let probability = f64::from(count) / len;
            entropy -= probability * probability.log2();
        }
    }

    entropy
}

/// Build a 256-element byte histogram.
///
/// Dispatches to SIMD or scalar implementation based on platform and CPU features.
#[inline]
fn build_byte_histogram(bytes: &[u8]) -> [u32; 256] {
    #[cfg(target_arch = "x86_64")]
    {
        if is_x86_feature_detected!("avx2") {
            // SAFETY: AVX2 feature check ensures the intrinsics are available
            return unsafe { build_byte_histogram_avx2(bytes) };
        }
    }

    build_byte_histogram_scalar(bytes)
}

/// Scalar implementation of byte histogram building.
///
/// Uses a fixed 256-element array instead of HashMap for O(1) updates.
#[inline]
fn build_byte_histogram_scalar(bytes: &[u8]) -> [u32; 256] {
    let mut histogram = [0u32; 256];

    // Process 4 bytes at a time for better instruction-level parallelism
    let chunks = bytes.chunks_exact(4);
    let remainder = chunks.remainder();

    for chunk in chunks {
        histogram[chunk[0] as usize] += 1;
        histogram[chunk[1] as usize] += 1;
        histogram[chunk[2] as usize] += 1;
        histogram[chunk[3] as usize] += 1;
    }

    for &b in remainder {
        histogram[b as usize] += 1;
    }

    histogram
}

/// AVX2 SIMD implementation of byte histogram building.
///
/// Processes 32 bytes at a time using SIMD comparisons (u8x32).
/// For each unique byte value, uses vectorized comparison and popcount
/// to count occurrences across 32-byte chunks simultaneously.
///
/// # Safety
///
/// Caller must ensure AVX2 is available on the CPU.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn build_byte_histogram_avx2(bytes: &[u8]) -> [u32; 256] {
    use std::arch::x86_64::{
        __m256i, _mm256_cmpeq_epi8, _mm256_loadu_si256, _mm256_movemask_epi8, _mm256_set1_epi8,
    };

    let mut histogram = [0u32; 256];
    let len = bytes.len();

    // SIMD setup overhead makes scalar faster for short strings
    if len < 128 {
        return build_byte_histogram_scalar(bytes);
    }

    let ptr = bytes.as_ptr();
    let aligned_len = len & !31; // Round down to multiple of 32

    // Process 32 bytes at a time
    for offset in (0..aligned_len).step_by(32) {
        // Load 32 bytes into AVX2 register (u8x32)
        let data = _mm256_loadu_si256(ptr.add(offset).cast::<__m256i>());

        // Count occurrences of each byte value using SIMD comparisons
        // Each comparison checks 32 bytes in parallel
        for byte_val in 0u8..=255u8 {
            // Broadcast single byte to all 32 lanes
            let pattern = _mm256_set1_epi8(byte_val as i8);
            // Compare: each lane becomes 0xFF if match, 0x00 otherwise
            let cmp = _mm256_cmpeq_epi8(data, pattern);
            // Extract MSB of each byte into 32-bit mask
            let mask = _mm256_movemask_epi8(cmp) as u32;
            // Count set bits = number of matches in this 32-byte chunk
            histogram[byte_val as usize] += mask.count_ones();
        }
    }

    // Handle remaining bytes with scalar code
    for &b in bytes.get_unchecked(aligned_len..) {
        histogram[b as usize] += 1;
    }

    histogram
}

/// Minimum entropy threshold for high-entropy detection.
const MIN_ENTROPY_THRESHOLD: f64 = 4.5;

/// Minimum length for high-entropy string detection.
const MIN_ENTROPY_STRING_LENGTH: usize = 16;

// =============================================================================
// Detector Implementation
// =============================================================================

/// Secrets detector for multiple languages.
pub struct SecretsDetector {
    /// Whether to skip test files
    skip_test_files: bool,
    /// Whether to include high-entropy detection
    include_entropy: bool,
    /// Minimum entropy threshold
    entropy_threshold: f64,
}

impl Default for SecretsDetector {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// SIMD Utilities
// =============================================================================

/// Check if all bytes in a slice are identical.
///
/// Uses u8x32 to compare 32 bytes at a time with early exit on first mismatch.
/// Falls back to scalar comparison for the remainder.
///
/// # Performance
/// - O(n/32) SIMD comparisons for the main loop
/// - Early exit on first mismatch avoids unnecessary work
/// - Zero allocations
#[inline]
#[allow(clippy::manual_is_ascii_check)] // SIMD optimization is intentional
fn is_all_same_byte(bytes: &[u8]) -> bool {
    use std::simd::{cmp::SimdPartialEq, u8x32};

    if bytes.is_empty() {
        return true;
    }

    let first = bytes[0];
    let len = bytes.len();

    // For very short inputs, scalar is faster (no SIMD setup overhead)
    if len < 32 {
        return bytes.iter().all(|&b| b == first);
    }

    // SIMD: splat first byte across all 32 lanes
    let first_vec = u8x32::splat(first);
    let mut offset = 0_usize;

    // Process 32 bytes at a time
    while offset + 32 <= len {
        // SAFETY: bounds check guarantees bytes[offset..offset+32] is valid
        let chunk = u8x32::from_slice(&bytes[offset..offset + 32]);
        let mask = chunk.simd_eq(first_vec);

        // Early exit: if not all lanes match, bytes are not uniform
        // All lanes equal means lower 32 bits are all 1s (0xFFFF_FFFF)
        // to_bitmask() returns u64, but only lower 32 bits are meaningful for u8x32
        if mask.to_bitmask() != 0xFFFF_FFFF_u64 {
            return false;
        }
        offset += 32;
    }

    // Scalar: handle remaining bytes (0..31)
    bytes[offset..].iter().all(|&b| b == first)
}

/// Count non-whitespace bytes in a string using SIMD.
///
/// Uses u8x32 to check 32 bytes at a time for ASCII whitespace characters:
/// space (0x20), tab (0x09), newline (0x0A), carriage return (0x0D).
/// Subtracts whitespace count from total length to get non-whitespace count.
///
/// # Performance
/// - O(n/32) SIMD operations for the main loop
/// - Processes 32 bytes per iteration using parallel comparison
/// - Zero allocations
///
/// # Note
/// This counts bytes, not Unicode code points. For ASCII-heavy content like
/// source code and secrets, this is equivalent and significantly faster than
/// iterating over chars.
#[inline]
fn count_non_whitespace_simd(s: &str) -> usize {
    use std::simd::{cmp::SimdPartialEq, u8x32};

    let bytes = s.as_bytes();
    let len = bytes.len();

    // For short inputs, scalar is faster (no SIMD setup overhead)
    if len < 32 {
        return bytes
            .iter()
            .filter(|&&b| !matches!(b, b' ' | b'\t' | b'\n' | b'\r'))
            .count();
    }

    // SIMD constants: splat each whitespace byte across all 32 lanes
    let space = u8x32::splat(b' '); // 0x20
    let tab = u8x32::splat(b'\t'); // 0x09
    let newline = u8x32::splat(b'\n'); // 0x0A
    let cr = u8x32::splat(b'\r'); // 0x0D

    let mut whitespace_count: usize = 0;
    let mut offset = 0_usize;

    // Process 32 bytes at a time
    while offset + 32 <= len {
        let chunk = u8x32::from_slice(&bytes[offset..offset + 32]);

        // Create masks for each whitespace character (parallel comparison)
        let is_space = chunk.simd_eq(space);
        let is_tab = chunk.simd_eq(tab);
        let is_newline = chunk.simd_eq(newline);
        let is_cr = chunk.simd_eq(cr);

        // Combine masks: true if byte matches any whitespace character
        let is_whitespace = is_space | is_tab | is_newline | is_cr;

        // Count set bits in bitmask (each set bit = one whitespace byte)
        // to_bitmask() returns u64, lower 32 bits are meaningful for u8x32
        whitespace_count += is_whitespace.to_bitmask().count_ones() as usize;

        offset += 32;
    }

    // Scalar: handle remaining bytes (0..31)
    for &b in &bytes[offset..] {
        if matches!(b, b' ' | b'\t' | b'\n' | b'\r') {
            whitespace_count += 1;
        }
    }

    // Return non-whitespace count by subtracting whitespace from total
    len - whitespace_count
}

impl SecretsDetector {
    /// Create a new secrets detector with default settings.
    pub fn new() -> Self {
        Self {
            skip_test_files: false,
            include_entropy: true,
            entropy_threshold: MIN_ENTROPY_THRESHOLD,
        }
    }

    /// Set whether to skip test files.
    #[must_use]
    pub fn skip_test_files(mut self, skip: bool) -> Self {
        self.skip_test_files = skip;
        self
    }

    /// Set whether to include high-entropy detection.
    #[must_use]
    pub fn include_entropy(mut self, include: bool) -> Self {
        self.include_entropy = include;
        self
    }

    /// Set the entropy threshold for high-entropy detection.
    #[must_use]
    pub fn entropy_threshold(mut self, threshold: f64) -> Self {
        self.entropy_threshold = threshold;
        self
    }

    /// Check if a file is a test file.
    fn is_test_file(path: &Path) -> bool {
        let path_str = path.to_string_lossy().to_lowercase();

        // Check directory names
        if path_str.contains("/test/")
            || path_str.contains("/tests/")
            || path_str.contains("/__tests__/")
            || path_str.contains("/spec/")
            || path_str.contains("/specs/")
            || path_str.contains("/_test/")
            || path_str.contains("/test_")
            || path_str.contains("/testdata/")
            || path_str.contains("/fixtures/")
            || path_str.contains("/mocks/")
        {
            return true;
        }

        // Check file names
        if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
            let name_lower = name.to_lowercase();
            if name_lower.starts_with("test_")
                || name_lower.ends_with("_test.py")
                || name_lower.ends_with("_test.go")
                || name_lower.ends_with("_test.rs")
                || name_lower.ends_with("_test.ts")
                || name_lower.ends_with("_test.js")
                || name_lower.ends_with(".test.ts")
                || name_lower.ends_with(".test.js")
                || name_lower.ends_with(".test.tsx")
                || name_lower.ends_with(".test.jsx")
                || name_lower.ends_with(".spec.ts")
                || name_lower.ends_with(".spec.js")
                || name_lower.ends_with("_spec.rb")
                || name_lower.ends_with("test.java")
            {
                return true;
            }
        }

        false
    }

    /// Check if a value is a placeholder (not a real secret).
    fn is_placeholder(value: &str) -> bool {
        // Empty or very short values
        if value.len() < 4 {
            return true;
        }

        // Check for repeating characters (e.g., "xxxxxxxx", "00000000")
        // This replaces the backreference pattern ^(.)\1{7,}$ which Rust regex doesn't support
        // Uses SIMD for efficient 32-byte-at-a-time comparison with early exit
        if value.len() >= 8 && is_all_same_byte(value.as_bytes()) {
            return true;
        }

        // Check against placeholder patterns
        for pattern in PLACEHOLDER_PATTERNS.iter() {
            if pattern.is_match(value) {
                return true;
            }
        }

        false
    }

    /// Check if a line is reading from environment or config.
    fn is_env_or_config_read(line: &str) -> bool {
        for pattern in ENV_VAR_PATTERNS.iter() {
            if pattern.is_match(line) {
                return true;
            }
        }

        for pattern in CONFIG_READ_PATTERNS.iter() {
            if pattern.is_match(line) {
                return true;
            }
        }

        false
    }

    /// Mask a secret value, showing only first and last few characters.
    fn mask_value(value: &str) -> String {
        let len = value.len();
        if len <= 8 {
            return "*".repeat(len);
        }

        let visible = std::cmp::min(4, len / 4);
        let masked_len = len - (visible * 2);

        format!(
            "{}{}{}",
            &value[..visible],
            "*".repeat(masked_len),
            &value[len - visible..]
        )
    }

    /// Generate remediation advice for a secret type.
    fn get_remediation(secret_type: SecretType) -> String {
        match secret_type {
            SecretType::AwsAccessKey | SecretType::AwsSecretKey => {
                "1. Immediately rotate the AWS credentials in IAM console\n\
                 2. Use environment variables or AWS Secrets Manager\n\
                 3. Consider using IAM roles for EC2/Lambda/ECS instead of keys"
                    .to_string()
            }
            SecretType::GitHubToken | SecretType::GitLabToken => {
                "1. Revoke the token immediately in repository settings\n\
                 2. Generate a new token with minimal required permissions\n\
                 3. Use GITHUB_TOKEN in Actions or environment variables"
                    .to_string()
            }
            SecretType::PrivateKey | SecretType::SshPrivateKey | SecretType::PgpPrivateKey => {
                "1. Remove the private key from source control\n\
                 2. Generate new key pair and distribute new public key\n\
                 3. Store private keys in secure key management systems\n\
                 4. Use ssh-agent or similar for authentication"
                    .to_string()
            }
            SecretType::ConnectionString => "1. Remove credentials from connection string\n\
                 2. Use environment variables for database credentials\n\
                 3. Consider using managed identity or IAM authentication\n\
                 4. Use connection pooling with credential injection"
                .to_string(),
            SecretType::Jwt => "1. Determine if JWT is a hardcoded test token\n\
                 2. If production: rotate signing keys and invalidate tokens\n\
                 3. Generate JWTs dynamically, never hardcode"
                .to_string(),
            SecretType::Password | SecretType::ApiKey | SecretType::GenericSecret => {
                "1. Remove hardcoded credential from source code\n\
                 2. Store in environment variables or secrets manager\n\
                 3. Rotate the credential if it was exposed in VCS history\n\
                 4. Consider using a .env file (not committed to VCS)"
                    .to_string()
            }
            SecretType::HighEntropyString => "1. Review if this is actually a secret\n\
                 2. If secret: move to environment variable or secrets manager\n\
                 3. If not a secret: consider adding to ignore list"
                .to_string(),
            _ => "1. Remove hardcoded credential from source code\n\
                 2. Store securely using environment variables or secrets manager\n\
                 3. Rotate the credential if exposed in VCS history"
                .to_string(),
        }
    }

    /// Scan a single file for secrets.
    pub fn scan_file(&self, file_path: &str) -> Result<Vec<SecretFinding>> {
        let path = Path::new(file_path);
        let is_test = Self::is_test_file(path);

        // Skip test files if configured
        if self.skip_test_files && is_test {
            return Ok(vec![]);
        }

        let source = std::fs::read_to_string(path).map_err(|e| BrrrError::io_with_path(e, path))?;

        let mut findings = Vec::new();

        for (line_num, line) in source.lines().enumerate() {
            let line_number = line_num + 1;

            // Skip lines that are reading from environment or config
            if Self::is_env_or_config_read(line) {
                continue;
            }

            // Check provider-specific patterns
            for pattern in PROVIDER_PATTERNS.iter() {
                if let Some(captures) = pattern.regex.captures(line) {
                    let matched = captures.get(1).or_else(|| captures.get(0));
                    if let Some(m) = matched {
                        let value = m.as_str();

                        // Skip placeholders
                        if Self::is_placeholder(value) {
                            continue;
                        }

                        // Skip very short matches for low-confidence patterns
                        if pattern.confidence == Confidence::Low && value.len() < 20 {
                            continue;
                        }

                        // Adjust severity for test files
                        let severity = if is_test {
                            match pattern.severity {
                                Severity::Critical => Severity::Medium,
                                Severity::High => Severity::Low,
                                _ => Severity::Info,
                            }
                        } else {
                            pattern.severity
                        };

                        let column = m.start() + 1;
                        let end_column = m.end() + 1;

                        findings.push(SecretFinding {
                            location: Location {
                                file: file_path.to_string(),
                                line: line_number,
                                column,
                                end_line: line_number,
                                end_column,
                            },
                            secret_type: pattern.secret_type,
                            severity,
                            confidence: pattern.confidence,
                            masked_value: Self::mask_value(value),
                            variable_name: None,
                            description: pattern.description.to_string(),
                            remediation: Self::get_remediation(pattern.secret_type),
                            is_test_file: is_test,
                            entropy: Some(calculate_entropy(value)),
                        });
                    }
                }
            }

            // Check generic assignment patterns
            for pattern in GENERIC_PATTERNS.iter() {
                if let Some(captures) = pattern.var_regex.captures(line) {
                    if let Some(value_match) = captures.get(1) {
                        let value = value_match.as_str();

                        // Skip placeholders
                        if Self::is_placeholder(value) {
                            continue;
                        }

                        // Skip short values
                        if value.len() < pattern.min_value_length {
                            continue;
                        }

                        // Calculate entropy
                        let entropy = calculate_entropy(value);

                        // Skip low-entropy values for generic patterns
                        if entropy < 3.0 {
                            continue;
                        }

                        // Determine confidence based on entropy
                        let confidence = if entropy > 4.5 {
                            Confidence::High
                        } else if entropy > 3.5 {
                            Confidence::Medium
                        } else {
                            Confidence::Low
                        };

                        // Determine severity
                        let base_severity = if entropy > 4.5 {
                            Severity::High
                        } else if entropy > 3.5 {
                            Severity::Medium
                        } else {
                            Severity::Low
                        };

                        let severity = if is_test {
                            match base_severity {
                                Severity::High => Severity::Low,
                                Severity::Medium => Severity::Info,
                                _ => Severity::Info,
                            }
                        } else {
                            base_severity
                        };

                        let column = value_match.start() + 1;
                        let end_column = value_match.end() + 1;

                        findings.push(SecretFinding {
                            location: Location {
                                file: file_path.to_string(),
                                line: line_number,
                                column,
                                end_line: line_number,
                                end_column,
                            },
                            secret_type: pattern.secret_type,
                            severity,
                            confidence,
                            masked_value: Self::mask_value(value),
                            variable_name: None,
                            description: pattern.description.to_string(),
                            remediation: Self::get_remediation(pattern.secret_type),
                            is_test_file: is_test,
                            entropy: Some(entropy),
                        });
                    }
                }
            }

            // High-entropy detection (if enabled)
            if self.include_entropy {
                self.detect_high_entropy_strings(
                    line,
                    line_number,
                    file_path,
                    is_test,
                    &mut findings,
                );
            }
        }

        Ok(findings)
    }

    /// Detect high-entropy strings that might be secrets.
    fn detect_high_entropy_strings(
        &self,
        line: &str,
        line_number: usize,
        file_path: &str,
        is_test: bool,
        findings: &mut Vec<SecretFinding>,
    ) {
        // Pattern to find quoted strings
        static STRING_PATTERN: Lazy<Regex> =
            Lazy::new(|| Regex::new(r#"["']([^"']{16,})["']"#).expect("Invalid regex"));

        // Skip comments (simple heuristic)
        let trimmed = line.trim();
        if trimmed.starts_with('#')
            || trimmed.starts_with("//")
            || trimmed.starts_with('*')
            || trimmed.starts_with("/*")
        {
            return;
        }

        for captures in STRING_PATTERN.captures_iter(line) {
            if let Some(value_match) = captures.get(1) {
                let value = value_match.as_str();

                // Skip if too short
                if value.len() < MIN_ENTROPY_STRING_LENGTH {
                    continue;
                }

                // Skip placeholders
                if Self::is_placeholder(value) {
                    continue;
                }

                // Skip URLs, paths, and common patterns
                if value.contains("http://")
                    || value.contains("https://")
                    || value.contains("file://")
                    || value.starts_with('/')
                    || value.contains("\\\\")
                    || value.contains(".com")
                    || value.contains(".org")
                    || value.contains(".io")
                {
                    continue;
                }

                // Skip if mostly spaces or newlines (SIMD-accelerated)
                let non_space: usize = count_non_whitespace_simd(value);
                if (non_space as f64) / (value.len() as f64) < 0.8 {
                    continue;
                }

                let entropy = calculate_entropy(value);

                if entropy >= self.entropy_threshold {
                    // Check if already matched by a provider pattern
                    let already_matched = findings.iter().any(|f| {
                        f.location.line == line_number
                            && f.location.column <= value_match.start() + 1
                            && f.location.end_column >= value_match.end() + 1
                    });

                    if already_matched {
                        continue;
                    }

                    let severity = if is_test {
                        Severity::Info
                    } else if entropy > 5.0 {
                        Severity::Medium
                    } else {
                        Severity::Low
                    };

                    let column = value_match.start() + 1;
                    let end_column = value_match.end() + 1;

                    findings.push(SecretFinding {
                        location: Location {
                            file: file_path.to_string(),
                            line: line_number,
                            column,
                            end_line: line_number,
                            end_column,
                        },
                        secret_type: SecretType::HighEntropyString,
                        severity,
                        confidence: Confidence::Low,
                        masked_value: Self::mask_value(value),
                        variable_name: None,
                        description: format!(
                            "High-entropy string detected (entropy: {:.2} bits/char)",
                            entropy
                        ),
                        remediation: Self::get_remediation(SecretType::HighEntropyString),
                        is_test_file: is_test,
                        entropy: Some(entropy),
                    });
                }
            }
        }
    }

    /// Scan a directory for secrets.
    pub fn scan_directory(&self, dir_path: &str, language: Option<&str>) -> Result<ScanResult> {
        let path = Path::new(dir_path);
        if !path.is_dir() {
            return Err(BrrrError::InvalidArgument(format!(
                "Not a directory: {}",
                dir_path
            )));
        }

        let mut findings = Vec::new();
        let mut files_scanned = 0;

        // Walk directory respecting .gitignore and .brrrignore
        let mut builder = ignore::WalkBuilder::new(path);
        builder.add_custom_ignore_filename(".brrrignore");
        builder.hidden(true);

        // Define extensions to scan based on language
        let extensions: HashSet<&str> = match language {
            Some("python") => ["py"].iter().copied().collect(),
            Some("typescript") | Some("javascript") => ["ts", "tsx", "js", "jsx", "mjs", "cjs"]
                .iter()
                .copied()
                .collect(),
            Some("go") => ["go"].iter().copied().collect(),
            Some("rust") => ["rs"].iter().copied().collect(),
            Some("java") => ["java"].iter().copied().collect(),
            Some("c") => ["c", "h"].iter().copied().collect(),
            Some("cpp") => ["cpp", "cc", "cxx", "hpp", "h"].iter().copied().collect(),
            Some("ruby") => ["rb", "erb"].iter().copied().collect(),
            Some("php") => ["php"].iter().copied().collect(),
            Some("csharp") => ["cs"].iter().copied().collect(),
            _ => [
                "py",
                "ts",
                "tsx",
                "js",
                "jsx",
                "mjs",
                "cjs",
                "go",
                "rs",
                "java",
                "c",
                "h",
                "cpp",
                "cc",
                "cxx",
                "hpp",
                "rb",
                "erb",
                "php",
                "cs",
                "yaml",
                "yml",
                "json",
                "toml",
                "xml",
                "properties",
                "ini",
                "cfg",
                "conf",
                "env",
                "sh",
                "bash",
                "zsh",
                "ps1",
                "bat",
                "cmd",
            ]
            .iter()
            .copied()
            .collect(),
        };

        for entry in builder.build().flatten() {
            let entry_path = entry.path();
            if !entry_path.is_file() {
                continue;
            }

            let ext = entry_path
                .extension()
                .and_then(|e| e.to_str())
                .unwrap_or("");

            // Special handling for dotenv files
            let file_name = entry_path
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or("");

            let should_scan = extensions.contains(ext)
                || file_name.starts_with(".env")
                || file_name.ends_with(".env")
                || file_name == "Dockerfile"
                || file_name == "docker-compose.yml"
                || file_name == "docker-compose.yaml";

            if !should_scan {
                continue;
            }

            files_scanned += 1;

            if let Ok(file_findings) = self.scan_file(entry_path.to_str().unwrap_or("")) {
                findings.extend(file_findings);
            }
        }

        // Count by type and severity
        let mut type_counts: HashMap<String, usize> = HashMap::new();
        let mut severity_counts: HashMap<String, usize> = HashMap::new();

        for finding in &findings {
            *type_counts
                .entry(finding.secret_type.to_string())
                .or_insert(0) += 1;
            *severity_counts
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
        }

        Ok(ScanResult {
            findings,
            files_scanned,
            type_counts,
            severity_counts,
        })
    }
}

// =============================================================================
// Public API Functions
// =============================================================================

/// Scan a file or directory for hardcoded secrets.
///
/// # Arguments
///
/// * `path` - Path to file or directory to scan
/// * `language` - Optional language filter (python, typescript, etc.)
///
/// # Returns
///
/// Scan result with all findings
pub fn scan_secrets(path: &str, language: Option<&str>) -> Result<ScanResult> {
    let detector = SecretsDetector::new();
    let path_obj = Path::new(path);

    if path_obj.is_file() {
        let findings = detector.scan_file(path)?;

        let mut type_counts: HashMap<String, usize> = HashMap::new();
        let mut severity_counts: HashMap<String, usize> = HashMap::new();

        for finding in &findings {
            *type_counts
                .entry(finding.secret_type.to_string())
                .or_insert(0) += 1;
            *severity_counts
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
        }

        Ok(ScanResult {
            findings,
            files_scanned: 1,
            type_counts,
            severity_counts,
        })
    } else {
        detector.scan_directory(path, language)
    }
}

/// Scan a single file for hardcoded secrets.
pub fn scan_file_secrets(path: &Path, _language: Option<&str>) -> Result<Vec<SecretFinding>> {
    let detector = SecretsDetector::new();
    detector.scan_file(path.to_str().unwrap_or(""))
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn create_temp_file(content: &str, extension: &str) -> tempfile::NamedTempFile {
        let mut file = tempfile::Builder::new()
            .suffix(extension)
            .tempfile()
            .expect("Failed to create temp file");
        file.write_all(content.as_bytes())
            .expect("Failed to write temp file");
        file
    }

    // =========================================================================
    // AWS Tests
    // =========================================================================

    #[test]
    fn test_detect_aws_access_key() {
        let source = r#"
AWS_ACCESS_KEY_ID = "AKIAIOSFODNN7EXAMPLE"
aws_secret_key = "wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY"
        "#;
        let file = create_temp_file(source, ".py");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect AWS credentials");

        let aws_key = findings
            .iter()
            .find(|f| f.secret_type == SecretType::AwsAccessKey);
        assert!(aws_key.is_some(), "Should detect AWS Access Key");
    }

    // =========================================================================
    // GitHub Token Tests
    // =========================================================================

    #[test]
    fn test_detect_github_token_classic() {
        let source = r#"
GITHUB_TOKEN = "ghp_1234567890abcdefghijklmnopqrstuvwxyz"
        "#;
        let file = create_temp_file(source, ".py");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect GitHub token");
        assert_eq!(findings[0].secret_type, SecretType::GitHubToken);
        assert_eq!(findings[0].confidence, Confidence::High);
    }

    #[test]
    fn test_detect_github_fine_grained_token() {
        // Fine-grained PAT format: github_pat_[base62]{22}_[base62]{59}
        // 22 chars + 59 chars
        let source = r#"
token = "github_pat_11ABCD1234567890abcdef_1234567890abcdefghijklmnopqrstuvwxyz1234567890abcdefghijklm"
        "#;
        let file = create_temp_file(source, ".py");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let gh_token = findings
            .iter()
            .find(|f| f.secret_type == SecretType::GitHubToken);
        assert!(
            gh_token.is_some(),
            "Should detect fine-grained GitHub token"
        );
    }

    // =========================================================================
    // Slack Token Tests
    // =========================================================================

    #[test]
    fn test_detect_slack_token() {
        let source = r#"
SLACK_TOKEN = "xoxb-FAKE-TEST-TOKEN-FOR-UNIT-TESTS-ONLY-abcd"
        "#;
        let file = create_temp_file(source, ".ts");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect Slack token");
        assert_eq!(findings[0].secret_type, SecretType::SlackToken);
    }

    // =========================================================================
    // Stripe Key Tests
    // =========================================================================

    #[test]
    fn test_detect_stripe_live_key() {
        // Stripe live key format: sk_live_[alphanumeric 24+ chars]
        // Must use sk_live_ prefix for Critical severity
        // Note: Using string concat to avoid GitHub push protection false positive
        let fake_key = format!("sk_live_{}", "ABCDEF1234567890abcdefgh");
        let source = format!(r#"
stripe.api_key = "{}"
        "#, fake_key);
        let file = create_temp_file(&source, ".py");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let stripe_key = findings
            .iter()
            .find(|f| f.secret_type == SecretType::StripeKey);
        assert!(stripe_key.is_some(), "Should detect Stripe live key");
        assert_eq!(stripe_key.unwrap().severity, Severity::Critical);
    }

    #[test]
    fn test_detect_stripe_test_key_lower_severity() {
        let source = r#"
stripe.api_key = "sk_test_1234567890abcdefghijklmnop"
        "#;
        let file = create_temp_file(source, ".py");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let stripe_key = findings
            .iter()
            .find(|f| f.secret_type == SecretType::StripeKey);
        assert!(stripe_key.is_some(), "Should detect Stripe test key");
        assert_eq!(stripe_key.unwrap().severity, Severity::Medium);
    }

    // =========================================================================
    // Google API Key Tests
    // =========================================================================

    #[test]
    fn test_detect_google_api_key() {
        let source = r#"
const apiKey = "AIzaSyDaGmWKa4JsXZ-HjGw7ISLn_3namBGewQe"
        "#;
        let file = create_temp_file(source, ".ts");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let google_key = findings
            .iter()
            .find(|f| f.secret_type == SecretType::GoogleApiKey);
        assert!(google_key.is_some(), "Should detect Google API key");
    }

    // =========================================================================
    // Private Key Tests
    // =========================================================================

    #[test]
    fn test_detect_rsa_private_key() {
        let source = r#"
-----BEGIN RSA PRIVATE KEY-----
MIIEpQIBAAKCAQEA2Z3qX2BTLS4e...
-----END RSA PRIVATE KEY-----
        "#;
        let file = create_temp_file(source, ".pem");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let priv_key = findings
            .iter()
            .find(|f| f.secret_type == SecretType::PrivateKey);
        assert!(priv_key.is_some(), "Should detect RSA private key");
        assert_eq!(priv_key.unwrap().severity, Severity::Critical);
    }

    #[test]
    fn test_detect_openssh_private_key() {
        let source = r#"
-----BEGIN OPENSSH PRIVATE KEY-----
b3BlbnNzaC1rZXktdjEAAAAABG5vbmUAAAA...
-----END OPENSSH PRIVATE KEY-----
        "#;
        let file = create_temp_file(source, ".key");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let ssh_key = findings
            .iter()
            .find(|f| f.secret_type == SecretType::SshPrivateKey);
        assert!(ssh_key.is_some(), "Should detect OpenSSH private key");
    }

    // =========================================================================
    // JWT Tests
    // =========================================================================

    #[test]
    fn test_detect_jwt() {
        let source = r#"
const token = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiIxMjM0NTY3ODkwIiwibmFtZSI6IkpvaG4gRG9lIiwiaWF0IjoxNTE2MjM5MDIyfQ.SflKxwRJSMeKKF2QT4fwpMeJf36POk6yJV_adQssw5c"
        "#;
        let file = create_temp_file(source, ".js");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let jwt = findings.iter().find(|f| f.secret_type == SecretType::Jwt);
        assert!(jwt.is_some(), "Should detect JWT");
    }

    // =========================================================================
    // Connection String Tests
    // =========================================================================

    #[test]
    fn test_detect_postgres_connection_string() {
        let source = r#"
DATABASE_URL = "postgres://user:password123@localhost:5432/mydb"
        "#;
        let file = create_temp_file(source, ".env");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let conn_str = findings
            .iter()
            .find(|f| f.secret_type == SecretType::ConnectionString);
        assert!(
            conn_str.is_some(),
            "Should detect Postgres connection string"
        );
        assert_eq!(conn_str.unwrap().severity, Severity::Critical);
    }

    #[test]
    fn test_detect_mongodb_connection_string() {
        let source = r#"
MONGO_URI = "mongodb+srv://admin:secretpass@cluster0.abc123.mongodb.net/mydb"
        "#;
        let file = create_temp_file(source, ".env");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let conn_str = findings
            .iter()
            .find(|f| f.secret_type == SecretType::ConnectionString);
        assert!(
            conn_str.is_some(),
            "Should detect MongoDB connection string"
        );
    }

    // =========================================================================
    // Generic Pattern Tests
    // =========================================================================

    #[test]
    fn test_detect_hardcoded_password() {
        let source = r#"
password = "MyS3cr3tP@ssw0rd!"
        "#;
        let file = create_temp_file(source, ".py");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let password = findings
            .iter()
            .find(|f| f.secret_type == SecretType::Password);
        assert!(password.is_some(), "Should detect hardcoded password");
    }

    #[test]
    fn test_detect_hardcoded_api_key() {
        let source = r#"
api_key = "abc123xyz789secretkey456"
        "#;
        let file = create_temp_file(source, ".py");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let api_key = findings
            .iter()
            .find(|f| f.secret_type == SecretType::ApiKey);
        assert!(api_key.is_some(), "Should detect hardcoded API key");
    }

    // =========================================================================
    // False Positive Tests
    // =========================================================================

    #[test]
    fn test_ignore_environment_variable_read_python() {
        let source = r#"
API_KEY = os.environ["API_KEY"]
SECRET = os.getenv("SECRET_KEY")
TOKEN = os.environ.get("AUTH_TOKEN")
        "#;
        let file = create_temp_file(source, ".py");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(
            findings.is_empty(),
            "Should NOT flag environment variable reads"
        );
    }

    #[test]
    fn test_ignore_environment_variable_read_typescript() {
        let source = r#"
const apiKey = process.env.API_KEY;
const secret = process.env["SECRET_KEY"];
        "#;
        let file = create_temp_file(source, ".ts");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(findings.is_empty(), "Should NOT flag process.env reads");
    }

    #[test]
    fn test_ignore_placeholder_values() {
        let source = r#"
API_KEY = "YOUR_API_KEY_HERE"
password = "changeme"
secret = "xxxxxxxxxxxxxxxx"
token = "<your-token>"
key = "placeholder"
        "#;
        let file = create_temp_file(source, ".py");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(findings.is_empty(), "Should NOT flag placeholder values");
    }

    #[test]
    fn test_ignore_config_reads() {
        let source = r#"
password = config.get("password")
api_key = settings["api_key"]
        "#;
        let file = create_temp_file(source, ".py");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(findings.is_empty(), "Should NOT flag config reads");
    }

    #[test]
    fn test_reduced_severity_in_test_files() {
        let source = r#"
GITHUB_TOKEN = "ghp_1234567890abcdefghijklmnopqrstuvwxyz"
        "#;
        let mut file = tempfile::Builder::new()
            .suffix("_test.py")
            .tempfile()
            .expect("Failed to create temp file");
        file.write_all(source.as_bytes())
            .expect("Failed to write temp file");

        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect token in test file");
        assert!(findings[0].is_test_file, "Should mark as test file");
        // Severity should be reduced
        assert!(
            findings[0].severity < Severity::High,
            "Severity should be reduced for test files"
        );
    }

    // =========================================================================
    // Entropy Tests
    // =========================================================================

    #[test]
    fn test_entropy_calculation() {
        // Low entropy (repeating characters)
        let low_entropy = calculate_entropy("aaaaaaaaaaaaaaaaaaaa");
        assert!(low_entropy < 1.0, "Repeating chars should have low entropy");

        // Medium entropy (simple text)
        let medium_entropy = calculate_entropy("hello world test");
        assert!(
            medium_entropy > 2.0 && medium_entropy < 4.0,
            "Simple text should have medium entropy"
        );

        // High entropy (random-looking)
        let high_entropy = calculate_entropy("aB3$kL9#mN2@pQ5&rT8");
        assert!(
            high_entropy > 4.0,
            "Random-looking string should have high entropy"
        );
    }

    #[test]
    fn test_detect_high_entropy_string() {
        let source = r#"
const key = "aB3kL9mN2pQ5rT8xY1cD4eF7gH0iJ"
        "#;
        let file = create_temp_file(source, ".js");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let high_entropy = findings
            .iter()
            .find(|f| f.secret_type == SecretType::HighEntropyString);
        assert!(
            high_entropy.is_some(),
            "Should detect high-entropy string as potential secret"
        );
    }

    // =========================================================================
    // Masking Tests
    // =========================================================================

    #[test]
    fn test_mask_value() {
        assert_eq!(SecretsDetector::mask_value("short"), "*****");
        assert_eq!(SecretsDetector::mask_value("12345678"), "********");
        assert_eq!(
            SecretsDetector::mask_value("1234567890123456"),
            "1234********3456"
        );
        assert_eq!(
            SecretsDetector::mask_value("ghp_1234567890abcdefghijklmnopqrstuvwxyz"),
            "ghp_********************************wxyz"
        );
    }

    // =========================================================================
    // OpenAI / Anthropic Tests
    // =========================================================================

    #[test]
    fn test_detect_openai_key() {
        let source = r#"
OPENAI_API_KEY = "sk-proj-abcdefghijklmnopqrstuvwxyz1234567890ABCD"
        "#;
        let file = create_temp_file(source, ".env");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let openai_key = findings
            .iter()
            .find(|f| f.secret_type == SecretType::OpenAiKey);
        assert!(openai_key.is_some(), "Should detect OpenAI API key");
    }

    // =========================================================================
    // SendGrid Tests
    // =========================================================================

    #[test]
    fn test_detect_sendgrid_key() {
        // SendGrid format: SG.[exactly 22 alphanumeric chars].[exactly 43 alphanumeric chars]
        // Regex: SG\.[a-zA-Z0-9_-]{22}\.[a-zA-Z0-9_-]{43}
        // Note: Using string concat to avoid GitHub push protection false positive
        let fake_key = format!("SG.{}.{}", "aBcDeFgHiJkLmNoPqRsTuV", "aBcDeFgHiJkLmNoPqRsTuVwXyZ0123456789ABCDEFG");
        let source = format!(r#"
SENDGRID_API_KEY = "{}"
        "#, fake_key);
        let file = create_temp_file(&source, ".env");
        let detector = SecretsDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let sg_key = findings
            .iter()
            .find(|f| f.secret_type == SecretType::SendGridKey);
        assert!(sg_key.is_some(), "Should detect SendGrid API key");
    }

    // =========================================================================
    // Severity / Display Tests
    // =========================================================================

    #[test]
    fn test_severity_display() {
        assert_eq!(Severity::Critical.to_string(), "CRITICAL");
        assert_eq!(Severity::High.to_string(), "HIGH");
        assert_eq!(Severity::Medium.to_string(), "MEDIUM");
        assert_eq!(Severity::Low.to_string(), "LOW");
        assert_eq!(Severity::Info.to_string(), "INFO");
    }

    #[test]
    fn test_confidence_display() {
        assert_eq!(Confidence::High.to_string(), "HIGH");
        assert_eq!(Confidence::Medium.to_string(), "MEDIUM");
        assert_eq!(Confidence::Low.to_string(), "LOW");
    }

    #[test]
    fn test_secret_type_display() {
        assert_eq!(SecretType::AwsAccessKey.to_string(), "AWS Access Key");
        assert_eq!(SecretType::GitHubToken.to_string(), "GitHub Token");
        assert_eq!(SecretType::PrivateKey.to_string(), "Private Key");
        assert_eq!(
            SecretType::ConnectionString.to_string(),
            "Connection String"
        );
    }

    // =========================================================================
    // Scan Result Tests
    // =========================================================================

    #[test]
    fn test_scan_result_counts() {
        let result = ScanResult {
            findings: vec![],
            files_scanned: 10,
            type_counts: [("AWS Access Key".to_string(), 2)].into_iter().collect(),
            severity_counts: [("CRITICAL".to_string(), 2), ("HIGH".to_string(), 3)]
                .into_iter()
                .collect(),
        };

        assert_eq!(result.files_scanned, 10);
        assert_eq!(result.type_counts.get("AWS Access Key"), Some(&2));
        assert_eq!(result.severity_counts.get("CRITICAL"), Some(&2));
    }

    // =========================================================================
    // SIMD Utility Tests
    // =========================================================================

    #[test]
    fn test_count_non_whitespace_simd() {
        // Empty string
        assert_eq!(count_non_whitespace_simd(""), 0);

        // All non-whitespace
        assert_eq!(count_non_whitespace_simd("hello"), 5);
        assert_eq!(count_non_whitespace_simd("abc123!@#"), 9);

        // All whitespace
        assert_eq!(count_non_whitespace_simd("    "), 0);
        assert_eq!(count_non_whitespace_simd("\t\t\t"), 0);
        assert_eq!(count_non_whitespace_simd("\n\n\n"), 0);
        assert_eq!(count_non_whitespace_simd("\r\n\r\n"), 0);
        assert_eq!(count_non_whitespace_simd(" \t\n\r"), 0);

        // Mixed
        assert_eq!(count_non_whitespace_simd("hello world"), 10);
        assert_eq!(count_non_whitespace_simd("  hello  "), 5);
        assert_eq!(count_non_whitespace_simd("\thello\n"), 5);
        assert_eq!(count_non_whitespace_simd("a b c d e"), 5);

        // Exactly 32 bytes (one SIMD iteration)
        let s32 = "abcdefghijklmnopqrstuvwxyz123456";
        assert_eq!(s32.len(), 32);
        assert_eq!(count_non_whitespace_simd(s32), 32);

        // 33 bytes with whitespace (6 spaces, 27 non-whitespace)
        let s33_ws = "abcd efgh ijkl mnop qrst uvwx yz1";
        assert_eq!(s33_ws.len(), 33);
        assert_eq!(count_non_whitespace_simd(s33_ws), 27);

        // Larger than 32 bytes (multiple SIMD iterations)
        let long = "a".repeat(100);
        assert_eq!(count_non_whitespace_simd(&long), 100);

        let long_ws = "a ".repeat(50); // 100 bytes, 50 'a' and 50 spaces
        assert_eq!(count_non_whitespace_simd(&long_ws), 50);

        // Edge case: 31 bytes (scalar path)
        let s31 = "abcdefghijklmnopqrstuvwxyz12345";
        assert_eq!(s31.len(), 31);
        assert_eq!(count_non_whitespace_simd(s31), 31);

        // Edge case: 33 bytes (SIMD + 1 scalar)
        let s33 = "abcdefghijklmnopqrstuvwxyz1234567";
        assert_eq!(s33.len(), 33);
        assert_eq!(count_non_whitespace_simd(s33), 33);

        // High-entropy secret-like string with no whitespace
        let secret = "wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY";
        assert_eq!(count_non_whitespace_simd(secret), secret.len());
    }
}
