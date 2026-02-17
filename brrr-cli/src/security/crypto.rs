//! Weak cryptography detection for source code.
//!
//! Detects insecure cryptographic patterns including:
//! - Weak hash functions (MD5, SHA1) used for security purposes
//! - Weak ciphers (DES, 3DES, RC4, Blowfish)
//! - Insecure cipher modes (ECB)
//! - Insufficient key sizes (RSA < 2048 bits)
//! - Hardcoded encryption keys and IVs
//! - Predictable random number generation for crypto
//!
//! # Context-Aware Analysis
//!
//! The detector distinguishes between safe and unsafe uses:
//! - **SAFE**: MD5/SHA1 for file checksums, cache keys, git operations
//! - **UNSAFE**: MD5/SHA1 for passwords, signatures, authentication tokens
//!
//! # Language Support
//!
//! Detects patterns in:
//! - Python: hashlib, Crypto, cryptography, PyCryptodome
//! - TypeScript/JavaScript: crypto, crypto-js, node:crypto
//! - Rust: md5, sha1, des crates, ring, rust-crypto
//! - Go: crypto/md5, crypto/des, crypto/rc4
//! - Java: MessageDigest, Cipher
//! - C/C++: OpenSSL, EVP, MD5(), DES_*
//!
//! # Example
//!
//! ```ignore
//! use brrr::security::crypto::{WeakCryptoDetector, scan_weak_crypto};
//!
//! let result = scan_weak_crypto("./src", None)?;
//! for finding in result.findings {
//!     println!("[{}] {} at {}:{}",
//!         finding.severity,
//!         finding.issue_type,
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

/// Type of weak cryptography issue detected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum WeakCryptoIssue {
    /// Weak hash algorithm (MD5, SHA1 for security purposes)
    WeakHash,
    /// Weak cipher algorithm (DES, 3DES, RC4, Blowfish)
    WeakCipher,
    /// Insecure cipher mode (ECB)
    InsecureMode,
    /// Insufficient key size (RSA < 2048, AES < 128)
    InsufficientKeySize,
    /// Hardcoded encryption key
    HardcodedKey,
    /// Hardcoded initialization vector (IV should be random)
    HardcodedIv,
    /// Predictable random number generator used for crypto
    PredictableRandom,
    /// Encryption without authentication (no MAC/HMAC)
    MissingAuthentication,
    /// Deprecated cryptographic function
    DeprecatedFunction,
}

impl std::fmt::Display for WeakCryptoIssue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WeakCryptoIssue::WeakHash => write!(f, "Weak Hash Algorithm"),
            WeakCryptoIssue::WeakCipher => write!(f, "Weak Cipher Algorithm"),
            WeakCryptoIssue::InsecureMode => write!(f, "Insecure Cipher Mode"),
            WeakCryptoIssue::InsufficientKeySize => write!(f, "Insufficient Key Size"),
            WeakCryptoIssue::HardcodedKey => write!(f, "Hardcoded Encryption Key"),
            WeakCryptoIssue::HardcodedIv => write!(f, "Hardcoded Initialization Vector"),
            WeakCryptoIssue::PredictableRandom => write!(f, "Predictable Random for Crypto"),
            WeakCryptoIssue::MissingAuthentication => {
                write!(f, "Encryption Without Authentication")
            }
            WeakCryptoIssue::DeprecatedFunction => write!(f, "Deprecated Cryptographic Function"),
        }
    }
}

/// Specific algorithm that was flagged.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Algorithm {
    /// MD5 hash (broken, collision attacks)
    Md5,
    /// SHA-1 hash (deprecated, collision attacks)
    Sha1,
    /// DES cipher (56-bit key, broken)
    Des,
    /// Triple DES (deprecated, slow, 112-bit effective)
    TripleDes,
    /// RC4 stream cipher (biased keystream, broken)
    Rc4,
    /// Blowfish (64-bit block, deprecated)
    Blowfish,
    /// ECB mode (reveals patterns in data)
    EcbMode,
    /// RSA with insufficient key size
    RsaWeakKey,
    /// DSA (deprecated in favor of ECDSA)
    Dsa,
    /// Hardcoded key pattern
    HardcodedKeyPattern,
    /// Hardcoded IV pattern
    HardcodedIvPattern,
    /// Non-cryptographic random
    InsecureRandom,
    /// Other weak algorithm
    Other(String),
}

impl std::fmt::Display for Algorithm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Algorithm::Md5 => write!(f, "MD5"),
            Algorithm::Sha1 => write!(f, "SHA-1"),
            Algorithm::Des => write!(f, "DES"),
            Algorithm::TripleDes => write!(f, "3DES/Triple-DES"),
            Algorithm::Rc4 => write!(f, "RC4"),
            Algorithm::Blowfish => write!(f, "Blowfish"),
            Algorithm::EcbMode => write!(f, "ECB Mode"),
            Algorithm::RsaWeakKey => write!(f, "RSA (weak key)"),
            Algorithm::Dsa => write!(f, "DSA"),
            Algorithm::HardcodedKeyPattern => write!(f, "Hardcoded Key"),
            Algorithm::HardcodedIvPattern => write!(f, "Hardcoded IV"),
            Algorithm::InsecureRandom => write!(f, "Insecure Random"),
            Algorithm::Other(s) => write!(f, "{}", s),
        }
    }
}

/// Severity level for crypto findings.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Severity {
    /// Informational only (legacy code, may be intentional)
    Info,
    /// Low severity (weak but not immediately exploitable)
    Low,
    /// Medium severity (deprecated algorithms, should be replaced)
    Medium,
    /// High severity (actively dangerous, exploitable)
    High,
    /// Critical severity (immediate security risk)
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
    /// Low confidence (pattern match only, needs review)
    Low,
    /// Medium confidence (likely issue but context unclear)
    Medium,
    /// High confidence (clear security issue)
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

/// Context in which the cryptographic function is used.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum UsageContext {
    /// Used for password hashing/storage
    PasswordHashing,
    /// Used for digital signatures
    Signature,
    /// Used for encryption of sensitive data
    Encryption,
    /// Used for file checksums (typically safe for MD5)
    FileChecksum,
    /// Used for cache key generation (typically safe)
    CacheKey,
    /// Used for git operations (typically safe for SHA1)
    GitOperation,
    /// Used for HMAC (typically safe)
    Hmac,
    /// Unknown context
    Unknown,
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

/// A weak cryptography finding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WeakCryptoFinding {
    /// Location in source code
    pub location: Location,
    /// Type of issue detected
    pub issue_type: WeakCryptoIssue,
    /// Specific algorithm flagged
    pub algorithm: Algorithm,
    /// Severity level
    pub severity: Severity,
    /// Confidence level
    pub confidence: Confidence,
    /// Detected usage context
    pub context: UsageContext,
    /// Code snippet showing the vulnerable code
    pub code_snippet: String,
    /// Human-readable description
    pub description: String,
    /// Suggested remediation
    pub remediation: String,
    /// Whether this is in a test file
    pub is_test_file: bool,
    /// Whether this appears to be safe usage (checksum, cache key)
    pub likely_safe: bool,
}

/// Summary of crypto scan results.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScanResult {
    /// All findings
    pub findings: Vec<WeakCryptoFinding>,
    /// Number of files scanned
    pub files_scanned: usize,
    /// Counts by issue type
    pub issue_counts: HashMap<String, usize>,
    /// Counts by severity
    pub severity_counts: HashMap<String, usize>,
    /// Counts by algorithm
    pub algorithm_counts: HashMap<String, usize>,
}

// =============================================================================
// Pattern Definitions
// =============================================================================

/// Cryptographic pattern with metadata.
struct CryptoPattern {
    regex: Regex,
    issue_type: WeakCryptoIssue,
    algorithm: Algorithm,
    base_severity: Severity,
    confidence: Confidence,
    description: &'static str,
    remediation: &'static str,
    /// Patterns that indicate safe context (checksums, cache)
    safe_context_patterns: Vec<&'static str>,
}

/// Context patterns that suggest safe/legitimate usage.
static SAFE_CONTEXT_PATTERNS: Lazy<Vec<Regex>> = Lazy::new(|| {
    vec![
        // Checksum/hash-related variable names and comments
        Regex::new(r"(?i)checksum").expect("Invalid regex"),
        Regex::new(r"(?i)file_?hash").expect("Invalid regex"),
        Regex::new(r"(?i)content_?hash").expect("Invalid regex"),
        Regex::new(r"(?i)etag").expect("Invalid regex"),
        Regex::new(r"(?i)cache_?key").expect("Invalid regex"),
        Regex::new(r"(?i)fingerprint").expect("Invalid regex"),
        Regex::new(r"(?i)dedup").expect("Invalid regex"),
        // Git-related
        Regex::new(r"(?i)git").expect("Invalid regex"),
        Regex::new(r"(?i)commit").expect("Invalid regex"),
        Regex::new(r"(?i)blob").expect("Invalid regex"),
        Regex::new(r"(?i)tree").expect("Invalid regex"),
        // Legacy compatibility comments
        Regex::new(r"(?i)legacy").expect("Invalid regex"),
        Regex::new(r"(?i)backward.?compat").expect("Invalid regex"),
        Regex::new(r"(?i)deprecated.?but.?required").expect("Invalid regex"),
        // Verification/comparison (not security)
        Regex::new(r"(?i)verify_?integrity").expect("Invalid regex"),
        Regex::new(r"(?i)compare_?hash").expect("Invalid regex"),
    ]
});

/// Context patterns that suggest security-sensitive usage.
static SECURITY_CONTEXT_PATTERNS: Lazy<Vec<Regex>> = Lazy::new(|| {
    vec![
        // Password-related
        Regex::new(r"(?i)password").expect("Invalid regex"),
        Regex::new(r"(?i)passwd").expect("Invalid regex"),
        Regex::new(r"(?i)pwd").expect("Invalid regex"),
        Regex::new(r"(?i)credential").expect("Invalid regex"),
        // Authentication-related
        Regex::new(r"(?i)auth").expect("Invalid regex"),
        Regex::new(r"(?i)token").expect("Invalid regex"),
        Regex::new(r"(?i)session").expect("Invalid regex"),
        Regex::new(r"(?i)login").expect("Invalid regex"),
        // Signature-related
        Regex::new(r"(?i)sign(ature)?").expect("Invalid regex"),
        Regex::new(r"(?i)verify").expect("Invalid regex"),
        Regex::new(r"(?i)certificate").expect("Invalid regex"),
        // Encryption-related
        Regex::new(r"(?i)encrypt").expect("Invalid regex"),
        Regex::new(r"(?i)decrypt").expect("Invalid regex"),
        Regex::new(r"(?i)secret").expect("Invalid regex"),
        Regex::new(r"(?i)private").expect("Invalid regex"),
        Regex::new(r"(?i)sensitive").expect("Invalid regex"),
    ]
});

/// Build all crypto patterns for detection.
static CRYPTO_PATTERNS: Lazy<Vec<CryptoPattern>> = Lazy::new(|| {
    vec![
        // =======================================================================
        // Python Patterns
        // =======================================================================

        // MD5 in Python
        CryptoPattern {
            regex: Regex::new(r"(?i)hashlib\s*\.\s*md5\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Md5,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "MD5 hash detected - collision attacks are practical",
            remediation: "Use SHA-256 or SHA-3 for checksums, or bcrypt/argon2 for passwords",
            safe_context_patterns: vec!["checksum", "etag", "cache", "fingerprint"],
        },
        CryptoPattern {
            regex: Regex::new(r#"(?i)hashlib\s*\.\s*new\s*\(\s*["']md5["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Md5,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "MD5 hash via hashlib.new() - collision attacks are practical",
            remediation: "Use SHA-256 or SHA-3 for checksums, or bcrypt/argon2 for passwords",
            safe_context_patterns: vec!["checksum", "etag", "cache"],
        },
        // SHA1 in Python
        CryptoPattern {
            regex: Regex::new(r"(?i)hashlib\s*\.\s*sha1\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Sha1,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "SHA-1 hash detected - collision attacks demonstrated (SHAttered)",
            remediation: "Use SHA-256 or SHA-3 for security purposes",
            safe_context_patterns: vec!["git", "checksum", "legacy"],
        },
        CryptoPattern {
            regex: Regex::new(r#"(?i)hashlib\s*\.\s*new\s*\(\s*["']sha1["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Sha1,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "SHA-1 hash via hashlib.new()",
            remediation: "Use SHA-256 or SHA-3 for security purposes",
            safe_context_patterns: vec!["git", "checksum", "legacy"],
        },
        // DES in Python (PyCryptodome) - direct import
        CryptoPattern {
            regex: Regex::new(r"(?i)(?:Crypto|Cryptodome)\s*\.\s*Cipher\s*\.\s*DES\b").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Des,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "DES cipher detected - 56-bit key is trivially brute-forceable",
            remediation: "Use AES-256 instead",
            safe_context_patterns: vec![],
        },
        // DES in Python (PyCryptodome) - from import style
        CryptoPattern {
            regex: Regex::new(r"(?i)from\s+(?:Crypto|Cryptodome)\s*\.\s*Cipher\s+import\s+DES\b").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Des,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "DES cipher import detected - 56-bit key is trivially brute-forceable",
            remediation: "Use AES-256 instead",
            safe_context_patterns: vec![],
        },
        // 3DES in Python
        CryptoPattern {
            regex: Regex::new(r"(?i)(?:Crypto|Cryptodome)\s*\.\s*Cipher\s*\.\s*(?:DES3|TripleDES)\b").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::TripleDes,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Triple DES detected - deprecated, use AES instead",
            remediation: "Use AES-256 instead",
            safe_context_patterns: vec!["legacy"],
        },
        // Blowfish in Python
        CryptoPattern {
            regex: Regex::new(r"(?i)(?:Crypto|Cryptodome)\s*\.\s*Cipher\s*\.\s*Blowfish\b").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Blowfish,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Blowfish cipher detected - 64-bit block size leads to birthday attacks",
            remediation: "Use AES-256 instead (128-bit block size)",
            safe_context_patterns: vec!["legacy"],
        },
        // RC4 in Python
        CryptoPattern {
            regex: Regex::new(r"(?i)(?:Crypto|Cryptodome)\s*\.\s*Cipher\s*\.\s*(?:ARC4|RC4)\b").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Rc4,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "RC4 stream cipher detected - biased keystream, multiple attacks",
            remediation: "Use AES-GCM or ChaCha20-Poly1305 instead",
            safe_context_patterns: vec![],
        },
        // ECB mode in Python
        CryptoPattern {
            regex: Regex::new(r"(?i)MODE_ECB\b").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::InsecureMode,
            algorithm: Algorithm::EcbMode,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "ECB mode detected - reveals patterns in encrypted data",
            remediation: "Use CBC with random IV, or preferably GCM/CCM for authenticated encryption",
            safe_context_patterns: vec![],
        },
        // Python cryptography library - weak algorithms
        CryptoPattern {
            regex: Regex::new(r"(?i)algorithms\s*\.\s*(?:MD5|SHA1)\b").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Md5,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Weak hash algorithm in cryptography library",
            remediation: "Use SHA256 or SHA512 for security purposes",
            safe_context_patterns: vec!["checksum", "legacy"],
        },
        // Predictable random in Python for crypto
        CryptoPattern {
            regex: Regex::new(r"(?i)random\s*\.\s*(?:random|randint|choice|randrange)\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::PredictableRandom,
            algorithm: Algorithm::InsecureRandom,
            base_severity: Severity::High,
            confidence: Confidence::Medium,
            description: "Non-cryptographic random used (random module) - predictable",
            remediation: "Use secrets module or os.urandom() for cryptographic purposes",
            safe_context_patterns: vec!["test", "mock", "sample", "shuffle"],
        },

        // =======================================================================
        // JavaScript/TypeScript Patterns
        // =======================================================================

        // MD5 in Node.js
        CryptoPattern {
            regex: Regex::new(r#"(?i)crypto\s*\.\s*createHash\s*\(\s*["']md5["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Md5,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "MD5 hash in Node.js crypto - collision attacks are practical",
            remediation: "Use 'sha256' or 'sha512' instead",
            safe_context_patterns: vec!["checksum", "etag", "cache"],
        },
        // SHA1 in Node.js
        CryptoPattern {
            regex: Regex::new(r#"(?i)crypto\s*\.\s*createHash\s*\(\s*["']sha1["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Sha1,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "SHA-1 hash in Node.js crypto - collision attacks demonstrated",
            remediation: "Use 'sha256' or 'sha512' for security purposes",
            safe_context_patterns: vec!["git", "checksum", "legacy"],
        },
        // DES in Node.js
        CryptoPattern {
            regex: Regex::new(r#"(?i)crypto\s*\.\s*createCipher(?:iv)?\s*\(\s*["']des(?:-[a-z]+)?["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Des,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "DES cipher in Node.js - 56-bit key is trivially brute-forceable",
            remediation: "Use 'aes-256-gcm' instead",
            safe_context_patterns: vec![],
        },
        // 3DES in Node.js
        CryptoPattern {
            regex: Regex::new(r#"(?i)crypto\s*\.\s*createCipher(?:iv)?\s*\(\s*["'](?:des-ede3|des3)(?:-[a-z]+)?["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::TripleDes,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Triple DES in Node.js - deprecated, slow",
            remediation: "Use 'aes-256-gcm' instead",
            safe_context_patterns: vec!["legacy"],
        },
        // RC4 in Node.js
        CryptoPattern {
            regex: Regex::new(r#"(?i)crypto\s*\.\s*createCipher(?:iv)?\s*\(\s*["']rc4["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Rc4,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "RC4 stream cipher in Node.js - broken, biased keystream",
            remediation: "Use 'aes-256-gcm' or 'chacha20-poly1305' instead",
            safe_context_patterns: vec![],
        },
        // ECB mode in Node.js
        CryptoPattern {
            regex: Regex::new(r#"(?i)createCipher(?:iv)?\s*\(\s*["'][a-z0-9-]+-ecb["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::InsecureMode,
            algorithm: Algorithm::EcbMode,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "ECB mode in Node.js - reveals patterns in encrypted data",
            remediation: "Use GCM mode for authenticated encryption",
            safe_context_patterns: vec![],
        },
        // Deprecated crypto.createCipher (no IV)
        CryptoPattern {
            regex: Regex::new(r"(?i)crypto\s*\.\s*createCipher\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::DeprecatedFunction,
            algorithm: Algorithm::Other("createCipher".to_string()),
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Deprecated createCipher() - uses weak key derivation",
            remediation: "Use createCipheriv() with a proper key derivation function",
            safe_context_patterns: vec![],
        },
        // crypto-js MD5
        CryptoPattern {
            regex: Regex::new(r"(?i)CryptoJS\s*\.\s*MD5\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Md5,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "MD5 via crypto-js - collision attacks are practical",
            remediation: "Use CryptoJS.SHA256() for checksums",
            safe_context_patterns: vec!["checksum", "etag"],
        },
        // crypto-js SHA1
        CryptoPattern {
            regex: Regex::new(r"(?i)CryptoJS\s*\.\s*SHA1\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Sha1,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "SHA-1 via crypto-js - collision attacks demonstrated",
            remediation: "Use CryptoJS.SHA256() for security purposes",
            safe_context_patterns: vec!["git", "checksum"],
        },
        // crypto-js DES
        CryptoPattern {
            regex: Regex::new(r"(?i)CryptoJS\s*\.\s*DES\s*\.").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Des,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "DES via crypto-js - 56-bit key is trivially brute-forceable",
            remediation: "Use CryptoJS.AES instead",
            safe_context_patterns: vec![],
        },
        // crypto-js 3DES
        CryptoPattern {
            regex: Regex::new(r"(?i)CryptoJS\s*\.\s*TripleDES\s*\.").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::TripleDes,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Triple DES via crypto-js - deprecated",
            remediation: "Use CryptoJS.AES instead",
            safe_context_patterns: vec!["legacy"],
        },
        // crypto-js RC4
        CryptoPattern {
            regex: Regex::new(r"(?i)CryptoJS\s*\.\s*(?:RC4|Rabbit)\s*\.").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Rc4,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "RC4/Rabbit via crypto-js - broken stream cipher",
            remediation: "Use CryptoJS.AES instead",
            safe_context_patterns: vec![],
        },
        // crypto-js ECB mode
        CryptoPattern {
            regex: Regex::new(r"(?i)CryptoJS\s*\.\s*mode\s*\.\s*ECB").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::InsecureMode,
            algorithm: Algorithm::EcbMode,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "ECB mode via crypto-js - reveals patterns in encrypted data",
            remediation: "Use CryptoJS.mode.CBC or CryptoJS.mode.CTR with random IV",
            safe_context_patterns: vec![],
        },
        // Math.random() for crypto
        CryptoPattern {
            regex: Regex::new(r"(?i)Math\s*\.\s*random\s*\(\s*\)").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::PredictableRandom,
            algorithm: Algorithm::InsecureRandom,
            base_severity: Severity::High,
            confidence: Confidence::Low, // Low because Math.random is often used legitimately
            description: "Math.random() is not cryptographically secure",
            remediation: "Use crypto.randomBytes() or crypto.getRandomValues() for crypto",
            safe_context_patterns: vec!["ui", "animation", "shuffle", "sample", "test"],
        },

        // =======================================================================
        // Go Patterns
        // =======================================================================

        // MD5 in Go
        CryptoPattern {
            regex: Regex::new(r"(?i)md5\s*\.\s*(?:New|Sum)\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Md5,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "MD5 hash in Go (crypto/md5) - collision attacks are practical",
            remediation: "Use crypto/sha256 instead",
            safe_context_patterns: vec!["checksum", "etag", "cache"],
        },
        // SHA1 in Go
        CryptoPattern {
            regex: Regex::new(r"(?i)sha1\s*\.\s*(?:New|Sum)\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Sha1,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "SHA-1 hash in Go (crypto/sha1) - collision attacks demonstrated",
            remediation: "Use crypto/sha256 for security purposes",
            safe_context_patterns: vec!["git", "checksum", "legacy"],
        },
        // DES in Go
        CryptoPattern {
            regex: Regex::new(r"(?i)des\s*\.\s*NewCipher\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Des,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "DES cipher in Go (crypto/des) - 56-bit key is trivially brute-forceable",
            remediation: "Use crypto/aes instead",
            safe_context_patterns: vec![],
        },
        // 3DES in Go
        CryptoPattern {
            regex: Regex::new(r"(?i)des\s*\.\s*NewTripleDESCipher\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::TripleDes,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Triple DES in Go - deprecated",
            remediation: "Use crypto/aes instead",
            safe_context_patterns: vec!["legacy"],
        },
        // RC4 in Go
        CryptoPattern {
            regex: Regex::new(r"(?i)rc4\s*\.\s*NewCipher\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Rc4,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "RC4 stream cipher in Go (crypto/rc4) - broken, biased keystream",
            remediation: "Use crypto/aes with GCM mode instead",
            safe_context_patterns: vec![],
        },
        // Go math/rand for crypto
        CryptoPattern {
            regex: Regex::new(r#"(?i)"math/rand""#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::PredictableRandom,
            algorithm: Algorithm::InsecureRandom,
            base_severity: Severity::Medium,
            confidence: Confidence::Low, // Import doesn't mean crypto usage
            description: "math/rand import detected - not cryptographically secure",
            remediation: "Use crypto/rand for cryptographic purposes",
            safe_context_patterns: vec!["test", "mock", "sample"],
        },

        // =======================================================================
        // Rust Patterns
        // =======================================================================

        // MD5 crate in Rust
        CryptoPattern {
            regex: Regex::new(r"(?i)md5\s*::\s*(?:compute|Md5|digest)").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Md5,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "MD5 crate usage in Rust - collision attacks are practical",
            remediation: "Use sha2 crate (Sha256) instead",
            safe_context_patterns: vec!["checksum", "etag", "cache"],
        },
        // SHA1 crate in Rust
        CryptoPattern {
            regex: Regex::new(r"(?i)sha1\s*::\s*(?:Sha1|digest)").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Sha1,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "SHA-1 crate usage in Rust - collision attacks demonstrated",
            remediation: "Use sha2 crate (Sha256) for security purposes",
            safe_context_patterns: vec!["git", "checksum", "legacy"],
        },
        // DES in Rust
        CryptoPattern {
            regex: Regex::new(r"(?i)des\s*::\s*Des\b").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Des,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "DES crate usage in Rust - 56-bit key is trivially brute-forceable",
            remediation: "Use aes crate instead",
            safe_context_patterns: vec![],
        },
        // RC4 in Rust
        CryptoPattern {
            regex: Regex::new(r"(?i)rc4\s*::\s*Rc4").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Rc4,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "RC4 crate usage in Rust - broken, biased keystream",
            remediation: "Use aes-gcm or chacha20poly1305 crate instead",
            safe_context_patterns: vec![],
        },
        // Blowfish in Rust
        CryptoPattern {
            regex: Regex::new(r"(?i)blowfish\s*::\s*Blowfish").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Blowfish,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Blowfish crate usage in Rust - 64-bit block size leads to birthday attacks",
            remediation: "Use aes crate instead (128-bit block size)",
            safe_context_patterns: vec!["legacy"],
        },
        // rand crate (non-crypto)
        CryptoPattern {
            regex: Regex::new(r"(?i)rand\s*::\s*(?:thread_rng|random)").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::PredictableRandom,
            algorithm: Algorithm::InsecureRandom,
            base_severity: Severity::Medium,
            confidence: Confidence::Low, // rand is fine for non-crypto
            description: "rand crate may not be suitable for cryptographic purposes",
            remediation: "Use rand::rngs::OsRng or the getrandom crate for crypto",
            safe_context_patterns: vec!["test", "mock", "sample", "shuffle"],
        },

        // =======================================================================
        // Java Patterns
        // =======================================================================

        // MD5 in Java
        CryptoPattern {
            regex: Regex::new(r#"(?i)MessageDigest\s*\.\s*getInstance\s*\(\s*["']MD5["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Md5,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "MD5 MessageDigest in Java - collision attacks are practical",
            remediation: "Use SHA-256: MessageDigest.getInstance(\"SHA-256\")",
            safe_context_patterns: vec!["checksum", "etag", "cache"],
        },
        // SHA1 in Java
        CryptoPattern {
            regex: Regex::new(r#"(?i)MessageDigest\s*\.\s*getInstance\s*\(\s*["']SHA-?1["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Sha1,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "SHA-1 MessageDigest in Java - collision attacks demonstrated",
            remediation: "Use SHA-256: MessageDigest.getInstance(\"SHA-256\")",
            safe_context_patterns: vec!["git", "checksum", "legacy"],
        },
        // DES in Java
        CryptoPattern {
            regex: Regex::new(r#"(?i)Cipher\s*\.\s*getInstance\s*\(\s*["']DES[/"']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Des,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "DES Cipher in Java - 56-bit key is trivially brute-forceable",
            remediation: "Use AES: Cipher.getInstance(\"AES/GCM/NoPadding\")",
            safe_context_patterns: vec![],
        },
        // 3DES in Java
        CryptoPattern {
            regex: Regex::new(r#"(?i)Cipher\s*\.\s*getInstance\s*\(\s*["'](?:DESede|TripleDES)[/"']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::TripleDes,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Triple DES Cipher in Java - deprecated",
            remediation: "Use AES: Cipher.getInstance(\"AES/GCM/NoPadding\")",
            safe_context_patterns: vec!["legacy"],
        },
        // RC4 in Java
        CryptoPattern {
            regex: Regex::new(r#"(?i)Cipher\s*\.\s*getInstance\s*\(\s*["'](?:RC4|ARCFOUR)["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Rc4,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "RC4 Cipher in Java - broken, biased keystream",
            remediation: "Use AES: Cipher.getInstance(\"AES/GCM/NoPadding\")",
            safe_context_patterns: vec![],
        },
        // Blowfish in Java
        CryptoPattern {
            regex: Regex::new(r#"(?i)Cipher\s*\.\s*getInstance\s*\(\s*["']Blowfish[/"']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Blowfish,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Blowfish Cipher in Java - 64-bit block size leads to birthday attacks",
            remediation: "Use AES: Cipher.getInstance(\"AES/GCM/NoPadding\")",
            safe_context_patterns: vec!["legacy"],
        },
        // ECB mode in Java
        CryptoPattern {
            regex: Regex::new(r#"(?i)Cipher\s*\.\s*getInstance\s*\(\s*["'][A-Z]+/ECB/"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::InsecureMode,
            algorithm: Algorithm::EcbMode,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "ECB mode in Java - reveals patterns in encrypted data",
            remediation: "Use GCM mode: Cipher.getInstance(\"AES/GCM/NoPadding\")",
            safe_context_patterns: vec![],
        },
        // java.util.Random for crypto
        CryptoPattern {
            regex: Regex::new(r"(?i)new\s+Random\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::PredictableRandom,
            algorithm: Algorithm::InsecureRandom,
            base_severity: Severity::Medium,
            confidence: Confidence::Low, // Random is often used legitimately
            description: "java.util.Random is not cryptographically secure",
            remediation: "Use SecureRandom for cryptographic purposes",
            safe_context_patterns: vec!["test", "mock", "sample", "shuffle"],
        },
        // DSA in Java (deprecated)
        CryptoPattern {
            regex: Regex::new(r#"(?i)KeyPairGenerator\s*\.\s*getInstance\s*\(\s*["']DSA["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Dsa,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "DSA key generation in Java - deprecated in favor of ECDSA",
            remediation: "Use EC or RSA: KeyPairGenerator.getInstance(\"EC\") or KeyPairGenerator.getInstance(\"RSA\")",
            safe_context_patterns: vec!["legacy"],
        },

        // =======================================================================
        // C/C++ Patterns
        // =======================================================================

        // MD5 in C (OpenSSL)
        CryptoPattern {
            regex: Regex::new(r"(?i)\bMD5(?:_Init|_Update|_Final)?\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Md5,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "MD5 function in C/OpenSSL - collision attacks are practical",
            remediation: "Use SHA256_Init/Update/Final or EVP_sha256()",
            safe_context_patterns: vec!["checksum", "etag", "cache"],
        },
        // SHA1 in C (OpenSSL)
        CryptoPattern {
            regex: Regex::new(r"(?i)\bSHA1(?:_Init|_Update|_Final)?\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Sha1,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "SHA-1 function in C/OpenSSL - collision attacks demonstrated",
            remediation: "Use SHA256_Init/Update/Final or EVP_sha256()",
            safe_context_patterns: vec!["git", "checksum", "legacy"],
        },
        // DES in C (OpenSSL)
        CryptoPattern {
            regex: Regex::new(r"(?i)\bDES_(?:set_key|ecb_encrypt|cbc_encrypt|ncbc_encrypt)\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Des,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "DES function in C/OpenSSL - 56-bit key is trivially brute-forceable",
            remediation: "Use AES with EVP_aes_256_gcm()",
            safe_context_patterns: vec![],
        },
        // RC4 in C (OpenSSL)
        CryptoPattern {
            regex: Regex::new(r"(?i)\bRC4(?:_set_key)?\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Rc4,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "RC4 function in C/OpenSSL - broken, biased keystream",
            remediation: "Use AES-GCM with EVP_aes_256_gcm()",
            safe_context_patterns: vec![],
        },
        // Blowfish in C (OpenSSL)
        CryptoPattern {
            regex: Regex::new(r"(?i)\bBF_(?:set_key|ecb_encrypt|cbc_encrypt)\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Blowfish,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Blowfish function in C/OpenSSL - 64-bit block size leads to birthday attacks",
            remediation: "Use AES with EVP_aes_256_gcm()",
            safe_context_patterns: vec!["legacy"],
        },
        // EVP with weak algorithms
        CryptoPattern {
            regex: Regex::new(r"(?i)EVP_(?:md5|sha1)\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakHash,
            algorithm: Algorithm::Md5,
            base_severity: Severity::Medium,
            confidence: Confidence::High,
            description: "Weak hash via EVP interface - collision attacks possible",
            remediation: "Use EVP_sha256() or EVP_sha512()",
            safe_context_patterns: vec!["checksum", "etag", "cache"],
        },
        // EVP with DES
        CryptoPattern {
            regex: Regex::new(r"(?i)EVP_des_(?:ecb|cbc|cfb|ofb)\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::WeakCipher,
            algorithm: Algorithm::Des,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "DES via EVP interface - 56-bit key is trivially brute-forceable",
            remediation: "Use EVP_aes_256_gcm()",
            safe_context_patterns: vec![],
        },
        // EVP ECB mode
        CryptoPattern {
            regex: Regex::new(r"(?i)EVP_[a-z0-9]+_ecb\s*\(").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::InsecureMode,
            algorithm: Algorithm::EcbMode,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "ECB mode via EVP interface - reveals patterns in encrypted data",
            remediation: "Use GCM mode: EVP_aes_256_gcm()",
            safe_context_patterns: vec![],
        },
        // rand() for crypto in C
        CryptoPattern {
            regex: Regex::new(r"\brand\s*\(\s*\)").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::PredictableRandom,
            algorithm: Algorithm::InsecureRandom,
            base_severity: Severity::High,
            confidence: Confidence::Medium,
            description: "rand() is not cryptographically secure",
            remediation: "Use RAND_bytes() from OpenSSL or /dev/urandom",
            safe_context_patterns: vec!["test", "mock", "sample"],
        },

        // =======================================================================
        // Hardcoded Key/IV Patterns (Language-agnostic)
        // =======================================================================

        // Hardcoded encryption key patterns
        CryptoPattern {
            regex: Regex::new(r#"(?i)(?:encryption_?key|secret_?key|aes_?key|cipher_?key)\s*[=:]\s*["'][A-Za-z0-9+/=]{16,}["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::HardcodedKey,
            algorithm: Algorithm::HardcodedKeyPattern,
            base_severity: Severity::Critical,
            confidence: Confidence::High,
            description: "Hardcoded encryption key detected - keys should never be in source code",
            remediation: "Store keys in environment variables, key management service, or secure vault",
            safe_context_patterns: vec!["test", "example", "mock", "placeholder"],
        },
        // Hardcoded IV patterns
        CryptoPattern {
            regex: Regex::new(r#"(?i)(?:iv|init(?:ialization)?_?vector|nonce)\s*[=:]\s*["'][A-Za-z0-9+/=]{12,}["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::HardcodedIv,
            algorithm: Algorithm::HardcodedIvPattern,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "Hardcoded IV/nonce detected - IV should be random for each encryption",
            remediation: "Generate random IV using cryptographic random number generator",
            safe_context_patterns: vec!["test", "example", "mock"],
        },
        // Hex-encoded key patterns (32+ hex chars often means 128+ bit key)
        CryptoPattern {
            regex: Regex::new(r#"(?i)(?:key|secret)\s*[=:]\s*["'][0-9a-fA-F]{32,}["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::HardcodedKey,
            algorithm: Algorithm::HardcodedKeyPattern,
            base_severity: Severity::Critical,
            confidence: Confidence::Medium,
            description: "Possible hardcoded key (hex string) - keys should never be in source code",
            remediation: "Store keys in environment variables, key management service, or secure vault",
            safe_context_patterns: vec!["test", "example", "mock", "checksum"],
        },
        // Base64-encoded key patterns (common for 128/256-bit keys)
        CryptoPattern {
            regex: Regex::new(r#"(?i)(?:encryption|cipher|aes|secret).*[=:]\s*["'][A-Za-z0-9+/]{22,}={0,2}["']"#).expect("Invalid regex"),
            issue_type: WeakCryptoIssue::HardcodedKey,
            algorithm: Algorithm::HardcodedKeyPattern,
            base_severity: Severity::High,
            confidence: Confidence::Medium,
            description: "Possible hardcoded key (base64) - keys should never be in source code",
            remediation: "Store keys in environment variables, key management service, or secure vault",
            safe_context_patterns: vec!["test", "example", "mock"],
        },

        // =======================================================================
        // RSA Key Size Patterns
        // =======================================================================

        // RSA with small key in Python
        CryptoPattern {
            regex: Regex::new(r"(?i)RSA\.generate\s*\(\s*(?:512|768|1024)\s*[,)]").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::InsufficientKeySize,
            algorithm: Algorithm::RsaWeakKey,
            base_severity: Severity::High,
            confidence: Confidence::High,
            description: "RSA key size < 2048 bits - can be factored with modern hardware",
            remediation: "Use at least 2048-bit RSA keys, preferably 4096-bit",
            safe_context_patterns: vec!["test"],
        },
        // RSA with small key in Java
        CryptoPattern {
            regex: Regex::new(r"(?i)\.initialize\s*\(\s*(?:512|768|1024)\s*[,)]").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::InsufficientKeySize,
            algorithm: Algorithm::RsaWeakKey,
            base_severity: Severity::High,
            confidence: Confidence::Medium,
            description: "RSA key size < 2048 bits - can be factored with modern hardware",
            remediation: "Use at least 2048-bit RSA keys, preferably 4096-bit",
            safe_context_patterns: vec!["test"],
        },
        // Generic key size check for RSA
        CryptoPattern {
            regex: Regex::new(r"(?i)(?:rsa|key_?size|modulus_?(?:size|length))\s*[=:]\s*(?:512|768|1024)\b").expect("Invalid regex"),
            issue_type: WeakCryptoIssue::InsufficientKeySize,
            algorithm: Algorithm::RsaWeakKey,
            base_severity: Severity::High,
            confidence: Confidence::Medium,
            description: "RSA key size < 2048 bits specified",
            remediation: "Use at least 2048-bit RSA keys, preferably 4096-bit",
            safe_context_patterns: vec!["test", "min_", "minimum"],
        },
    ]
});

// =============================================================================
// Detector Implementation
// =============================================================================

/// Weak cryptography detector for multiple languages.
pub struct WeakCryptoDetector {
    /// Whether to skip test files
    skip_test_files: bool,
    /// Whether to include likely-safe patterns (checksums, cache keys)
    include_safe_patterns: bool,
}

impl Default for WeakCryptoDetector {
    fn default() -> Self {
        Self::new()
    }
}

impl WeakCryptoDetector {
    /// Create a new weak crypto detector with default settings.
    pub fn new() -> Self {
        Self {
            skip_test_files: false,
            include_safe_patterns: false, // By default, don't report safe usages
        }
    }

    /// Set whether to skip test files.
    #[must_use]
    pub fn skip_test_files(mut self, skip: bool) -> Self {
        self.skip_test_files = skip;
        self
    }

    /// Set whether to include likely-safe patterns (checksums, cache keys).
    #[must_use]
    pub fn include_safe_patterns(mut self, include: bool) -> Self {
        self.include_safe_patterns = include;
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

    /// Analyze context around a match to determine if it's security-sensitive.
    ///
    /// Context priority:
    /// 1. CURRENT LINE safe indicators (checksum, cache, git) - if present, line is likely safe
    /// 2. CURRENT LINE security indicators (password, auth, token) - if present, line is sensitive
    /// 3. SURROUNDING LINES security indicators - might indicate sensitive context
    /// 4. Unknown context
    fn analyze_context(line: &str, surrounding_lines: &[&str]) -> UsageContext {
        let line_lower = line.to_lowercase();
        let surrounding = surrounding_lines.join(" ").to_lowercase();

        // FIRST: Check CURRENT LINE for safe context indicators
        // If the current line mentions checksum/cache/git, it's likely safe usage
        if line_lower.contains("checksum")
            || line_lower.contains("file_hash")
            || line_lower.contains("content_hash")
            || line_lower.contains("filehash")
        {
            return UsageContext::FileChecksum;
        }
        if line_lower.contains("cache_key")
            || line_lower.contains("cache") && line_lower.contains("hash")
        {
            return UsageContext::CacheKey;
        }
        if line_lower.contains("git") && !line_lower.contains("digit") {
            return UsageContext::GitOperation;
        }
        if line_lower.contains("hmac") {
            return UsageContext::Hmac;
        }

        // SECOND: Check CURRENT LINE for security-sensitive context
        if line_lower.contains("password")
            || line_lower.contains("passwd")
            || line_lower.contains("pwd")
        {
            return UsageContext::PasswordHashing;
        }
        if line_lower.contains("signature")
            || (line_lower.contains("sign") && !line_lower.contains("assign"))
        {
            return UsageContext::Signature;
        }
        if line_lower.contains("encrypt") || line_lower.contains("cipher") {
            return UsageContext::Encryption;
        }
        if line_lower.contains("token")
            || line_lower.contains("credential")
            || line_lower.contains("auth")
        {
            return UsageContext::PasswordHashing;
        }

        // THIRD: Check SURROUNDING LINES for security-sensitive context
        // (don't inherit safe context from surrounding lines - only security context)
        if surrounding.contains("password") || surrounding.contains("passwd") {
            return UsageContext::PasswordHashing;
        }
        if surrounding.contains("signature")
            || (surrounding.contains("sign") && !surrounding.contains("assign"))
        {
            return UsageContext::Signature;
        }
        if surrounding.contains("encrypt") || surrounding.contains("cipher") {
            return UsageContext::Encryption;
        }

        UsageContext::Unknown
    }

    /// Determine if the usage is likely safe based on context.
    fn is_likely_safe(
        context: UsageContext,
        issue_type: WeakCryptoIssue,
        algorithm: &Algorithm,
    ) -> bool {
        match context {
            // File checksums with MD5 are generally acceptable
            UsageContext::FileChecksum => matches!(
                (issue_type, algorithm),
                (WeakCryptoIssue::WeakHash, Algorithm::Md5)
                    | (WeakCryptoIssue::WeakHash, Algorithm::Sha1)
            ),
            // Cache keys with weak hashes are acceptable
            UsageContext::CacheKey => matches!(
                (issue_type, algorithm),
                (WeakCryptoIssue::WeakHash, Algorithm::Md5)
                    | (WeakCryptoIssue::WeakHash, Algorithm::Sha1)
            ),
            // Git operations with SHA1 are acceptable (git's design)
            UsageContext::GitOperation => matches!(
                (issue_type, algorithm),
                (WeakCryptoIssue::WeakHash, Algorithm::Sha1)
            ),
            // HMAC with weak hash is generally still secure due to HMAC construction
            UsageContext::Hmac => matches!(
                (issue_type, algorithm),
                (WeakCryptoIssue::WeakHash, Algorithm::Md5)
                    | (WeakCryptoIssue::WeakHash, Algorithm::Sha1)
            ),
            // All other contexts are potentially unsafe
            _ => false,
        }
    }

    /// Adjust severity based on context.
    fn adjust_severity(
        base_severity: Severity,
        context: UsageContext,
        is_test: bool,
        likely_safe: bool,
    ) -> Severity {
        // Test files get reduced severity
        if is_test {
            return match base_severity {
                Severity::Critical => Severity::Low,
                Severity::High => Severity::Low,
                Severity::Medium => Severity::Info,
                _ => Severity::Info,
            };
        }

        // Likely safe usage gets reduced severity
        if likely_safe {
            return match base_severity {
                Severity::Critical | Severity::High => Severity::Info,
                _ => Severity::Info,
            };
        }

        // Security-sensitive context might increase severity
        match context {
            UsageContext::PasswordHashing => match base_severity {
                Severity::Medium => Severity::High,
                Severity::High => Severity::Critical,
                s => s,
            },
            UsageContext::Signature | UsageContext::Encryption => match base_severity {
                Severity::Medium => Severity::High,
                s => s,
            },
            _ => base_severity,
        }
    }

    /// Get remediation advice based on issue type and algorithm.
    fn get_remediation(issue_type: WeakCryptoIssue, algorithm: &Algorithm) -> String {
        match issue_type {
            WeakCryptoIssue::WeakHash => {
                match algorithm {
                    Algorithm::Md5 => "Replace MD5 with SHA-256 for integrity checks, or bcrypt/argon2 for password hashing".to_string(),
                    Algorithm::Sha1 => "Replace SHA-1 with SHA-256 for security purposes".to_string(),
                    _ => "Use SHA-256 or SHA-3 family of hash functions".to_string(),
                }
            }
            WeakCryptoIssue::WeakCipher => {
                match algorithm {
                    Algorithm::Des => "Replace DES with AES-256-GCM for authenticated encryption".to_string(),
                    Algorithm::TripleDes => "Replace 3DES with AES-256-GCM for better performance and security".to_string(),
                    Algorithm::Rc4 => "Replace RC4 with AES-GCM or ChaCha20-Poly1305".to_string(),
                    Algorithm::Blowfish => "Replace Blowfish with AES-256 (128-bit block size)".to_string(),
                    _ => "Use AES-256-GCM or ChaCha20-Poly1305 for authenticated encryption".to_string(),
                }
            }
            WeakCryptoIssue::InsecureMode => {
                "Use GCM or CCM mode for authenticated encryption, or at minimum CBC with random IV".to_string()
            }
            WeakCryptoIssue::InsufficientKeySize => {
                "Use at least 2048-bit RSA keys (4096-bit recommended), or switch to ECC (P-256 or better)".to_string()
            }
            WeakCryptoIssue::HardcodedKey => {
                "Store encryption keys in:\n  - Environment variables\n  - Key management service (AWS KMS, HashiCorp Vault)\n  - Hardware security module (HSM)\n  Never commit keys to source control".to_string()
            }
            WeakCryptoIssue::HardcodedIv => {
                "Generate a random IV for each encryption operation:\n  - Python: os.urandom(16)\n  - Node.js: crypto.randomBytes(16)\n  - Go: io.ReadFull(rand.Reader, iv)\n  Store IV alongside ciphertext".to_string()
            }
            WeakCryptoIssue::PredictableRandom => {
                "Use cryptographically secure random:\n  - Python: secrets module or os.urandom()\n  - Node.js: crypto.randomBytes()\n  - Go: crypto/rand\n  - Rust: rand::rngs::OsRng or getrandom".to_string()
            }
            WeakCryptoIssue::MissingAuthentication => {
                "Use authenticated encryption (AEAD):\n  - AES-GCM\n  - ChaCha20-Poly1305\n  Or add HMAC for integrity verification".to_string()
            }
            WeakCryptoIssue::DeprecatedFunction => {
                "Update to use the modern, recommended API for cryptographic operations".to_string()
            }
        }
    }

    /// Scan a single file for weak cryptography.
    pub fn scan_file(&self, file_path: &str) -> Result<Vec<WeakCryptoFinding>> {
        let path = Path::new(file_path);
        let is_test = Self::is_test_file(path);

        // Skip test files if configured
        if self.skip_test_files && is_test {
            return Ok(vec![]);
        }

        let source = std::fs::read_to_string(path).map_err(|e| BrrrError::io_with_path(e, path))?;
        let lines: Vec<&str> = source.lines().collect();

        let mut findings = Vec::new();
        let mut seen_locations: HashSet<(usize, usize)> = HashSet::new();

        for (line_num, line) in lines.iter().enumerate() {
            let line_number = line_num + 1;

            // Skip comments (simple heuristic)
            let trimmed = line.trim();
            if trimmed.starts_with('#')
                || trimmed.starts_with("//")
                || trimmed.starts_with('*')
                || trimmed.starts_with("/*")
                || trimmed.starts_with("'''")
                || trimmed.starts_with("\"\"\"")
            {
                continue;
            }

            // Get surrounding lines for context analysis
            let start = line_num.saturating_sub(3);
            let end = (line_num + 4).min(lines.len());
            let surrounding: Vec<&str> = lines[start..end].to_vec();

            // Check all patterns
            for pattern in CRYPTO_PATTERNS.iter() {
                if let Some(m) = pattern.regex.find(line) {
                    // Skip if we've already found something at this location
                    let loc_key = (line_number, m.start());
                    if seen_locations.contains(&loc_key) {
                        continue;
                    }
                    seen_locations.insert(loc_key);

                    // Analyze context
                    let context = Self::analyze_context(line, &surrounding);

                    // Check if this is a safe context based on pattern's safe_context_patterns
                    // BUT: only check the CURRENT line, not surrounding lines that might have different context
                    let pattern_safe = pattern
                        .safe_context_patterns
                        .iter()
                        .any(|p| line.to_lowercase().contains(p));

                    // Security-sensitive contexts should NEVER be considered safe
                    // even if nearby lines mention "checksum" etc.
                    let is_security_sensitive = matches!(
                        context,
                        UsageContext::PasswordHashing
                            | UsageContext::Signature
                            | UsageContext::Encryption
                    );

                    // Determine if likely safe - security-sensitive always wins
                    let likely_safe = !is_security_sensitive
                        && (pattern_safe
                            || Self::is_likely_safe(
                                context,
                                pattern.issue_type,
                                &pattern.algorithm,
                            ));

                    // Skip safe patterns if not including them
                    if likely_safe && !self.include_safe_patterns {
                        continue;
                    }

                    // Adjust severity
                    let severity =
                        Self::adjust_severity(pattern.base_severity, context, is_test, likely_safe);

                    // Get code snippet
                    let snippet_start = line_num.saturating_sub(1);
                    let snippet_end = (line_num + 2).min(lines.len());
                    let code_snippet = lines[snippet_start..snippet_end].join("\n");

                    findings.push(WeakCryptoFinding {
                        location: Location {
                            file: file_path.to_string(),
                            line: line_number,
                            column: m.start() + 1,
                            end_line: line_number,
                            end_column: m.end() + 1,
                        },
                        issue_type: pattern.issue_type,
                        algorithm: pattern.algorithm.clone(),
                        severity,
                        confidence: pattern.confidence,
                        context,
                        code_snippet,
                        description: pattern.description.to_string(),
                        remediation: Self::get_remediation(pattern.issue_type, &pattern.algorithm),
                        is_test_file: is_test,
                        likely_safe,
                    });
                }
            }
        }

        Ok(findings)
    }

    /// Scan a directory for weak cryptography.
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
            Some("cpp") => ["cpp", "cc", "cxx", "hpp", "h", "cu", "cuh"].iter().copied().collect(),
            _ => [
                "py", "ts", "tsx", "js", "jsx", "mjs", "cjs", "go", "rs", "java", "c", "h", "cpp",
                "cc", "cxx", "hpp", "cu", "cuh",
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

            if !extensions.contains(ext) {
                continue;
            }

            files_scanned += 1;

            if let Ok(file_findings) = self.scan_file(entry_path.to_str().unwrap_or("")) {
                findings.extend(file_findings);
            }
        }

        // Count by issue type, severity, and algorithm
        let mut issue_counts: HashMap<String, usize> = HashMap::new();
        let mut severity_counts: HashMap<String, usize> = HashMap::new();
        let mut algorithm_counts: HashMap<String, usize> = HashMap::new();

        for finding in &findings {
            *issue_counts
                .entry(finding.issue_type.to_string())
                .or_insert(0) += 1;
            *severity_counts
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
            *algorithm_counts
                .entry(finding.algorithm.to_string())
                .or_insert(0) += 1;
        }

        Ok(ScanResult {
            findings,
            files_scanned,
            issue_counts,
            severity_counts,
            algorithm_counts,
        })
    }
}

// =============================================================================
// Public API Functions
// =============================================================================

/// Scan a file or directory for weak cryptography.
///
/// # Arguments
///
/// * `path` - Path to file or directory to scan
/// * `language` - Optional language filter (python, typescript, etc.)
///
/// # Returns
///
/// Scan result with all findings
pub fn scan_weak_crypto(path: &str, language: Option<&str>) -> Result<ScanResult> {
    let detector = WeakCryptoDetector::new();
    let path_obj = Path::new(path);

    if path_obj.is_file() {
        let findings = detector.scan_file(path)?;

        let mut issue_counts: HashMap<String, usize> = HashMap::new();
        let mut severity_counts: HashMap<String, usize> = HashMap::new();
        let mut algorithm_counts: HashMap<String, usize> = HashMap::new();

        for finding in &findings {
            *issue_counts
                .entry(finding.issue_type.to_string())
                .or_insert(0) += 1;
            *severity_counts
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
            *algorithm_counts
                .entry(finding.algorithm.to_string())
                .or_insert(0) += 1;
        }

        Ok(ScanResult {
            findings,
            files_scanned: 1,
            issue_counts,
            severity_counts,
            algorithm_counts,
        })
    } else {
        detector.scan_directory(path, language)
    }
}

/// Scan a single file for weak cryptography.
pub fn scan_file_weak_crypto(
    path: &Path,
    _language: Option<&str>,
) -> Result<Vec<WeakCryptoFinding>> {
    let detector = WeakCryptoDetector::new();
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
    // Python Tests
    // =========================================================================

    #[test]
    fn test_detect_python_md5() {
        let source = r#"
import hashlib
password_hash = hashlib.md5(password.encode()).hexdigest()
        "#;
        let file = create_temp_file(source, ".py");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect MD5 usage");
        assert_eq!(findings[0].algorithm, Algorithm::Md5);
        assert_eq!(findings[0].issue_type, WeakCryptoIssue::WeakHash);
    }

    #[test]
    fn test_detect_python_md5_for_checksum_safe() {
        let source = r#"
import hashlib
# Calculate file checksum
file_checksum = hashlib.md5(file_content).hexdigest()
        "#;
        let file = create_temp_file(source, ".py");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        // By default, safe patterns are not included
        assert!(
            findings.is_empty(),
            "Should not flag MD5 for checksums by default"
        );
    }

    #[test]
    fn test_detect_python_md5_for_checksum_include_safe() {
        let source = r#"
import hashlib
# Calculate file checksum
file_checksum = hashlib.md5(file_content).hexdigest()
        "#;
        let file = create_temp_file(source, ".py");
        let detector = WeakCryptoDetector::new().include_safe_patterns(true);
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(
            !findings.is_empty(),
            "Should detect MD5 when including safe patterns"
        );
        assert!(findings[0].likely_safe, "Should mark as likely safe");
        assert_eq!(
            findings[0].severity,
            Severity::Info,
            "Severity should be reduced"
        );
    }

    #[test]
    fn test_detect_python_sha1() {
        let source = r#"
import hashlib
token = hashlib.sha1(secret.encode()).hexdigest()
        "#;
        let file = create_temp_file(source, ".py");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect SHA-1 usage");
        assert_eq!(findings[0].algorithm, Algorithm::Sha1);
    }

    #[test]
    fn test_detect_python_des() {
        let source = r#"
from Crypto.Cipher import DES
cipher = DES.new(key, DES.MODE_ECB)
        "#;
        let file = create_temp_file(source, ".py");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let des_finding = findings.iter().find(|f| f.algorithm == Algorithm::Des);
        assert!(des_finding.is_some(), "Should detect DES cipher");
        assert_eq!(des_finding.unwrap().severity, Severity::High);
    }

    #[test]
    fn test_detect_python_ecb_mode() {
        let source = r#"
from Crypto.Cipher import AES
cipher = AES.new(key, AES.MODE_ECB)
        "#;
        let file = create_temp_file(source, ".py");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let ecb_finding = findings.iter().find(|f| f.algorithm == Algorithm::EcbMode);
        assert!(ecb_finding.is_some(), "Should detect ECB mode");
    }

    #[test]
    fn test_detect_python_predictable_random() {
        let source = r#"
import random
encryption_key = ''.join(random.choice(chars) for _ in range(32))
        "#;
        let file = create_temp_file(source, ".py");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let random_finding = findings
            .iter()
            .find(|f| f.issue_type == WeakCryptoIssue::PredictableRandom);
        assert!(random_finding.is_some(), "Should detect insecure random");
    }

    // =========================================================================
    // JavaScript/TypeScript Tests
    // =========================================================================

    #[test]
    fn test_detect_nodejs_md5() {
        let source = r#"
const crypto = require('crypto');
const hash = crypto.createHash('md5').update(password).digest('hex');
        "#;
        let file = create_temp_file(source, ".js");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect MD5 in Node.js");
        assert_eq!(findings[0].algorithm, Algorithm::Md5);
    }

    #[test]
    fn test_detect_nodejs_des() {
        let source = r#"
const crypto = require('crypto');
const cipher = crypto.createCipher('des', key);
        "#;
        let file = create_temp_file(source, ".js");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        // Should find both DES and deprecated createCipher
        let des_finding = findings.iter().find(|f| f.algorithm == Algorithm::Des);
        assert!(des_finding.is_some(), "Should detect DES in Node.js");
    }

    #[test]
    fn test_detect_nodejs_ecb_mode() {
        let source = r#"
const cipher = crypto.createCipheriv('aes-256-ecb', key, null);
        "#;
        let file = create_temp_file(source, ".js");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let ecb_finding = findings.iter().find(|f| f.algorithm == Algorithm::EcbMode);
        assert!(ecb_finding.is_some(), "Should detect ECB mode in Node.js");
    }

    #[test]
    fn test_detect_cryptojs_md5() {
        let source = r#"
const hash = CryptoJS.MD5(password).toString();
        "#;
        let file = create_temp_file(source, ".js");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect CryptoJS MD5");
    }

    // =========================================================================
    // Go Tests
    // =========================================================================

    #[test]
    fn test_detect_go_md5() {
        let source = r#"
package main

import "crypto/md5"

func hash(data []byte) []byte {
    h := md5.New()
    h.Write(data)
    return h.Sum(nil)
}
        "#;
        let file = create_temp_file(source, ".go");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect MD5 in Go");
        assert_eq!(findings[0].algorithm, Algorithm::Md5);
    }

    #[test]
    fn test_detect_go_des() {
        let source = r#"
package main

import "crypto/des"

func encrypt(key, data []byte) {
    block, _ := des.NewCipher(key)
}
        "#;
        let file = create_temp_file(source, ".go");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let des_finding = findings.iter().find(|f| f.algorithm == Algorithm::Des);
        assert!(des_finding.is_some(), "Should detect DES in Go");
    }

    // =========================================================================
    // Rust Tests
    // =========================================================================

    #[test]
    fn test_detect_rust_md5() {
        let source = r#"
use md5::{Md5, Digest};

fn hash_password(password: &str) -> String {
    let result = md5::compute(password.as_bytes());
    format!("{:x}", result)
}
        "#;
        let file = create_temp_file(source, ".rs");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect MD5 in Rust");
    }

    // =========================================================================
    // Java Tests
    // =========================================================================

    #[test]
    fn test_detect_java_md5() {
        let source = r#"
import java.security.MessageDigest;

public class HashUtil {
    public static byte[] hash(String data) throws Exception {
        MessageDigest md = MessageDigest.getInstance("MD5");
        return md.digest(data.getBytes());
    }
}
        "#;
        let file = create_temp_file(source, ".java");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect MD5 in Java");
        assert_eq!(findings[0].algorithm, Algorithm::Md5);
    }

    #[test]
    fn test_detect_java_des() {
        let source = r#"
import javax.crypto.Cipher;

public class CryptoUtil {
    public static byte[] encrypt(byte[] data, byte[] key) throws Exception {
        Cipher cipher = Cipher.getInstance("DES/ECB/PKCS5Padding");
        return cipher.doFinal(data);
    }
}
        "#;
        let file = create_temp_file(source, ".java");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        // Should detect both DES and ECB
        let des_finding = findings.iter().find(|f| f.algorithm == Algorithm::Des);
        assert!(des_finding.is_some(), "Should detect DES in Java");
    }

    // =========================================================================
    // C/C++ Tests
    // =========================================================================

    #[test]
    fn test_detect_c_md5() {
        let source = r#"
#include <openssl/md5.h>

void hash_password(const char* password, unsigned char* digest) {
    MD5((unsigned char*)password, strlen(password), digest);
}
        "#;
        let file = create_temp_file(source, ".c");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect MD5 in C");
        assert_eq!(findings[0].algorithm, Algorithm::Md5);
    }

    #[test]
    fn test_detect_c_des() {
        let source = r#"
#include <openssl/des.h>

void encrypt(DES_cblock* key, unsigned char* data) {
    DES_key_schedule schedule;
    DES_set_key(key, &schedule);
    DES_ecb_encrypt((DES_cblock*)data, (DES_cblock*)data, &schedule, DES_ENCRYPT);
}
        "#;
        let file = create_temp_file(source, ".c");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let des_finding = findings.iter().find(|f| f.algorithm == Algorithm::Des);
        assert!(des_finding.is_some(), "Should detect DES in C");
    }

    // =========================================================================
    // Hardcoded Key/IV Tests
    // =========================================================================

    #[test]
    fn test_detect_hardcoded_key() {
        let source = r#"
const encryption_key = "0123456789abcdef0123456789abcdef";
const cipher = crypto.createCipheriv('aes-256-cbc', encryption_key, iv);
        "#;
        let file = create_temp_file(source, ".js");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let key_finding = findings
            .iter()
            .find(|f| f.issue_type == WeakCryptoIssue::HardcodedKey);
        assert!(key_finding.is_some(), "Should detect hardcoded key");
        assert_eq!(key_finding.unwrap().severity, Severity::Critical);
    }

    #[test]
    fn test_detect_hardcoded_iv() {
        let source = r#"
iv = "1234567890123456"
cipher = AES.new(key, AES.MODE_CBC, iv)
        "#;
        let file = create_temp_file(source, ".py");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let iv_finding = findings
            .iter()
            .find(|f| f.issue_type == WeakCryptoIssue::HardcodedIv);
        assert!(iv_finding.is_some(), "Should detect hardcoded IV");
    }

    // =========================================================================
    // RSA Key Size Tests
    // =========================================================================

    #[test]
    fn test_detect_weak_rsa_python() {
        let source = r#"
from Crypto.PublicKey import RSA
key = RSA.generate(1024)
        "#;
        let file = create_temp_file(source, ".py");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        let rsa_finding = findings
            .iter()
            .find(|f| f.issue_type == WeakCryptoIssue::InsufficientKeySize);
        assert!(rsa_finding.is_some(), "Should detect weak RSA key size");
    }

    // =========================================================================
    // Context Tests
    // =========================================================================

    #[test]
    fn test_password_context_increases_severity() {
        let source = r#"
import hashlib
# Hash password for storage
password_hash = hashlib.sha1(password.encode()).hexdigest()
        "#;
        let file = create_temp_file(source, ".py");
        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect SHA-1 usage");
        // Password context should increase severity from Medium to High
        assert!(
            findings[0].severity >= Severity::High,
            "Severity should be elevated for password context"
        );
    }

    #[test]
    fn test_test_file_reduces_severity() {
        let source = r#"
import hashlib
hash = hashlib.md5(data).hexdigest()
        "#;
        let mut file = tempfile::Builder::new()
            .suffix("_test.py")
            .tempfile()
            .expect("Failed to create temp file");
        file.write_all(source.as_bytes())
            .expect("Failed to write temp file");

        let detector = WeakCryptoDetector::new();
        let findings = detector
            .scan_file(file.path().to_str().unwrap())
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect MD5 in test file");
        assert!(findings[0].is_test_file, "Should mark as test file");
        assert!(
            findings[0].severity <= Severity::Low,
            "Severity should be reduced for test files"
        );
    }

    // =========================================================================
    // Display Tests
    // =========================================================================

    #[test]
    fn test_issue_type_display() {
        assert_eq!(WeakCryptoIssue::WeakHash.to_string(), "Weak Hash Algorithm");
        assert_eq!(
            WeakCryptoIssue::WeakCipher.to_string(),
            "Weak Cipher Algorithm"
        );
        assert_eq!(
            WeakCryptoIssue::InsecureMode.to_string(),
            "Insecure Cipher Mode"
        );
        assert_eq!(
            WeakCryptoIssue::HardcodedKey.to_string(),
            "Hardcoded Encryption Key"
        );
    }

    #[test]
    fn test_algorithm_display() {
        assert_eq!(Algorithm::Md5.to_string(), "MD5");
        assert_eq!(Algorithm::Sha1.to_string(), "SHA-1");
        assert_eq!(Algorithm::Des.to_string(), "DES");
        assert_eq!(Algorithm::EcbMode.to_string(), "ECB Mode");
    }

    #[test]
    fn test_severity_display() {
        assert_eq!(Severity::Critical.to_string(), "CRITICAL");
        assert_eq!(Severity::High.to_string(), "HIGH");
        assert_eq!(Severity::Medium.to_string(), "MEDIUM");
        assert_eq!(Severity::Low.to_string(), "LOW");
        assert_eq!(Severity::Info.to_string(), "INFO");
    }

    // =========================================================================
    // Scan Result Tests
    // =========================================================================

    #[test]
    fn test_scan_result_counts() {
        let result = ScanResult {
            findings: vec![],
            files_scanned: 10,
            issue_counts: [("Weak Hash Algorithm".to_string(), 5)]
                .into_iter()
                .collect(),
            severity_counts: [("HIGH".to_string(), 3), ("MEDIUM".to_string(), 2)]
                .into_iter()
                .collect(),
            algorithm_counts: [("MD5".to_string(), 3), ("SHA-1".to_string(), 2)]
                .into_iter()
                .collect(),
        };

        assert_eq!(result.files_scanned, 10);
        assert_eq!(result.issue_counts.get("Weak Hash Algorithm"), Some(&5));
        assert_eq!(result.severity_counts.get("HIGH"), Some(&3));
        assert_eq!(result.algorithm_counts.get("MD5"), Some(&3));
    }
}
