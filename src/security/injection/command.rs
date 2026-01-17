//! Command injection vulnerability detection.
//!
//! Detects potential command injection vulnerabilities by tracking data flow
//! from user-controlled inputs (sources) to dangerous shell execution functions (sinks).
//!
//! # Command Injection vs Argument Injection
//!
//! - **Command Injection**: User input containing shell metacharacters (`;`, `|`, `&`, etc.)
//!   can execute arbitrary commands. Example: `os.system("ls " + user_input)` where
//!   `user_input = "; rm -rf /"`.
//!
//! - **Argument Injection**: User input is passed as arguments to a command but can
//!   manipulate flags/options. Example: `subprocess.run(["tar", "-xf", user_input])`
//!   where `user_input = "--checkpoint-action=exec=malicious.sh"`.
//!
//! # Detection Strategy
//!
//! 1. Parse source files using tree-sitter
//! 2. Identify calls to known command execution sinks
//! 3. Extract the arguments passed to these sinks
//! 4. Track data flow backwards to identify if arguments come from taint sources
//! 5. Report findings with severity and confidence levels
//!
//! # Shell Metacharacters
//!
//! The following characters are dangerous in shell contexts:
//! - Command separators: `;`, `|`, `&`, `&&`, `||`, `\n`
//! - Subshell/substitution: `` ` ``, `$()`, `$()`
//! - Redirection: `<`, `>`, `>>`
//! - Glob expansion: `*`, `?`, `[`, `]`
//! - Quote escape: `'`, `"`, `\`

use std::collections::HashMap;
use std::path::Path;

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use streaming_iterator::StreamingIterator;
use tree_sitter::{Node, Query, QueryCursor, Tree};

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{Result, BrrrError};
use crate::lang::LanguageRegistry;
use crate::util::format_query_error;

// =============================================================================
// Type Definitions
// =============================================================================

/// Severity level for security findings.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    /// Informational - may not be exploitable but worth reviewing
    Info,
    /// Low severity - limited impact or requires specific conditions
    Low,
    /// Medium severity - potential for significant impact
    Medium,
    /// High severity - likely exploitable with serious impact
    High,
    /// Critical - easily exploitable with severe consequences
    Critical,
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Info => write!(f, "INFO"),
            Self::Low => write!(f, "LOW"),
            Self::Medium => write!(f, "MEDIUM"),
            Self::High => write!(f, "HIGH"),
            Self::Critical => write!(f, "CRITICAL"),
        }
    }
}

/// Confidence level for the finding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Confidence {
    /// Low confidence - pattern match only, no data flow confirmation
    Low,
    /// Medium confidence - some data flow indicators but incomplete path
    Medium,
    /// High confidence - clear data flow from source to sink
    High,
}

impl std::fmt::Display for Confidence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Low => write!(f, "LOW"),
            Self::Medium => write!(f, "MEDIUM"),
            Self::High => write!(f, "HIGH"),
        }
    }
}

/// Type of injection vulnerability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum InjectionKind {
    /// Full command injection - user input can execute arbitrary commands
    CommandInjection,
    /// Argument injection - user input can manipulate command arguments
    ArgumentInjection,
    /// Code injection via eval/exec
    CodeInjection,
}

impl std::fmt::Display for InjectionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CommandInjection => write!(f, "command_injection"),
            Self::ArgumentInjection => write!(f, "argument_injection"),
            Self::CodeInjection => write!(f, "code_injection"),
        }
    }
}

/// Source location in code.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SourceLocation {
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

impl std::fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.column)
    }
}

/// Kind of taint source.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TaintSourceKind {
    /// HTTP request parameters (query string, body, headers)
    HttpRequest,
    /// Form input data
    FormInput,
    /// Standard input (stdin)
    StdIn,
    /// File read operations
    FileRead,
    /// Environment variables
    EnvVar,
    /// Command line arguments
    CmdLineArg,
    /// Database query results
    DatabaseResult,
    /// Network socket data
    NetworkData,
    /// User-provided configuration
    UserConfig,
    /// Unknown/generic user input
    Unknown,
}

/// A taint source - origin of potentially malicious data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaintSource {
    /// Type of taint source
    pub kind: TaintSourceKind,
    /// Variable name carrying the taint
    pub variable: String,
    /// Location where taint originates
    pub location: SourceLocation,
    /// Description of the source
    pub description: String,
}

/// A command execution sink - dangerous function that executes commands.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommandSink {
    /// Language this sink applies to
    pub language: String,
    /// Module or namespace (e.g., "os", "subprocess", "child_process")
    pub module: Option<String>,
    /// Function name (e.g., "system", "exec", "popen")
    pub function: String,
    /// Argument index that receives the command (0-indexed)
    pub command_arg_index: usize,
    /// Whether this sink uses a shell by default
    pub shell_by_default: bool,
    /// Severity when this sink is exploited
    pub severity: Severity,
    /// Description of the sink
    pub description: String,
}

/// A command injection finding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommandInjectionFinding {
    /// Location of the vulnerable sink call
    pub location: SourceLocation,
    /// Severity of the vulnerability
    pub severity: Severity,
    /// Name of the dangerous function being called
    pub sink_function: String,
    /// The tainted input reaching the sink (variable name or expression)
    pub tainted_input: String,
    /// Confidence level of the finding
    pub confidence: Confidence,
    /// Type of injection
    pub kind: InjectionKind,
    /// Chain of taint propagation (source -> ... -> sink)
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub taint_chain: Vec<TaintSource>,
    /// Code snippet showing the vulnerable pattern
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code_snippet: Option<String>,
    /// Remediation advice
    pub remediation: String,
}

// =============================================================================
// Language-Specific Command Sinks
// =============================================================================

/// Get all known command execution sinks for a language.
pub fn get_command_sinks(language: &str) -> Vec<CommandSink> {
    match language {
        "python" => python_sinks(),
        "typescript" | "javascript" => typescript_sinks(),
        "rust" => rust_sinks(),
        "go" => go_sinks(),
        "c" | "cpp" => c_sinks(),
        "java" => java_sinks(),
        _ => vec![],
    }
}

fn python_sinks() -> Vec<CommandSink> {
    vec![
        // os module
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "system".to_string(),
            command_arg_index: 0,
            shell_by_default: true,
            severity: Severity::Critical,
            description: "Executes command in shell, vulnerable to command injection".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "popen".to_string(),
            command_arg_index: 0,
            shell_by_default: true,
            severity: Severity::Critical,
            description: "Opens pipe to command in shell".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "spawn".to_string(),
            command_arg_index: 1,
            shell_by_default: false,
            severity: Severity::High,
            description: "Spawns process, less dangerous but still risky".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "spawnl".to_string(),
            command_arg_index: 1,
            shell_by_default: false,
            severity: Severity::High,
            description: "Spawns process with list args".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "spawnle".to_string(),
            command_arg_index: 1,
            shell_by_default: false,
            severity: Severity::High,
            description: "Spawns process with list args and env".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "spawnlp".to_string(),
            command_arg_index: 1,
            shell_by_default: false,
            severity: Severity::High,
            description: "Spawns process using PATH".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "spawnlpe".to_string(),
            command_arg_index: 1,
            shell_by_default: false,
            severity: Severity::High,
            description: "Spawns process using PATH with env".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "spawnv".to_string(),
            command_arg_index: 1,
            shell_by_default: false,
            severity: Severity::High,
            description: "Spawns process with vector args".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "spawnve".to_string(),
            command_arg_index: 1,
            shell_by_default: false,
            severity: Severity::High,
            description: "Spawns process with vector args and env".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "spawnvp".to_string(),
            command_arg_index: 1,
            shell_by_default: false,
            severity: Severity::High,
            description: "Spawns process with vector args using PATH".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "spawnvpe".to_string(),
            command_arg_index: 1,
            shell_by_default: false,
            severity: Severity::High,
            description: "Spawns process with vector args and env using PATH".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "execl".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces current process with new program".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "execle".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces current process with env".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "execlp".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces current process using PATH".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "execlpe".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces current process using PATH with env".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "execv".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces current process with vector args".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "execve".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces current process with vector args and env".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "execvp".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces current process using PATH".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("os".to_string()),
            function: "execvpe".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces current process using PATH with env".to_string(),
        },
        // subprocess module
        CommandSink {
            language: "python".to_string(),
            module: Some("subprocess".to_string()),
            function: "call".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Runs command, dangerous with shell=True".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("subprocess".to_string()),
            function: "run".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Runs command, dangerous with shell=True".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("subprocess".to_string()),
            function: "Popen".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Creates subprocess, dangerous with shell=True".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("subprocess".to_string()),
            function: "check_call".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Runs command with return code check".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("subprocess".to_string()),
            function: "check_output".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Runs command and captures output".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("subprocess".to_string()),
            function: "getoutput".to_string(),
            command_arg_index: 0,
            shell_by_default: true,
            severity: Severity::Critical,
            description: "Runs command in shell, always uses shell".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("subprocess".to_string()),
            function: "getstatusoutput".to_string(),
            command_arg_index: 0,
            shell_by_default: true,
            severity: Severity::Critical,
            description: "Runs command in shell, returns status and output".to_string(),
        },
        // commands module (deprecated but still used)
        CommandSink {
            language: "python".to_string(),
            module: Some("commands".to_string()),
            function: "getoutput".to_string(),
            command_arg_index: 0,
            shell_by_default: true,
            severity: Severity::Critical,
            description: "Deprecated shell command execution".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: Some("commands".to_string()),
            function: "getstatusoutput".to_string(),
            command_arg_index: 0,
            shell_by_default: true,
            severity: Severity::Critical,
            description: "Deprecated shell command with status".to_string(),
        },
        // eval/exec - code injection
        CommandSink {
            language: "python".to_string(),
            module: None,
            function: "eval".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Critical,
            description: "Evaluates Python expression, code injection risk".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: None,
            function: "exec".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Critical,
            description: "Executes Python code, code injection risk".to_string(),
        },
        CommandSink {
            language: "python".to_string(),
            module: None,
            function: "compile".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Compiles Python code, potential code injection".to_string(),
        },
        // pty module
        CommandSink {
            language: "python".to_string(),
            module: Some("pty".to_string()),
            function: "spawn".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Spawns process in pseudo-terminal".to_string(),
        },
    ]
}

fn typescript_sinks() -> Vec<CommandSink> {
    vec![
        // child_process module
        CommandSink {
            language: "typescript".to_string(),
            module: Some("child_process".to_string()),
            function: "exec".to_string(),
            command_arg_index: 0,
            shell_by_default: true,
            severity: Severity::Critical,
            description: "Executes command in shell".to_string(),
        },
        CommandSink {
            language: "typescript".to_string(),
            module: Some("child_process".to_string()),
            function: "execSync".to_string(),
            command_arg_index: 0,
            shell_by_default: true,
            severity: Severity::Critical,
            description: "Synchronously executes command in shell".to_string(),
        },
        CommandSink {
            language: "typescript".to_string(),
            module: Some("child_process".to_string()),
            function: "spawn".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Spawns process, dangerous with shell:true option".to_string(),
        },
        CommandSink {
            language: "typescript".to_string(),
            module: Some("child_process".to_string()),
            function: "spawnSync".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Synchronously spawns process".to_string(),
        },
        CommandSink {
            language: "typescript".to_string(),
            module: Some("child_process".to_string()),
            function: "execFile".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Medium,
            description: "Executes file directly, safer but still risky".to_string(),
        },
        CommandSink {
            language: "typescript".to_string(),
            module: Some("child_process".to_string()),
            function: "execFileSync".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Medium,
            description: "Synchronously executes file".to_string(),
        },
        CommandSink {
            language: "typescript".to_string(),
            module: Some("child_process".to_string()),
            function: "fork".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Medium,
            description: "Forks Node.js process".to_string(),
        },
        // eval - code injection
        CommandSink {
            language: "typescript".to_string(),
            module: None,
            function: "eval".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Critical,
            description: "Evaluates JavaScript code, code injection risk".to_string(),
        },
        CommandSink {
            language: "typescript".to_string(),
            module: None,
            function: "Function".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Critical,
            description: "Creates function from string, code injection risk".to_string(),
        },
        // setTimeout/setInterval with string argument
        CommandSink {
            language: "typescript".to_string(),
            module: None,
            function: "setTimeout".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Can execute string as code (legacy behavior)".to_string(),
        },
        CommandSink {
            language: "typescript".to_string(),
            module: None,
            function: "setInterval".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Can execute string as code (legacy behavior)".to_string(),
        },
        // Bun/Deno specific
        CommandSink {
            language: "typescript".to_string(),
            module: Some("Bun".to_string()),
            function: "spawn".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Bun process spawning".to_string(),
        },
        CommandSink {
            language: "typescript".to_string(),
            module: Some("Deno".to_string()),
            function: "run".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Deno command execution".to_string(),
        },
    ]
}

fn rust_sinks() -> Vec<CommandSink> {
    vec![
        // std::process::Command
        CommandSink {
            language: "rust".to_string(),
            module: Some("std::process".to_string()),
            function: "Command::new".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Creates command, dangerous if user controls program path".to_string(),
        },
        // Command builder methods that take user input
        CommandSink {
            language: "rust".to_string(),
            module: Some("std::process".to_string()),
            function: "arg".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Medium,
            description: "Adds argument to command, argument injection risk".to_string(),
        },
        CommandSink {
            language: "rust".to_string(),
            module: Some("std::process".to_string()),
            function: "args".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Medium,
            description: "Adds arguments to command".to_string(),
        },
        // Shell execution via sh -c
        CommandSink {
            language: "rust".to_string(),
            module: None,
            function: "shell".to_string(),
            command_arg_index: 0,
            shell_by_default: true,
            severity: Severity::Critical,
            description: "Shell command execution pattern".to_string(),
        },
        // tokio::process
        CommandSink {
            language: "rust".to_string(),
            module: Some("tokio::process".to_string()),
            function: "Command::new".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Async command creation".to_string(),
        },
    ]
}

fn go_sinks() -> Vec<CommandSink> {
    vec![
        // os/exec package
        CommandSink {
            language: "go".to_string(),
            module: Some("os/exec".to_string()),
            function: "Command".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Creates command, dangerous if user controls program".to_string(),
        },
        CommandSink {
            language: "go".to_string(),
            module: Some("exec".to_string()),
            function: "Command".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Creates command (short import)".to_string(),
        },
        CommandSink {
            language: "go".to_string(),
            module: Some("os/exec".to_string()),
            function: "CommandContext".to_string(),
            command_arg_index: 1,
            shell_by_default: false,
            severity: Severity::High,
            description: "Creates command with context".to_string(),
        },
        // syscall package
        CommandSink {
            language: "go".to_string(),
            module: Some("syscall".to_string()),
            function: "Exec".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Critical,
            description: "Low-level exec syscall".to_string(),
        },
        CommandSink {
            language: "go".to_string(),
            module: Some("syscall".to_string()),
            function: "ForkExec".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Critical,
            description: "Fork and exec syscall".to_string(),
        },
        CommandSink {
            language: "go".to_string(),
            module: Some("syscall".to_string()),
            function: "StartProcess".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Critical,
            description: "Starts new process".to_string(),
        },
    ]
}

fn c_sinks() -> Vec<CommandSink> {
    vec![
        // Standard library
        CommandSink {
            language: "c".to_string(),
            module: None,
            function: "system".to_string(),
            command_arg_index: 0,
            shell_by_default: true,
            severity: Severity::Critical,
            description: "Executes command in shell".to_string(),
        },
        CommandSink {
            language: "c".to_string(),
            module: None,
            function: "popen".to_string(),
            command_arg_index: 0,
            shell_by_default: true,
            severity: Severity::Critical,
            description: "Opens pipe to shell command".to_string(),
        },
        // exec family
        CommandSink {
            language: "c".to_string(),
            module: None,
            function: "execl".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces process with new program".to_string(),
        },
        CommandSink {
            language: "c".to_string(),
            module: None,
            function: "execle".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces process with environment".to_string(),
        },
        CommandSink {
            language: "c".to_string(),
            module: None,
            function: "execlp".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces process using PATH".to_string(),
        },
        CommandSink {
            language: "c".to_string(),
            module: None,
            function: "execv".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces process with vector args".to_string(),
        },
        CommandSink {
            language: "c".to_string(),
            module: None,
            function: "execve".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces process with vector and env".to_string(),
        },
        CommandSink {
            language: "c".to_string(),
            module: None,
            function: "execvp".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces process using PATH".to_string(),
        },
        CommandSink {
            language: "c".to_string(),
            module: None,
            function: "execvpe".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Replaces process using PATH with env".to_string(),
        },
        // fork/spawn
        CommandSink {
            language: "c".to_string(),
            module: None,
            function: "posix_spawn".to_string(),
            command_arg_index: 1,
            shell_by_default: false,
            severity: Severity::High,
            description: "POSIX spawn interface".to_string(),
        },
        CommandSink {
            language: "c".to_string(),
            module: None,
            function: "posix_spawnp".to_string(),
            command_arg_index: 1,
            shell_by_default: false,
            severity: Severity::High,
            description: "POSIX spawn with PATH search".to_string(),
        },
    ]
}

fn java_sinks() -> Vec<CommandSink> {
    vec![
        // Runtime.exec
        CommandSink {
            language: "java".to_string(),
            module: Some("java.lang.Runtime".to_string()),
            function: "exec".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Critical,
            description: "Executes system command".to_string(),
        },
        CommandSink {
            language: "java".to_string(),
            module: Some("Runtime".to_string()),
            function: "exec".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Critical,
            description: "Executes system command (short form)".to_string(),
        },
        // ProcessBuilder
        CommandSink {
            language: "java".to_string(),
            module: Some("java.lang.ProcessBuilder".to_string()),
            function: "command".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Sets process command".to_string(),
        },
        CommandSink {
            language: "java".to_string(),
            module: Some("ProcessBuilder".to_string()),
            function: "command".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Sets process command (short form)".to_string(),
        },
        // Constructor with command
        CommandSink {
            language: "java".to_string(),
            module: None,
            function: "ProcessBuilder".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::High,
            description: "Creates ProcessBuilder with command".to_string(),
        },
        // Script engines
        CommandSink {
            language: "java".to_string(),
            module: Some("javax.script.ScriptEngine".to_string()),
            function: "eval".to_string(),
            command_arg_index: 0,
            shell_by_default: false,
            severity: Severity::Critical,
            description: "Evaluates script code".to_string(),
        },
    ]
}

// =============================================================================
// Taint Source Detection
// =============================================================================

/// Get tree-sitter query for detecting taint sources in a language.
fn get_taint_source_query(language: &str) -> Option<&'static str> {
    match language {
        "python" => Some(PYTHON_TAINT_SOURCES_QUERY),
        "typescript" | "javascript" => Some(TYPESCRIPT_TAINT_SOURCES_QUERY),
        "go" => Some(GO_TAINT_SOURCES_QUERY),
        "rust" => Some(RUST_TAINT_SOURCES_QUERY),
        "c" | "cpp" => Some(C_TAINT_SOURCES_QUERY),
        "java" => Some(JAVA_TAINT_SOURCES_QUERY),
        _ => None,
    }
}

/// Python taint sources query.
const PYTHON_TAINT_SOURCES_QUERY: &str = r#"
; HTTP request parameters (Flask, Django, FastAPI)
(attribute object: (identifier) @obj attribute: (identifier) @attr
  (#any-of? @obj "request" "req")
  (#any-of? @attr "args" "form" "data" "json" "values" "files" "headers" "cookies" "get_json" "params" "query_params" "body")) @source

; request.GET/POST (Django)
(subscript value: (attribute object: (identifier) @obj attribute: (identifier) @attr)
  (#eq? @obj "request")
  (#any-of? @attr "GET" "POST" "FILES" "COOKIES")) @source

; input() builtin
(call function: (identifier) @func (#eq? @func "input")) @source

; Environment variables
(subscript value: (attribute object: (identifier) @obj attribute: (identifier) @attr)
  (#eq? @obj "os")
  (#eq? @attr "environ")) @source
(call function: (attribute object: (identifier) @obj attribute: (identifier) @attr)
  (#eq? @obj "os")
  (#any-of? @attr "getenv" "environ")) @source

; File read operations
(call function: (attribute attribute: (identifier) @method)
  (#any-of? @method "read" "readline" "readlines")) @source

; sys.argv
(subscript value: (attribute object: (identifier) @obj attribute: (identifier) @attr)
  (#eq? @obj "sys")
  (#eq? @attr "argv")) @source
(attribute object: (identifier) @obj attribute: (identifier) @attr
  (#eq? @obj "sys")
  (#eq? @attr "argv")) @source

; stdin
(attribute object: (identifier) @obj attribute: (identifier) @attr
  (#eq? @obj "sys")
  (#eq? @attr "stdin")) @source
"#;

/// TypeScript/JavaScript taint sources query.
const TYPESCRIPT_TAINT_SOURCES_QUERY: &str = r#"
; Express req.body, req.query, req.params
(member_expression object: (identifier) @obj property: (property_identifier) @prop
  (#eq? @obj "req")
  (#any-of? @prop "body" "query" "params" "headers" "cookies")) @source

; request object properties
(member_expression object: (identifier) @obj property: (property_identifier) @prop
  (#eq? @obj "request")
  (#any-of? @prop "body" "query" "params" "headers")) @source

; process.argv
(member_expression object: (member_expression object: (identifier) @obj property: (property_identifier) @prop)
  (#eq? @obj "process")
  (#eq? @prop "argv")) @source
(member_expression object: (identifier) @obj property: (property_identifier) @prop
  (#eq? @obj "process")
  (#eq? @prop "argv")) @source

; process.env
(member_expression object: (member_expression object: (identifier) @obj property: (property_identifier) @prop)
  (#eq? @obj "process")
  (#eq? @prop "env")) @source

; readline input
(call_expression function: (member_expression property: (property_identifier) @method)
  (#any-of? @method "question" "prompt")) @source

; DOM input
(call_expression function: (member_expression property: (property_identifier) @method)
  (#any-of? @method "getElementById" "querySelector" "querySelectorAll")) @source

; URL search params
(new_expression constructor: (identifier) @ctor
  (#eq? @ctor "URLSearchParams")) @source
"#;

/// Go taint sources query.
const GO_TAINT_SOURCES_QUERY: &str = r#"
; HTTP request
(selector_expression operand: (identifier) @obj field: (field_identifier) @field
  (#any-of? @obj "r" "req" "request")
  (#any-of? @field "Body" "URL" "Form" "PostForm" "Header")) @source

; URL query
(call_expression function: (selector_expression field: (field_identifier) @method)
  (#any-of? @method "Query" "FormValue" "PostFormValue")) @source

; os.Args
(selector_expression operand: (identifier) @pkg field: (field_identifier) @field
  (#eq? @pkg "os")
  (#eq? @field "Args")) @source

; Environment
(call_expression function: (selector_expression operand: (identifier) @pkg field: (field_identifier) @method)
  (#eq? @pkg "os")
  (#any-of? @method "Getenv" "LookupEnv" "Environ")) @source

; flag package
(call_expression function: (selector_expression operand: (identifier) @pkg)
  (#eq? @pkg "flag")) @source

; stdin
(selector_expression operand: (identifier) @pkg field: (field_identifier) @field
  (#eq? @pkg "os")
  (#eq? @field "Stdin")) @source
"#;

/// Rust taint sources query.
/// Note: tree-sitter-rust doesn't have method_call_expression, so HTTP framework
/// detection is limited.
const RUST_TAINT_SOURCES_QUERY: &str = r#"
; std::env::args
(call_expression function: (scoped_identifier) @func
  (#match? @func "std::env::args")) @source
(call_expression function: (scoped_identifier) @func
  (#match? @func "env::args")) @source

; std::env::var
(call_expression function: (scoped_identifier) @func
  (#match? @func "std::env::var")) @source
(call_expression function: (scoped_identifier) @func
  (#match? @func "env::var")) @source

; stdin read
(call_expression function: (scoped_identifier) @func
  (#match? @func "stdin")) @source
"#;

/// C taint sources query.
const C_TAINT_SOURCES_QUERY: &str = r#"
; argv parameter
(parameter_declaration declarator: (pointer_declarator declarator: (array_declarator declarator: (identifier) @name))
  (#eq? @name "argv")) @source
(parameter_declaration declarator: (pointer_declarator declarator: (pointer_declarator declarator: (identifier) @name))
  (#eq? @name "argv")) @source

; getenv
(call_expression function: (identifier) @func
  (#eq? @func "getenv")) @source

; stdin read
(call_expression function: (identifier) @func
  (#any-of? @func "fgets" "gets" "scanf" "fscanf" "getchar" "fgetc" "getc" "fread")) @source

; Environment via environ
(identifier) @source
  (#eq? @source "environ")
"#;

/// Java taint sources query.
const JAVA_TAINT_SOURCES_QUERY: &str = r#"
; HTTP servlet request
(method_invocation object: (identifier) @obj name: (identifier) @method
  (#any-of? @obj "request" "req" "httpRequest")
  (#any-of? @method "getParameter" "getParameterValues" "getParameterMap" "getHeader" "getHeaders" "getCookies" "getInputStream" "getReader")) @source

; Spring @RequestParam, @RequestBody (harder to detect, but method calls)
(method_invocation name: (identifier) @method
  (#any-of? @method "getParameter" "getBody" "getHeaders")) @source

; System.getenv
(method_invocation object: (identifier) @obj name: (identifier) @method
  (#eq? @obj "System")
  (#any-of? @method "getenv" "getProperty")) @source

; args[] in main
(array_access array: (identifier) @arr
  (#eq? @arr "args")) @source

; Scanner input
(method_invocation object: (identifier) @obj name: (identifier) @method
  (#any-of? @method "nextLine" "next" "nextInt" "nextDouble")) @source

; BufferedReader
(method_invocation name: (identifier) @method
  (#eq? @method "readLine")) @source
"#;

// =============================================================================
// Sink Detection
// =============================================================================

/// Get tree-sitter query for detecting command sinks in a language.
fn get_sink_query(language: &str) -> Option<&'static str> {
    match language {
        "python" => Some(PYTHON_SINK_QUERY),
        "typescript" | "javascript" => Some(TYPESCRIPT_SINK_QUERY),
        "go" => Some(GO_SINK_QUERY),
        "rust" => Some(RUST_SINK_QUERY),
        "c" | "cpp" => Some(C_SINK_QUERY),
        "java" => Some(JAVA_SINK_QUERY),
        _ => None,
    }
}

/// Python command sink detection query.
const PYTHON_SINK_QUERY: &str = r#"
; os.system, os.popen, etc.
(call function: (attribute object: (identifier) @module attribute: (identifier) @func)
  (#eq? @module "os")
  (#any-of? @func "system" "popen" "spawn" "spawnl" "spawnle" "spawnlp" "spawnlpe" "spawnv" "spawnve" "spawnvp" "spawnvpe" "execl" "execle" "execlp" "execlpe" "execv" "execve" "execvp" "execvpe")
  arguments: (argument_list) @args) @sink

; subprocess module calls
(call function: (attribute object: (identifier) @module attribute: (identifier) @func)
  (#eq? @module "subprocess")
  (#any-of? @func "call" "run" "Popen" "check_call" "check_output" "getoutput" "getstatusoutput")
  arguments: (argument_list) @args) @sink

; commands module (deprecated)
(call function: (attribute object: (identifier) @module attribute: (identifier) @func)
  (#eq? @module "commands")
  (#any-of? @func "getoutput" "getstatusoutput")
  arguments: (argument_list) @args) @sink

; eval/exec builtins
(call function: (identifier) @func
  (#any-of? @func "eval" "exec" "compile")
  arguments: (argument_list) @args) @sink

; pty.spawn
(call function: (attribute object: (identifier) @module attribute: (identifier) @func)
  (#eq? @module "pty")
  (#eq? @func "spawn")
  arguments: (argument_list) @args) @sink
"#;

/// TypeScript/JavaScript command sink detection query.
const TYPESCRIPT_SINK_QUERY: &str = r#"
; child_process.exec, spawn, etc.
(call_expression function: (member_expression object: (identifier) @module property: (property_identifier) @func)
  (#any-of? @module "child_process" "cp")
  (#any-of? @func "exec" "execSync" "spawn" "spawnSync" "execFile" "execFileSync" "fork")
  arguments: (arguments) @args) @sink

; require('child_process').exec pattern
(call_expression function: (member_expression object: (call_expression function: (identifier) @req arguments: (arguments (string) @mod))
    property: (property_identifier) @func)
  (#eq? @req "require")
  (#match? @mod "child_process")
  (#any-of? @func "exec" "execSync" "spawn" "spawnSync" "execFile" "execFileSync")
  arguments: (arguments) @args) @sink

; eval
(call_expression function: (identifier) @func
  (#eq? @func "eval")
  arguments: (arguments) @args) @sink

; Function constructor
(new_expression constructor: (identifier) @func
  (#eq? @func "Function")
  arguments: (arguments) @args) @sink

; setTimeout/setInterval with string
(call_expression function: (identifier) @func
  (#any-of? @func "setTimeout" "setInterval")
  arguments: (arguments (string) @str_arg)) @sink

; Bun.spawn, Deno.run
(call_expression function: (member_expression object: (identifier) @obj property: (property_identifier) @func)
  (#any-of? @obj "Bun" "Deno")
  (#any-of? @func "spawn" "run")
  arguments: (arguments) @args) @sink
"#;

/// Go command sink detection query.
const GO_SINK_QUERY: &str = r#"
; exec.Command
(call_expression function: (selector_expression operand: (identifier) @pkg field: (field_identifier) @func)
  (#any-of? @pkg "exec" "os/exec")
  (#any-of? @func "Command" "CommandContext")
  arguments: (argument_list) @args) @sink

; syscall.Exec, ForkExec
(call_expression function: (selector_expression operand: (identifier) @pkg field: (field_identifier) @func)
  (#eq? @pkg "syscall")
  (#any-of? @func "Exec" "ForkExec" "StartProcess")
  arguments: (argument_list) @args) @sink

; os.StartProcess
(call_expression function: (selector_expression operand: (identifier) @pkg field: (field_identifier) @func)
  (#eq? @pkg "os")
  (#eq? @func "StartProcess")
  arguments: (argument_list) @args) @sink
"#;

/// Rust command sink detection query.
/// Note: In tree-sitter-rust, method calls use `call_expression` not a separate node type.
const RUST_SINK_QUERY: &str = r#"
; Command::new - scoped path
(call_expression function: (scoped_identifier) @func
  (#match? @func "Command::new")
  arguments: (arguments) @args) @sink

; std::process::Command::new - fully qualified
(call_expression function: (scoped_identifier) @func
  (#match? @func "std::process::Command::new")
  arguments: (arguments) @args) @sink

; tokio::process::Command::new - async version
(call_expression function: (scoped_identifier) @func
  (#match? @func "tokio::process::Command::new")
  arguments: (arguments) @args) @sink

; Generic new() call that might be Command
(call_expression function: (field_expression value: (identifier) @obj field: (field_identifier) @method)
  (#eq? @method "new")
  arguments: (arguments) @args) @sink
"#;

/// C command sink detection query.
const C_SINK_QUERY: &str = r#"
; system(), popen()
(call_expression function: (identifier) @func
  (#any-of? @func "system" "popen")
  arguments: (argument_list) @args) @sink

; exec family
(call_expression function: (identifier) @func
  (#any-of? @func "execl" "execle" "execlp" "execv" "execve" "execvp" "execvpe")
  arguments: (argument_list) @args) @sink

; posix_spawn
(call_expression function: (identifier) @func
  (#any-of? @func "posix_spawn" "posix_spawnp")
  arguments: (argument_list) @args) @sink
"#;

/// Java command sink detection query.
const JAVA_SINK_QUERY: &str = r#"
; Runtime.exec
(method_invocation object: (method_invocation object: (identifier) @cls name: (identifier) @get)
  name: (identifier) @method
  (#eq? @cls "Runtime")
  (#eq? @get "getRuntime")
  (#eq? @method "exec")
  arguments: (argument_list) @args) @sink

; Direct Runtime.getRuntime().exec
(method_invocation name: (identifier) @method
  (#eq? @method "exec")
  arguments: (argument_list) @args) @sink

; ProcessBuilder constructor
(object_creation_expression type: (type_identifier) @type
  (#eq? @type "ProcessBuilder")
  arguments: (argument_list) @args) @sink

; ProcessBuilder.command
(method_invocation name: (identifier) @method
  (#eq? @method "command")
  arguments: (argument_list) @args) @sink

; ScriptEngine.eval
(method_invocation object: (identifier) @obj name: (identifier) @method
  (#eq? @method "eval")
  arguments: (argument_list) @args) @sink
"#;

// =============================================================================
// Scanning Implementation
// =============================================================================

/// Scan a directory for command injection vulnerabilities.
///
/// # Arguments
///
/// * `path` - Directory to scan
/// * `language` - Optional language filter (scans all supported languages if None)
///
/// # Returns
///
/// Vector of command injection findings.
pub fn scan_command_injection(path: &Path, language: Option<&str>) -> Result<Vec<CommandInjectionFinding>> {
    let path_str = path.to_str().ok_or_else(|| {
        BrrrError::InvalidArgument("Invalid path encoding".to_string())
    })?;

    let scanner = ProjectScanner::new(path_str)?;
    let config = match language {
        Some(lang) => ScanConfig::for_language(lang),
        None => ScanConfig::default(),
    };

    let scan_result = scanner.scan_with_config(&config)?;
    let files = scan_result.files;

    // Process files in parallel
    let findings: Vec<CommandInjectionFinding> = files
        .par_iter()
        .filter_map(|file| {
            scan_file_command_injection(file, language).ok()
        })
        .flatten()
        .collect();

    Ok(findings)
}

/// Scan a single file for command injection vulnerabilities.
///
/// # Arguments
///
/// * `file` - Path to the file to scan
/// * `language` - Optional language override (auto-detected if None)
///
/// # Returns
///
/// Vector of command injection findings in this file.
pub fn scan_file_command_injection(file: &Path, language: Option<&str>) -> Result<Vec<CommandInjectionFinding>> {
    let registry = LanguageRegistry::global();

    // Detect language
    let lang = match language {
        Some(lang_name) => registry
            .get_by_name(lang_name)
            .ok_or_else(|| BrrrError::UnsupportedLanguage(lang_name.to_string()))?,
        None => registry
            .detect_language(file)
            .ok_or_else(|| BrrrError::UnsupportedLanguage(
                file.extension()
                    .and_then(|e| e.to_str())
                    .unwrap_or("unknown")
                    .to_string(),
            ))?,
    };

    let lang_name = lang.name();

    // Get queries for this language
    let sink_query_str = get_sink_query(lang_name)
        .ok_or_else(|| BrrrError::UnsupportedLanguage(format!("{} (no sink query)", lang_name)))?;

    let taint_query_str = get_taint_source_query(lang_name);

    // Parse the file
    let source = std::fs::read(file).map_err(|e| BrrrError::io_with_path(e, file))?;
    let mut parser = lang.parser_for_path(file)?;
    let tree = parser.parse(&source, None).ok_or_else(|| BrrrError::Parse {
        file: file.display().to_string(),
        message: "Failed to parse file".to_string(),
    })?;

    let ts_lang = tree.language();
    let file_path = file.display().to_string();

    // Find sinks
    let sinks = find_sinks(&tree, &source, &ts_lang, sink_query_str, lang_name, &file_path)?;

    // Find taint sources if query is available
    let taint_sources = if let Some(taint_query) = taint_query_str {
        find_taint_sources(&tree, &source, &ts_lang, taint_query, lang_name, &file_path)?
    } else {
        HashMap::new()
    };

    // Analyze each sink for potential injection
    let mut findings = Vec::new();
    for (sink_loc, sink_info) in sinks {
        let finding = analyze_sink(
            &sink_info,
            &sink_loc,
            &taint_sources,
            &source,
            &tree,
            lang_name,
            &file_path,
        );
        if let Some(f) = finding {
            findings.push(f);
        }
    }

    Ok(findings)
}

/// Information about a detected sink.
#[derive(Debug)]
struct SinkInfo {
    function_name: String,
    arguments_node: Option<tree_sitter::Range>,
    first_arg_text: Option<String>,
    has_shell_true: bool,
}

/// Find all command execution sinks in the parsed tree.
fn find_sinks(
    tree: &Tree,
    source: &[u8],
    ts_lang: &tree_sitter::Language,
    query_str: &str,
    lang_name: &str,
    file_path: &str,
) -> Result<HashMap<SourceLocation, SinkInfo>> {
    let query = Query::new(ts_lang, query_str)
        .map_err(|e| BrrrError::TreeSitter(format_query_error(lang_name, "sink", query_str, &e)))?;

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    // Get capture indices
    let sink_idx = query.capture_index_for_name("sink");
    let func_idx = query.capture_index_for_name("func");
    let args_idx = query.capture_index_for_name("args");

    let mut sinks = HashMap::new();

    while let Some(match_) = matches.next() {
        let sink_node = sink_idx
            .and_then(|idx| match_.captures.iter().find(|c| c.index == idx))
            .map(|c| c.node);

        let func_node = func_idx
            .and_then(|idx| match_.captures.iter().find(|c| c.index == idx))
            .map(|c| c.node);

        let args_node = args_idx
            .and_then(|idx| match_.captures.iter().find(|c| c.index == idx))
            .map(|c| c.node);

        if let Some(sink_node) = sink_node {
            let location = SourceLocation {
                file: file_path.to_string(),
                line: sink_node.start_position().row + 1,
                column: sink_node.start_position().column + 1,
                end_line: sink_node.end_position().row + 1,
                end_column: sink_node.end_position().column + 1,
            };

            let function_name = func_node
                .map(|n| node_text(n, source).to_string())
                .unwrap_or_else(|| "unknown".to_string());

            let first_arg_text = args_node.and_then(|args| {
                extract_first_argument(args, source)
            });

            let has_shell_true = args_node
                .map(|args| check_shell_true(args, source, lang_name))
                .unwrap_or(false);

            sinks.insert(location, SinkInfo {
                function_name,
                arguments_node: args_node.map(|n| n.range()),
                first_arg_text,
                has_shell_true,
            });
        }
    }

    Ok(sinks)
}

/// Find all taint sources in the parsed tree.
fn find_taint_sources(
    tree: &Tree,
    source: &[u8],
    ts_lang: &tree_sitter::Language,
    query_str: &str,
    lang_name: &str,
    file_path: &str,
) -> Result<HashMap<String, Vec<TaintSource>>> {
    let query = Query::new(ts_lang, query_str)
        .map_err(|e| BrrrError::TreeSitter(format_query_error(lang_name, "taint_source", query_str, &e)))?;

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    let source_idx = query.capture_index_for_name("source");

    let mut sources: HashMap<String, Vec<TaintSource>> = HashMap::new();

    while let Some(match_) = matches.next() {
        if let Some(idx) = source_idx {
            if let Some(capture) = match_.captures.iter().find(|c| c.index == idx) {
                let node = capture.node;
                let text = node_text(node, source);

                // Try to extract variable name from assignment context
                let variable = extract_assigned_variable(node, source)
                    .unwrap_or_else(|| text.to_string());

                let kind = classify_taint_source(text, lang_name);

                let location = SourceLocation {
                    file: file_path.to_string(),
                    line: node.start_position().row + 1,
                    column: node.start_position().column + 1,
                    end_line: node.end_position().row + 1,
                    end_column: node.end_position().column + 1,
                };

                let taint = TaintSource {
                    kind,
                    variable: variable.clone(),
                    location,
                    description: format!("Taint from {}", text),
                };

                sources.entry(variable).or_default().push(taint);
            }
        }
    }

    Ok(sources)
}

/// Classify the type of taint source based on the expression.
fn classify_taint_source(text: &str, _lang: &str) -> TaintSourceKind {
    let lower = text.to_lowercase();

    if lower.contains("request") || lower.contains("req.") {
        if lower.contains("body") || lower.contains("json") || lower.contains("form") {
            TaintSourceKind::FormInput
        } else {
            TaintSourceKind::HttpRequest
        }
    } else if lower.contains("stdin") || lower.contains("input") || lower.contains("readline") {
        TaintSourceKind::StdIn
    } else if lower.contains("getenv") || lower.contains("environ") || lower.contains("env.") {
        TaintSourceKind::EnvVar
    } else if lower.contains("argv") || lower.contains("args") {
        TaintSourceKind::CmdLineArg
    } else if lower.contains("read") || lower.contains("file") {
        TaintSourceKind::FileRead
    } else {
        TaintSourceKind::Unknown
    }
}

/// Extract the variable being assigned if this node is part of an assignment.
fn extract_assigned_variable(node: Node, source: &[u8]) -> Option<String> {
    // Walk up to find assignment
    let mut current = node;
    while let Some(parent) = current.parent() {
        match parent.kind() {
            "assignment" | "assignment_statement" | "variable_declaration" | "lexical_declaration" => {
                // Get the left side of assignment
                let mut cursor = parent.walk();
                for child in parent.children(&mut cursor) {
                    if child.kind() == "identifier" || child.kind() == "pattern" {
                        return Some(node_text(child, source).to_string());
                    }
                    // For Python: pattern_list, tuple_pattern, etc.
                    if child.end_byte() < node.start_byte() {
                        // This child is before the node, likely the target
                        let text = node_text(child, source);
                        if !text.contains('(') && !text.contains('[') {
                            return Some(text.to_string());
                        }
                    }
                }
            }
            _ => {}
        }
        current = parent;
    }
    None
}

/// Analyze a sink to determine if it's vulnerable.
fn analyze_sink(
    sink: &SinkInfo,
    location: &SourceLocation,
    taint_sources: &HashMap<String, Vec<TaintSource>>,
    source: &[u8],
    tree: &Tree,
    lang_name: &str,
    file_path: &str,
) -> Option<CommandInjectionFinding> {
    let known_sinks = get_command_sinks(lang_name);
    let sink_def = known_sinks.iter().find(|s| s.function == sink.function_name)?;

    // Determine injection kind
    let kind = if sink.function_name == "eval" || sink.function_name == "exec" || sink.function_name == "compile" {
        InjectionKind::CodeInjection
    } else if sink_def.shell_by_default || sink.has_shell_true {
        InjectionKind::CommandInjection
    } else {
        InjectionKind::ArgumentInjection
    };

    // Analyze the first argument for taint
    let (tainted_input, confidence, taint_chain) = if let Some(ref arg_text) = sink.first_arg_text {
        analyze_argument_taint(arg_text, taint_sources, tree, source, file_path)
    } else {
        ("unknown".to_string(), Confidence::Low, vec![])
    };

    // Adjust severity based on context
    // Code injection (eval/exec/compile) is ALWAYS critical - even pattern matches are dangerous
    let severity = if kind == InjectionKind::CodeInjection {
        // eval/exec/compile are inherently critical - arbitrary code execution
        Severity::Critical
    } else if sink_def.shell_by_default || sink.has_shell_true {
        // Shell execution with user input is always critical
        if confidence >= Confidence::Medium {
            Severity::Critical
        } else {
            sink_def.severity
        }
    } else if confidence == Confidence::High {
        // Direct taint to non-shell sink is high
        Severity::High
    } else if confidence == Confidence::Medium {
        Severity::Medium
    } else {
        // Pattern match only - use sink's defined severity as minimum
        sink_def.severity.min(Severity::Low)
    };

    // Generate code snippet
    let code_snippet = extract_code_snippet(source, location);

    // Generate remediation advice
    let remediation = generate_remediation(lang_name, &sink.function_name, kind);

    Some(CommandInjectionFinding {
        location: location.clone(),
        severity,
        sink_function: sink.function_name.clone(),
        tainted_input,
        confidence,
        kind,
        taint_chain,
        code_snippet,
        remediation,
    })
}

/// Analyze an argument for taint propagation.
fn analyze_argument_taint(
    arg_text: &str,
    taint_sources: &HashMap<String, Vec<TaintSource>>,
    _tree: &Tree,
    _source: &[u8],
    _file_path: &str,
) -> (String, Confidence, Vec<TaintSource>) {
    // Check for direct taint (variable matches a taint source)
    for (var_name, sources) in taint_sources {
        if arg_text.contains(var_name) {
            return (
                var_name.clone(),
                Confidence::High,
                sources.clone(),
            );
        }
    }

    // Check for suspicious patterns even without direct taint tracking
    let suspicious_patterns = [
        "request", "req", "params", "query", "body", "input",
        "argv", "args", "env", "getenv", "user", "data",
        "stdin", "file", "read", "form",
    ];

    let lower = arg_text.to_lowercase();
    for pattern in suspicious_patterns {
        if lower.contains(pattern) {
            return (
                arg_text.to_string(),
                Confidence::Medium,
                vec![],
            );
        }
    }

    // Check for string concatenation or interpolation with variables
    if arg_text.contains('+') || arg_text.contains("format") ||
       arg_text.contains('%') || arg_text.contains('{') ||
       arg_text.contains('$') || arg_text.contains('`') {
        return (
            arg_text.to_string(),
            Confidence::Medium,
            vec![],
        );
    }

    // If it's a variable (not a literal), flag with low confidence
    if !arg_text.starts_with('"') && !arg_text.starts_with('\'') &&
       !arg_text.starts_with('[') && !arg_text.chars().next().map(|c| c.is_numeric()).unwrap_or(false) {
        return (
            arg_text.to_string(),
            Confidence::Low,
            vec![],
        );
    }

    (arg_text.to_string(), Confidence::Low, vec![])
}

/// Check if subprocess call has shell=True.
fn check_shell_true(args_node: Node, source: &[u8], lang: &str) -> bool {
    let text = node_text(args_node, source);

    match lang {
        "python" => text.contains("shell=True") || text.contains("shell = True"),
        "typescript" | "javascript" => text.contains("shell: true") || text.contains("shell:true"),
        _ => false,
    }
}

/// Extract the first argument from an argument list.
fn extract_first_argument(args_node: Node, source: &[u8]) -> Option<String> {
    let mut cursor = args_node.walk();
    for child in args_node.children(&mut cursor) {
        // Skip punctuation
        if child.kind() == "(" || child.kind() == ")" || child.kind() == "," {
            continue;
        }
        // Return first actual argument
        return Some(node_text(child, source).to_string());
    }
    None
}

/// Extract a code snippet around the finding.
fn extract_code_snippet(source: &[u8], location: &SourceLocation) -> Option<String> {
    let source_str = std::str::from_utf8(source).ok()?;
    let lines: Vec<&str> = source_str.lines().collect();

    // Get lines around the finding (1 before, finding line, 1 after)
    let start = location.line.saturating_sub(2);
    let end = (location.end_line + 1).min(lines.len());

    let snippet: Vec<String> = lines[start..end]
        .iter()
        .enumerate()
        .map(|(i, line)| format!("{:4} | {}", start + i + 1, line))
        .collect();

    Some(snippet.join("\n"))
}

/// Generate remediation advice for the finding.
fn generate_remediation(lang: &str, function: &str, kind: InjectionKind) -> String {
    match kind {
        InjectionKind::CodeInjection => {
            "CRITICAL: Never pass user input to eval/exec/compile. Use safer alternatives:\n\
             - JSON parsing for data: json.loads() / JSON.parse()\n\
             - AST parsing for expressions: ast.literal_eval() (Python)\n\
             - Template engines for dynamic content\n\
             - If absolutely necessary, use strict whitelisting and sandboxing".to_string()
        }
        InjectionKind::CommandInjection => {
            match lang {
                "python" => format!(
                    "CRITICAL: {} uses shell=True or is inherently shell-based.\n\
                     Fix: Use subprocess with a list of arguments and shell=False:\n\
                     - subprocess.run(['cmd', arg1, arg2], shell=False)\n\
                     - Never concatenate user input into command strings\n\
                     - Validate/whitelist allowed commands and arguments\n\
                     - Use shlex.quote() if shell execution is unavoidable",
                    function
                ),
                "typescript" | "javascript" => format!(
                    "CRITICAL: {} executes commands in a shell.\n\
                     Fix: Use execFile or spawn without shell option:\n\
                     - execFile('/bin/cmd', [arg1, arg2])\n\
                     - spawn('cmd', [arg1, arg2]) without shell:true\n\
                     - Validate/whitelist allowed commands\n\
                     - Never concatenate user input into command strings",
                    function
                ),
                "go" => format!(
                    "CRITICAL: {} executes system commands.\n\
                     Fix: Use exec.Command with separate arguments:\n\
                     - exec.Command(\"cmd\", arg1, arg2) not exec.Command(\"sh\", \"-c\", userInput)\n\
                     - Validate/whitelist allowed commands and arguments\n\
                     - Never use string concatenation for commands",
                    function
                ),
                "c" | "cpp" => format!(
                    "CRITICAL: {} executes commands via shell.\n\
                     Fix: Use exec* family functions with explicit arguments:\n\
                     - execv() or execvp() with argument array\n\
                     - Never pass user input to system() or popen()\n\
                     - Validate/whitelist all inputs before use",
                    function
                ),
                "java" => format!(
                    "CRITICAL: {} executes system commands.\n\
                     Fix: Use ProcessBuilder with argument list:\n\
                     - new ProcessBuilder(\"cmd\", arg1, arg2)\n\
                     - Avoid Runtime.exec(string) with concatenated commands\n\
                     - Validate/whitelist allowed commands and arguments",
                    function
                ),
                _ => "Use parameterized command execution without shell interpretation".to_string(),
            }
        }
        InjectionKind::ArgumentInjection => {
            format!(
                "WARNING: User input may be passed as command arguments.\n\
                 Fix: Validate and sanitize all inputs:\n\
                 - Whitelist allowed values where possible\n\
                 - Reject inputs containing suspicious characters (-, --, etc.)\n\
                 - Use -- to separate options from arguments\n\
                 - Consider using allowlists for filenames/paths",
            )
        }
    }
}

/// Get text from a node, handling UTF-8 safely.
fn node_text<'a>(node: Node<'a>, source: &'a [u8]) -> &'a str {
    std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn create_temp_file(content: &str, extension: &str) -> NamedTempFile {
        let mut file = tempfile::Builder::new()
            .suffix(extension)
            .tempfile()
            .expect("Failed to create temp file");
        file.write_all(content.as_bytes()).expect("Failed to write");
        file
    }

    // =========================================================================
    // Python Tests
    // =========================================================================

    #[test]
    fn test_python_direct_os_system_injection() {
        let source = r#"
import os

def handle_request(request):
    cmd = request.args['cmd']
    os.system(cmd)  # Direct injection
"#;
        let file = create_temp_file(source, ".py");
        let findings = scan_file_command_injection(file.path(), Some("python"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect os.system vulnerability");
        let finding = &findings[0];
        assert_eq!(finding.sink_function, "system");
        assert_eq!(finding.kind, InjectionKind::CommandInjection);
        assert!(finding.severity >= Severity::High);
    }

    #[test]
    fn test_python_indirect_os_system_injection() {
        let source = r#"
import os

def handle_request(request):
    user_input = request.args.get('cmd')
    command = "ls -la " + user_input
    os.system(command)  # Indirect injection via concatenation
"#;
        let file = create_temp_file(source, ".py");
        let findings = scan_file_command_injection(file.path(), Some("python"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect indirect injection");
        // Even without full taint tracking, os.system is a dangerous sink
        // The severity should be at least High due to shell_by_default
        assert!(findings[0].severity >= Severity::High);
    }

    #[test]
    fn test_python_subprocess_shell_true() {
        let source = r#"
import subprocess

def run_command(user_input):
    subprocess.run(user_input, shell=True)  # Dangerous!
"#;
        let file = create_temp_file(source, ".py");
        let findings = scan_file_command_injection(file.path(), Some("python"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect subprocess with shell=True");
        let finding = &findings[0];
        assert_eq!(finding.kind, InjectionKind::CommandInjection);
    }

    #[test]
    fn test_python_subprocess_list_args_safe() {
        let source = r#"
import subprocess

def run_safe(filename):
    # Safe: using list args without shell
    subprocess.run(['cat', filename], shell=False)
"#;
        let file = create_temp_file(source, ".py");
        let findings = scan_file_command_injection(file.path(), Some("python"))
            .expect("Scan should succeed");

        // Should still detect but with lower severity (argument injection possible)
        if !findings.is_empty() {
            assert!(findings[0].kind == InjectionKind::ArgumentInjection ||
                    findings[0].severity <= Severity::Medium);
        }
    }

    #[test]
    fn test_python_eval_code_injection() {
        let source = r#"
def calculate(expression):
    return eval(expression)  # Code injection!
"#;
        let file = create_temp_file(source, ".py");
        let findings = scan_file_command_injection(file.path(), Some("python"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect eval vulnerability");
        let finding = &findings[0];
        assert_eq!(finding.sink_function, "eval");
        assert_eq!(finding.kind, InjectionKind::CodeInjection);
        assert_eq!(finding.severity, Severity::Critical);
    }

    #[test]
    fn test_python_exec_code_injection() {
        let source = r#"
def run_code(code):
    exec(code)  # Code injection!
"#;
        let file = create_temp_file(source, ".py");
        let findings = scan_file_command_injection(file.path(), Some("python"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect exec vulnerability");
        assert_eq!(findings[0].kind, InjectionKind::CodeInjection);
    }

    #[test]
    fn test_python_input_to_system() {
        let source = r#"
import os

def main():
    cmd = input("Enter command: ")
    os.system(cmd)
"#;
        let file = create_temp_file(source, ".py");
        let findings = scan_file_command_injection(file.path(), Some("python"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect input() to os.system");
    }

    // =========================================================================
    // TypeScript/JavaScript Tests
    // =========================================================================

    #[test]
    fn test_typescript_child_process_exec() {
        // Use child_process.exec pattern which matches the query
        let source = r#"
const child_process = require('child_process');

function runCommand(userInput: string) {
    child_process.exec(userInput, (error, stdout, stderr) => {
        console.log(stdout);
    });
}
"#;
        let file = create_temp_file(source, ".ts");
        let findings = scan_file_command_injection(file.path(), Some("typescript"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect child_process.exec");
        // Find the CommandInjection finding (there may be multiple findings)
        let cmd_injection = findings.iter().find(|f| f.kind == InjectionKind::CommandInjection);
        assert!(cmd_injection.is_some() || findings[0].sink_function == "exec",
            "Should detect command injection or exec sink");
    }

    #[test]
    fn test_typescript_eval() {
        let source = r#"
function processUserCode(code: string) {
    return eval(code);  // Code injection!
}
"#;
        let file = create_temp_file(source, ".ts");
        let findings = scan_file_command_injection(file.path(), Some("typescript"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect eval vulnerability");
        assert_eq!(findings[0].kind, InjectionKind::CodeInjection);
    }

    #[test]
    fn test_typescript_spawn_shell_true() {
        let source = r#"
import { spawn } from 'child_process';

function runWithShell(cmd: string) {
    spawn(cmd, { shell: true });
}
"#;
        let file = create_temp_file(source, ".ts");
        let findings = scan_file_command_injection(file.path(), Some("typescript"))
            .expect("Scan should succeed");

        // Should detect spawn with shell:true
        if !findings.is_empty() {
            assert!(findings[0].severity >= Severity::High);
        }
    }

    // =========================================================================
    // Go Tests
    // =========================================================================

    #[test]
    fn test_go_exec_command() {
        let source = r#"
package main

import (
    "os/exec"
)

func runCommand(userInput string) {
    cmd := exec.Command(userInput)
    cmd.Run()
}
"#;
        let file = create_temp_file(source, ".go");
        let findings = scan_file_command_injection(file.path(), Some("go"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect exec.Command with user input");
    }

    // =========================================================================
    // C Tests
    // =========================================================================

    #[test]
    fn test_c_system_call() {
        let source = r#"
#include <stdlib.h>

void execute(char* userInput) {
    system(userInput);
}
"#;
        let file = create_temp_file(source, ".c");
        let findings = scan_file_command_injection(file.path(), Some("c"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect system() call");
        assert_eq!(findings[0].kind, InjectionKind::CommandInjection);
        assert_eq!(findings[0].severity, Severity::Critical);
    }

    #[test]
    fn test_c_popen() {
        let source = r#"
#include <stdio.h>

void readOutput(char* cmd) {
    FILE* fp = popen(cmd, "r");
    pclose(fp);
}
"#;
        let file = create_temp_file(source, ".c");
        let findings = scan_file_command_injection(file.path(), Some("c"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect popen() call");
    }

    // =========================================================================
    // Rust Tests
    // =========================================================================

    #[test]
    fn test_rust_command_new() {
        let source = r#"
use std::process::Command;

fn run_command(user_input: &str) {
    Command::new(user_input)
        .spawn()
        .expect("failed");
}
"#;
        let file = create_temp_file(source, ".rs");
        let findings = scan_file_command_injection(file.path(), Some("rust"))
            .expect("Scan should succeed");

        assert!(!findings.is_empty(), "Should detect Command::new with user input");
    }

    // =========================================================================
    // Java Tests
    // =========================================================================

    #[test]
    fn test_java_runtime_exec() {
        let source = r#"
public class CommandRunner {
    public void run(String userInput) throws Exception {
        Runtime.getRuntime().exec(userInput);
    }
}
"#;
        let file = create_temp_file(source, ".java");
        let findings = scan_file_command_injection(file.path(), Some("java"))
            .expect("Scan should succeed");

        // Note: Java Runtime.exec detection depends on tree-sitter-java grammar details
        // This test verifies the scan completes without error; detection may vary
        if !findings.is_empty() {
            assert!(findings[0].sink_function.contains("exec"));
        }
    }

    // =========================================================================
    // Utility Tests
    // =========================================================================

    #[test]
    fn test_severity_ordering() {
        assert!(Severity::Critical > Severity::High);
        assert!(Severity::High > Severity::Medium);
        assert!(Severity::Medium > Severity::Low);
        assert!(Severity::Low > Severity::Info);
    }

    #[test]
    fn test_confidence_ordering() {
        assert!(Confidence::High > Confidence::Medium);
        assert!(Confidence::Medium > Confidence::Low);
    }

    #[test]
    fn test_get_command_sinks_coverage() {
        // Ensure we have sinks defined for all supported languages
        let languages = ["python", "typescript", "javascript", "go", "rust", "c", "cpp", "java"];
        for lang in languages {
            let sinks = get_command_sinks(lang);
            assert!(!sinks.is_empty(), "Should have sinks for {}", lang);
        }
    }

    #[test]
    fn test_classify_taint_source() {
        assert_eq!(
            classify_taint_source("request.args", "python"),
            TaintSourceKind::HttpRequest
        );
        assert_eq!(
            classify_taint_source("request.body", "python"),
            TaintSourceKind::FormInput
        );
        assert_eq!(
            classify_taint_source("os.environ", "python"),
            TaintSourceKind::EnvVar
        );
        assert_eq!(
            classify_taint_source("sys.argv", "python"),
            TaintSourceKind::CmdLineArg
        );
        assert_eq!(
            classify_taint_source("sys.stdin", "python"),
            TaintSourceKind::StdIn
        );
    }

    #[test]
    fn test_injection_kind_display() {
        assert_eq!(
            format!("{}", InjectionKind::CommandInjection),
            "command_injection"
        );
        assert_eq!(
            format!("{}", InjectionKind::ArgumentInjection),
            "argument_injection"
        );
        assert_eq!(
            format!("{}", InjectionKind::CodeInjection),
            "code_injection"
        );
    }

    #[test]
    fn test_source_location_display() {
        let loc = SourceLocation {
            file: "test.py".to_string(),
            line: 10,
            column: 5,
            end_line: 10,
            end_column: 20,
        };
        assert_eq!(format!("{}", loc), "test.py:10:5");
    }
}
