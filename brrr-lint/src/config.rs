//! Configuration handling for the F* LSP server.

use crate::error::{FstarError, Result};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use tokio::fs;
use tokio::time::{timeout, Duration};
use tracing::{debug, warn};

/// F* project configuration, typically from `.fst.config.json`.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FstarConfig {
    #[serde(default)]
    pub include_dirs: Vec<String>,

    #[serde(default)]
    pub options: Vec<String>,

    #[serde(default)]
    pub fstar_exe: Option<String>,

    #[serde(default)]
    pub cwd: Option<String>,
}

/// LSP server settings.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LspSettings {
    #[serde(default)]
    pub verify_on_open: bool,

    #[serde(default = "default_true")]
    pub verify_on_save: bool,

    #[serde(default = "default_true")]
    pub fly_check: bool,

    #[serde(default)]
    pub debug: bool,

    #[serde(default = "default_timeout")]
    pub timeout_ms: u64,

    #[serde(default = "default_max_processes")]
    pub max_processes: usize,

    /// CLI override for F* executable path.
    #[serde(default)]
    pub fstar_exe: Option<String>,
}

fn default_true() -> bool {
    true
}

fn default_timeout() -> u64 {
    30_000
}

fn default_max_processes() -> usize {
    4
}

impl Default for LspSettings {
    fn default() -> Self {
        Self {
            verify_on_open: false,
            verify_on_save: true,
            fly_check: true,
            debug: false,
            timeout_ms: default_timeout(),
            max_processes: default_max_processes(),
            fstar_exe: None,
        }
    }
}

impl FstarConfig {
    /// Find and load config file by searching up the directory tree.
    /// Stops at workspace folder boundaries to avoid using unrelated configs.
    /// Falls back to `make <file>-in` if no config file is found.
    pub async fn find_and_load(
        file_path: &Path,
        workspace_folders: &[PathBuf],
    ) -> Result<Option<(Self, PathBuf)>> {
        let mut current = file_path.parent();

        while let Some(dir) = current {
            // Stop if we've left all workspace folders
            if !workspace_folders.is_empty()
                && !workspace_folders.iter().any(|ws| dir.starts_with(ws))
            {
                break;
            }

            let config_path = dir.join(".fst.config.json");
            if config_path.exists() {
                debug!("Found config file: {}", config_path.display());
                let config = Self::load(&config_path).await?;
                return Ok(Some((config, config_path)));
            }
            current = dir.parent();
        }

        // Fallback: try to get config from Makefile
        if let Some(args) = try_make_config(file_path).await {
            debug!("Using Makefile-derived config for {}", file_path.display());
            let config = Self::from_make_args(&args);
            return Ok(Some((config, file_path.to_path_buf())));
        }

        Ok(None)
    }

    /// Parse config from `make <file>-in` output args.
    /// Extracts `--include` paths and passes remaining args as options.
    fn from_make_args(args: &[String]) -> Self {
        let mut include_dirs = Vec::new();
        let mut options = Vec::new();
        let mut iter = args.iter();

        while let Some(arg) = iter.next() {
            if arg == "--include" {
                if let Some(dir) = iter.next() {
                    include_dirs.push(dir.clone());
                }
            } else {
                options.push(arg.clone());
            }
        }

        Self {
            include_dirs,
            options,
            fstar_exe: None,
            cwd: None,
        }
    }

    /// Load config from a specific file.
    pub async fn load(path: &Path) -> Result<Self> {
        let contents = fs::read_to_string(path).await?;
        let mut config: FstarConfig = serde_json::from_str(&contents)?;
        config.expand_env_vars();
        Ok(config)
    }

    /// Expand environment variables in config values.
    /// Supports `${VAR}` and `$VAR` syntax. Use `$$` for a literal `$`.
    /// Warns on unresolved variables.
    fn expand_env_vars(&mut self) {
        fn expand(s: &str) -> String {
            let mut result = String::with_capacity(s.len());
            let mut chars = s.chars().peekable();

            while let Some(c) = chars.next() {
                if c == '$' {
                    // Handle $$ as escaped literal $
                    if chars.peek() == Some(&'$') {
                        chars.next(); // consume second $
                        result.push('$');
                        continue;
                    }

                    let braced = chars.peek() == Some(&'{');
                    if braced {
                        chars.next(); // consume '{'
                    }

                    let mut var_name = String::new();
                    while let Some(&nc) = chars.peek() {
                        if braced {
                            if nc == '}' {
                                chars.next();
                                break;
                            }
                        } else if !nc.is_alphanumeric() && nc != '_' {
                            break;
                        }
                        var_name.push(nc);
                        chars.next();
                    }

                    if var_name.is_empty() {
                        result.push('$');
                        if braced {
                            result.push('{');
                            result.push('}');
                        }
                    } else {
                        match std::env::var(&var_name) {
                            Ok(val) => result.push_str(&val),
                            Err(_) => {
                                warn!("Unresolved environment variable '{}' in config", var_name);
                                // Preserve the original reference so the user sees it
                                if braced {
                                    result.push_str(&format!("${{{}}}", var_name));
                                } else {
                                    result.push_str(&format!("${}", var_name));
                                }
                            }
                        }
                    }
                } else {
                    result.push(c);
                }
            }
            result
        }

        self.include_dirs = self.include_dirs.iter().map(|s| expand(s)).collect();
        self.options = self.options.iter().map(|s| expand(s)).collect();
        self.fstar_exe = self.fstar_exe.as_ref().map(|s| expand(s));
        self.cwd = self.cwd.as_ref().map(|s| expand(s));
    }

    /// Build command-line arguments for F*.
    pub fn build_args(&self, lax: bool) -> Vec<String> {
        let mut args = vec!["--ide".to_string()];

        for dir in &self.include_dirs {
            args.push("--include".to_string());
            args.push(dir.clone());
        }

        args.extend(self.options.clone());

        if lax {
            args.push("--admit_smt_queries".to_string());
            args.push("true".to_string());
        }

        args
    }

    /// Resolve the F* executable path.
    pub fn resolve_fstar_exe(&self) -> Result<PathBuf> {
        let exe = self.fstar_exe.as_deref().unwrap_or("fstar.exe");

        // Try to find in PATH
        match which::which(exe) {
            Ok(path) => Ok(path),
            Err(_) => {
                // Try common locations
                let home = std::env::var("HOME").unwrap_or_default();
                let candidates: Vec<PathBuf> = vec![
                    PathBuf::from(exe),
                    PathBuf::from("/usr/bin/fstar.exe"),
                    PathBuf::from("/usr/local/bin/fstar.exe"),
                    PathBuf::from(format!("{}/.opam/default/bin/fstar.exe", home)),
                ];

                for candidate in candidates {
                    if candidate.exists() {
                        return Ok(candidate);
                    }
                }

                Err(FstarError::FstarNotFound(exe.to_string()))
            }
        }
    }

    /// Get working directory.
    pub fn get_cwd(&self, file_path: &Path) -> PathBuf {
        self.cwd
            .as_ref()
            .map(PathBuf::from)
            .unwrap_or_else(|| file_path.parent().unwrap_or(Path::new(".")).to_path_buf())
    }
}

/// Try to get config from `make <file>-in` output (fallback).
/// Used when no `.fst.config.json` is found in the directory tree.
pub async fn try_make_config(file_path: &Path) -> Option<Vec<String>> {
    let file_name = file_path.file_name()?.to_str()?;
    let target = format!("{}-in", file_name);
    let dir = file_path.parent()?;

    let output = timeout(
        Duration::from_secs(10),
        tokio::process::Command::new("make")
            .arg(&target)
            .current_dir(dir)
            .output(),
    )
    .await
    .ok()? // Timeout elapsed
    .ok()?; // Command failed

    if output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let args: Vec<String> = stdout.split_whitespace().map(String::from).collect();
        if !args.is_empty() {
            debug!("Got config from make: {:?}", args);
            return Some(args);
        }
    }

    None
}
