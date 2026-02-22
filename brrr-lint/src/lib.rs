//! F* Language Server Protocol library.
//!
//! This crate provides a complete LSP implementation for F*.

#![recursion_limit = "256"]

pub mod cli;
pub mod config;
pub mod connection;
pub mod document;
pub mod error;
pub mod lint;
pub mod lint_config;
pub mod protocol;
pub mod server;

pub use cli::{Cli, Commands, SeverityFilter, validate_cli_semantics};
pub use config::{FstarConfig, LspSettings};
pub use error::{FstarError, LintError, ParseError, Result, exit_code};
pub use lint::{LintConfig, LintEngine, OutputFormat};
pub use lint_config::{
    LintFileConfig, ConfigError, FileMatcher,
    discover_config, discover_and_load_config, CONFIG_FILE_NAME,
};
pub use server::FstarServer;
