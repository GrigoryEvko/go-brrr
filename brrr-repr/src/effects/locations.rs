//! Abstract locations and identifiers for parameterized effects
//!
//! Mirrors F* Effects.fsti: abstract_loc, lock_id, chan_id, io_source, io_sink

use lasso::Spur;
use serde::{Deserialize, Serialize};

/// Lock identifier for concurrency effects
pub type LockId = u32;

/// Channel identifier for session effects
pub type ChanId = u32;

/// Abstract location for parameterized memory effects.
/// Supports both concrete allocation sites and symbolic/polymorphic locations.
///
/// Maps to F*:
/// ```fstar
/// type abstract_loc =
///   | LocConcrete : nat -> abstract_loc
///   | LocAbstract : string -> abstract_loc
///   | LocParam    : nat -> abstract_loc
///   | LocUnknown  : abstract_loc
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AbstractLoc {
    /// Concrete allocation site (e.g., from SSA numbering)
    Concrete(u32),
    /// Abstract/symbolic location (named region)
    Abstract(Spur),
    /// Parameter location for polymorphism (de Bruijn index)
    Param(u32),
    /// Unknown/any location - aliases all locations (conservative)
    Unknown,
}

impl AbstractLoc {
    /// Check if this location may alias another.
    /// Unknown aliases everything; Param locations are conservative.
    pub fn may_alias(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unknown, _) | (_, Self::Unknown) => true,
            (Self::Param(_), _) | (_, Self::Param(_)) => true,
            (Self::Concrete(a), Self::Concrete(b)) => a == b,
            (Self::Abstract(a), Self::Abstract(b)) => a == b,
            _ => false,
        }
    }

    /// Check if this is a concrete location
    pub const fn is_concrete(&self) -> bool {
        matches!(self, Self::Concrete(_))
    }

    /// Check if this is the unknown location
    pub const fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }

    /// Get discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Concrete(_) => 0,
            Self::Abstract(_) => 1,
            Self::Param(_) => 2,
            Self::Unknown => 3,
        }
    }
}

impl Default for AbstractLoc {
    fn default() -> Self {
        Self::Unknown
    }
}

/// I/O source types for parameterized input effects
///
/// Maps to F*:
/// ```fstar
/// type io_source =
///   | IOStdin      : io_source
///   | IOEnvVar     : string -> io_source
///   | IOFileInput  : string -> io_source
///   | IONetworkIn  : io_source
///   | IOUserInput  : io_source
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum IoSource {
    /// Standard input
    Stdin,
    /// Environment variable read
    EnvVar(Spur),
    /// File input (path)
    FileInput(Spur),
    /// Network input
    NetworkIn,
    /// Interactive user input
    UserInput,
    /// Command line arguments
    Args,
    /// Random number generator
    Random,
    /// System clock/time
    Clock,
}

impl IoSource {
    /// Get discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Stdin => 0,
            Self::EnvVar(_) => 1,
            Self::FileInput(_) => 2,
            Self::NetworkIn => 3,
            Self::UserInput => 4,
            Self::Args => 5,
            Self::Random => 6,
            Self::Clock => 7,
        }
    }

    /// Format as symbol for .brrrx output
    pub fn as_symbol(&self) -> String {
        match self {
            Self::Stdin => "stdin".to_string(),
            Self::EnvVar(_) => "env".to_string(),
            Self::FileInput(_) => "file".to_string(),
            Self::NetworkIn => "net".to_string(),
            Self::UserInput => "user".to_string(),
            Self::Args => "args".to_string(),
            Self::Random => "random".to_string(),
            Self::Clock => "clock".to_string(),
        }
    }
}

/// I/O sink types for parameterized output effects
///
/// Maps to F*:
/// ```fstar
/// type io_sink =
///   | IOStdout     : io_sink
///   | IOStderr     : io_sink
///   | IOFileOutput : string -> io_sink
///   | IONetworkOut : io_sink
///   | IODatabase   : string -> io_sink
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum IoSink {
    /// Standard output
    Stdout,
    /// Standard error
    Stderr,
    /// File output (path)
    FileOutput(Spur),
    /// Network output
    NetworkOut,
    /// Database write (connection name)
    Database(Spur),
    /// Log output
    Log,
    /// Metrics/telemetry
    Metrics,
}

impl IoSink {
    /// Get discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Stdout => 0,
            Self::Stderr => 1,
            Self::FileOutput(_) => 2,
            Self::NetworkOut => 3,
            Self::Database(_) => 4,
            Self::Log => 5,
            Self::Metrics => 6,
        }
    }

    /// Format as symbol for .brrrx output
    pub fn as_symbol(&self) -> String {
        match self {
            Self::Stdout => "stdout".to_string(),
            Self::Stderr => "stderr".to_string(),
            Self::FileOutput(_) => "file".to_string(),
            Self::NetworkOut => "net".to_string(),
            Self::Database(_) => "db".to_string(),
            Self::Log => "log".to_string(),
            Self::Metrics => "metrics".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abstract_loc_aliasing() {
        let loc1 = AbstractLoc::Concrete(1);
        let loc2 = AbstractLoc::Concrete(2);
        let loc3 = AbstractLoc::Concrete(1);

        assert!(!loc1.may_alias(&loc2));
        assert!(loc1.may_alias(&loc3));
        assert!(loc1.may_alias(&AbstractLoc::Unknown));
        assert!(loc1.may_alias(&AbstractLoc::Param(0)));
    }

    #[test]
    fn test_io_source_discriminants() {
        assert_eq!(IoSource::Stdin.discriminant(), 0);
        assert_eq!(IoSource::NetworkIn.discriminant(), 3);
    }

    #[test]
    fn test_io_sink_discriminants() {
        assert_eq!(IoSink::Stdout.discriminant(), 0);
        assert_eq!(IoSink::Stderr.discriminant(), 1);
    }
}
