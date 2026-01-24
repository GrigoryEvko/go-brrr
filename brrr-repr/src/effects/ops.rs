//! Effect operations and effect types
//!
//! Mirrors F* Effects.fsti: effect_op (50+ variants), effect_type

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::locations::{AbstractLoc, ChanId, IoSink, IoSource, LockId};

/// Simple type representation for effect parameters.
/// Forward reference to avoid circular dependency with BrrrType.
///
/// Maps to F*:
/// ```fstar
/// type effect_type =
///   | ETUnit   : effect_type
///   | ETBool   : effect_type
///   | ETInt    : effect_type
///   | ETString : effect_type
///   | ETChan   : effect_type -> effect_type
///   | ETRef    : effect_type -> effect_type
///   | ETFn     : effect_type -> effect_type -> effect_type
///   | ETVar    : nat -> effect_type
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EffectType {
    /// Unit type
    Unit,
    /// Boolean type
    Bool,
    /// Integer type
    Int,
    /// String type
    String,
    /// Channel type `Chan<T>`
    Chan(Box<EffectType>),
    /// Reference type `Ref<T>`
    Ref(Box<EffectType>),
    /// Function type `A -> B`
    Fn(Box<EffectType>, Box<EffectType>),
    /// Type variable (de Bruijn index)
    Var(u32),
    /// Named type reference
    Named(Spur),
}

impl EffectType {
    /// Unit type constant
    pub const UNIT: Self = Self::Unit;

    /// Bool type constant
    pub const BOOL: Self = Self::Bool;

    /// Int type constant
    pub const INT: Self = Self::Int;

    /// String type constant
    pub const STRING: Self = Self::String;

    /// Create a channel type
    pub fn chan(elem: Self) -> Self {
        Self::Chan(Box::new(elem))
    }

    /// Create a reference type
    pub fn ref_type(elem: Self) -> Self {
        Self::Ref(Box::new(elem))
    }

    /// Create a function type
    pub fn func(arg: Self, ret: Self) -> Self {
        Self::Fn(Box::new(arg), Box::new(ret))
    }

    /// Get discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Unit => 0,
            Self::Bool => 1,
            Self::Int => 2,
            Self::String => 3,
            Self::Chan(_) => 4,
            Self::Ref(_) => 5,
            Self::Fn(_, _) => 6,
            Self::Var(_) => 7,
            Self::Named(_) => 8,
        }
    }
}

impl Default for EffectType {
    fn default() -> Self {
        Self::Unit
    }
}

/// Resource type identifier for acquire/release effects
pub type ResourceType = Spur;

/// Individual effect operations with parameters.
/// Based on F* Effects.fsti effect_op (50+ variants).
///
/// Effects are organized into categories:
/// - Memory effects (location-parameterized)
/// - Control effects (exceptions, async, continuations)
/// - I/O effects (source/sink-parameterized)
/// - Concurrency effects (lock-parameterized)
/// - Session effects (channel-parameterized, Honda 1998/2008)
/// - Resource effects (acquire/release)
/// - State effects (STRef-style)
/// - FFI effects
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EffectOp {
    // ========== Memory Effects (0-9) ==========
    /// Read from location `ERead(loc)`
    Read(AbstractLoc),
    /// Write to location `EWrite(loc)`
    Write(AbstractLoc),
    /// Allocate memory `EAlloc`
    Alloc,
    /// Free memory at location `EFree(loc)`
    Free(AbstractLoc),
    /// Memory read (unparameterized, legacy)
    ReadSimple,
    /// Memory write (unparameterized, legacy)
    WriteSimple,

    // ========== Control Effects (10-19) ==========
    /// Throw exception of type `EThrow(exn_type)`
    Throw(Spur),
    /// Catch exception of type `ECatch(exn_type)`
    Catch(Spur),
    /// Panic/abort `EPanic`
    Panic,
    /// Async operation `EAsync`
    Async,
    /// Yield with type `EYield(yield_type, resume_type)`
    Yield(EffectType, EffectType),
    /// Divergence/non-termination `EDiv`
    Div,
    /// Shift (delimited continuation) `EShift`
    Shift,
    /// Abort execution `EAbort`
    Abort,

    // ========== I/O Effects (20-34) ==========
    /// Input from source `EInput(source)`
    Input(IoSource),
    /// Output to sink `EOutput(sink)`
    Output(IoSink),
    /// General I/O `EIO`
    Io,
    /// Network I/O `ENet`
    Net,
    /// Filesystem I/O `EFS`
    Fs,
    /// File read at path `EFileRead(path)`
    FileRead(Spur),
    /// File write at path `EFileWrite(path)`
    FileWrite(Spur),
    /// Random number generation `ERandom`
    Random,
    /// Clock/time access `EClock`
    Clock,
    /// Console I/O `EConsole`
    Console,
    /// Environment variable access `EEnv`
    Env,

    // ========== Concurrency Effects (35-44) ==========
    /// Spawn thread/task `ESpawn`
    Spawn,
    /// Join thread/task `EJoin`
    Join,
    /// Acquire lock `ELock(lock_id)`
    Lock(LockId),
    /// Release lock `EUnlock(lock_id)`
    Unlock(LockId),
    /// Atomic operation `EAtomic`
    Atomic,
    /// Lock (unparameterized, legacy)
    LockSimple,
    /// Thread-local storage access
    ThreadLocal,
    /// Memory barrier
    Barrier,

    // ========== Session Effects (45-59) ==========
    /// Send on channel `ESend(chan, payload_type)`
    Send(ChanId, EffectType),
    /// Receive from channel `ERecv(chan, payload_type)`
    Recv(ChanId, EffectType),
    /// Select label on channel `ESelect(chan, label)`
    Select(ChanId, Spur),
    /// Branch on channel `EBranch(chan, labels)`
    Branch(ChanId, Vec<Spur>),
    /// Create channel `EChanCreate(chan, elem_type, buf_size)`
    ChanCreate(ChanId, EffectType, u32),
    /// Close channel `EChanClose(chan)`
    ChanClose(ChanId),
    /// Delegate channel `EDelegate(source_chan, target_chan)`
    Delegate(ChanId, ChanId),
    /// New channel (unparameterized, legacy) `ENewCh`
    NewCh,

    // ========== Resource Effects (60-64) ==========
    /// Acquire resource `EAcquire(resource_type)`
    Acquire(ResourceType),
    /// Release resource `ERelease(resource_type)`
    Release(ResourceType),
    /// Use resource `EUse(resource_type)`
    Use(ResourceType),

    // ========== State Effects (65-69) ==========
    /// General state `EState`
    State,
    /// ST read from ref `ESTRead(ref_id)`
    StRead(u32),
    /// ST write to ref `ESTWrite(ref_id)`
    StWrite(u32),
    /// ST create new ref `ESTNew`
    StNew,

    // ========== FFI Effects (70-74) ==========
    /// Unsafe operation `EUnsafe`
    Unsafe,
    /// Foreign function interface `EFFI`
    Ffi,
    /// C interop
    CInterop,
    /// Platform-specific operation
    Platform,
}

impl EffectOp {
    /// Get discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            // Memory effects (0-9)
            Self::Read(_) => 0,
            Self::Write(_) => 1,
            Self::Alloc => 2,
            Self::Free(_) => 3,
            Self::ReadSimple => 4,
            Self::WriteSimple => 5,

            // Control effects (10-19)
            Self::Throw(_) => 10,
            Self::Catch(_) => 11,
            Self::Panic => 12,
            Self::Async => 13,
            Self::Yield(_, _) => 14,
            Self::Div => 15,
            Self::Shift => 16,
            Self::Abort => 17,

            // I/O effects (20-34)
            Self::Input(_) => 20,
            Self::Output(_) => 21,
            Self::Io => 22,
            Self::Net => 23,
            Self::Fs => 24,
            Self::FileRead(_) => 25,
            Self::FileWrite(_) => 26,
            Self::Random => 27,
            Self::Clock => 28,
            Self::Console => 29,
            Self::Env => 30,

            // Concurrency effects (35-44)
            Self::Spawn => 35,
            Self::Join => 36,
            Self::Lock(_) => 37,
            Self::Unlock(_) => 38,
            Self::Atomic => 39,
            Self::LockSimple => 40,
            Self::ThreadLocal => 41,
            Self::Barrier => 42,

            // Session effects (45-59)
            Self::Send(_, _) => 45,
            Self::Recv(_, _) => 46,
            Self::Select(_, _) => 47,
            Self::Branch(_, _) => 48,
            Self::ChanCreate(_, _, _) => 49,
            Self::ChanClose(_) => 50,
            Self::Delegate(_, _) => 51,
            Self::NewCh => 52,

            // Resource effects (60-64)
            Self::Acquire(_) => 60,
            Self::Release(_) => 61,
            Self::Use(_) => 62,

            // State effects (65-69)
            Self::State => 65,
            Self::StRead(_) => 66,
            Self::StWrite(_) => 67,
            Self::StNew => 68,

            // FFI effects (70-74)
            Self::Unsafe => 70,
            Self::Ffi => 71,
            Self::CInterop => 72,
            Self::Platform => 73,
        }
    }

    /// Get the effect category name
    pub const fn category(&self) -> &'static str {
        match self.discriminant() {
            0..=9 => "memory",
            10..=19 => "control",
            20..=34 => "io",
            35..=44 => "concurrency",
            45..=59 => "session",
            60..=64 => "resource",
            65..=69 => "state",
            70..=74 => "ffi",
            _ => "unknown",
        }
    }

    /// Is this a memory effect?
    pub const fn is_memory(&self) -> bool {
        matches!(
            self,
            Self::Read(_)
                | Self::Write(_)
                | Self::Alloc
                | Self::Free(_)
                | Self::ReadSimple
                | Self::WriteSimple
        )
    }

    /// Is this an I/O effect?
    pub const fn is_io(&self) -> bool {
        matches!(self.discriminant(), 20..=34)
    }

    /// Is this a concurrency effect?
    pub const fn is_concurrency(&self) -> bool {
        matches!(self.discriminant(), 35..=59)
    }

    /// Is this a session/channel effect?
    pub const fn is_session(&self) -> bool {
        matches!(self.discriminant(), 45..=59)
    }

    /// Get the location if this is a location-parameterized effect
    pub fn location(&self) -> Option<&AbstractLoc> {
        match self {
            Self::Read(loc) | Self::Write(loc) | Self::Free(loc) => Some(loc),
            _ => None,
        }
    }

    /// Get the channel ID if this is a channel effect
    pub const fn channel(&self) -> Option<ChanId> {
        match self {
            Self::Send(ch, _)
            | Self::Recv(ch, _)
            | Self::Select(ch, _)
            | Self::Branch(ch, _)
            | Self::ChanCreate(ch, _, _)
            | Self::ChanClose(ch) => Some(*ch),
            Self::Delegate(src, _) => Some(*src),
            _ => None,
        }
    }

    /// Get the lock ID if this is a lock effect
    pub const fn lock(&self) -> Option<LockId> {
        match self {
            Self::Lock(id) | Self::Unlock(id) => Some(*id),
            _ => None,
        }
    }

    /// Check if two effects may commute (operate on disjoint resources)
    pub fn commutes_with(&self, other: &Self) -> bool {
        // Effects on different resources commute
        match (self, other) {
            // Same location effects don't commute
            (Self::Read(l1), Self::Write(l2))
            | (Self::Write(l1), Self::Read(l2))
            | (Self::Write(l1), Self::Write(l2)) => !l1.may_alias(l2),

            // Read-read commutes
            (Self::Read(_), Self::Read(_)) => true,

            // Same channel effects don't commute
            (Self::Send(c1, _), Self::Recv(c2, _))
            | (Self::Recv(c1, _), Self::Send(c2, _))
            | (Self::Send(c1, _), Self::Send(c2, _))
            | (Self::Recv(c1, _), Self::Recv(c2, _)) => c1 != c2,

            // Same lock effects don't commute
            (Self::Lock(l1), Self::Lock(l2))
            | (Self::Unlock(l1), Self::Unlock(l2))
            | (Self::Lock(l1), Self::Unlock(l2))
            | (Self::Unlock(l1), Self::Lock(l2)) => l1 != l2,

            // Different categories generally commute (conservative)
            _ => self.category() != other.category(),
        }
    }

    /// Format as UTF-8 symbol for .brrrx output
    pub fn as_symbol(&self) -> String {
        match self {
            Self::Read(loc) => format!("Read({:?})", loc),
            Self::Write(loc) => format!("Write({:?})", loc),
            Self::Alloc => "Alloc".to_string(),
            Self::Free(loc) => format!("Free({:?})", loc),
            Self::ReadSimple => "Read".to_string(),
            Self::WriteSimple => "Write".to_string(),
            Self::Throw(_) => "Throw".to_string(),
            Self::Catch(_) => "Catch".to_string(),
            Self::Panic => "Panic".to_string(),
            Self::Async => "Async".to_string(),
            Self::Yield(_, _) => "Yield".to_string(),
            Self::Div => "Div".to_string(),
            Self::Shift => "Shift".to_string(),
            Self::Abort => "Abort".to_string(),
            Self::Input(src) => format!("Input({})", src.as_symbol()),
            Self::Output(sink) => format!("Output({})", sink.as_symbol()),
            Self::Io => "IO".to_string(),
            Self::Net => "Net".to_string(),
            Self::Fs => "FS".to_string(),
            Self::FileRead(_) => "FileRead".to_string(),
            Self::FileWrite(_) => "FileWrite".to_string(),
            Self::Random => "Random".to_string(),
            Self::Clock => "Clock".to_string(),
            Self::Console => "Console".to_string(),
            Self::Env => "Env".to_string(),
            Self::Spawn => "Spawn".to_string(),
            Self::Join => "Join".to_string(),
            Self::Lock(id) => format!("Lock({})", id),
            Self::Unlock(id) => format!("Unlock({})", id),
            Self::Atomic => "Atomic".to_string(),
            Self::LockSimple => "Lock".to_string(),
            Self::ThreadLocal => "ThreadLocal".to_string(),
            Self::Barrier => "Barrier".to_string(),
            Self::Send(ch, _) => format!("Send({})", ch),
            Self::Recv(ch, _) => format!("Recv({})", ch),
            Self::Select(ch, _) => format!("Select({})", ch),
            Self::Branch(ch, _) => format!("Branch({})", ch),
            Self::ChanCreate(ch, _, _) => format!("ChanCreate({})", ch),
            Self::ChanClose(ch) => format!("ChanClose({})", ch),
            Self::Delegate(src, tgt) => format!("Delegate({} -> {})", src, tgt),
            Self::NewCh => "NewCh".to_string(),
            Self::Acquire(_) => "Acquire".to_string(),
            Self::Release(_) => "Release".to_string(),
            Self::Use(_) => "Use".to_string(),
            Self::State => "State".to_string(),
            Self::StRead(id) => format!("STRead({})", id),
            Self::StWrite(id) => format!("STWrite({})", id),
            Self::StNew => "STNew".to_string(),
            Self::Unsafe => "Unsafe".to_string(),
            Self::Ffi => "FFI".to_string(),
            Self::CInterop => "CInterop".to_string(),
            Self::Platform => "Platform".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_effect_type_discriminants() {
        assert_eq!(EffectType::Unit.discriminant(), 0);
        assert_eq!(EffectType::Bool.discriminant(), 1);
        assert_eq!(EffectType::chan(EffectType::Int).discriminant(), 4);
    }

    #[test]
    fn test_effect_op_categories() {
        assert_eq!(EffectOp::Read(AbstractLoc::Unknown).category(), "memory");
        assert_eq!(EffectOp::Panic.category(), "control");
        assert_eq!(EffectOp::Io.category(), "io");
        assert_eq!(EffectOp::Spawn.category(), "concurrency");
        assert_eq!(
            EffectOp::Send(0, EffectType::Unit).category(),
            "session"
        );
        assert_eq!(EffectOp::Unsafe.category(), "ffi");
    }

    #[test]
    fn test_effect_op_commutativity() {
        let loc1 = AbstractLoc::Concrete(1);
        let loc2 = AbstractLoc::Concrete(2);

        // Read-read commutes
        assert!(EffectOp::Read(loc1.clone()).commutes_with(&EffectOp::Read(loc2.clone())));
        assert!(EffectOp::Read(loc1.clone()).commutes_with(&EffectOp::Read(loc1.clone())));

        // Read-write on same location doesn't commute
        assert!(!EffectOp::Read(loc1.clone()).commutes_with(&EffectOp::Write(loc1.clone())));

        // Read-write on different locations commutes
        assert!(EffectOp::Read(loc1.clone()).commutes_with(&EffectOp::Write(loc2.clone())));
    }

    #[test]
    fn test_effect_op_location() {
        let loc = AbstractLoc::Concrete(42);
        assert_eq!(EffectOp::Read(loc.clone()).location(), Some(&loc));
        assert_eq!(EffectOp::Alloc.location(), None);
    }

    #[test]
    fn test_effect_op_channel() {
        assert_eq!(
            EffectOp::Send(5, EffectType::Int).channel(),
            Some(5)
        );
        assert_eq!(EffectOp::Alloc.channel(), None);
    }
}
