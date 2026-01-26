//! Free monad types for effect semantics
//!
//! Mirrors F* Effects.fst lines 833-856:
//! ```fstar
//! noeq type free (eff: effect_row) (a: Type) =
//!   | FreeReturn : value:a -> free eff a
//!   | FreeBind   : op:effect_op -> args:list value -> cont:(value -> free eff a) -> free eff a
//! ```
//!
//! Since Rust cannot directly encode GADTs or higher-kinded types, we use a
//! defunctionalized representation where continuations are identified by
//! indices into a separate table.
//!
//! # Architecture
//!
//! - `Value` - Runtime values for effect arguments and results
//! - `FreeOp` - A single effect operation with continuation reference
//! - `Free` - The free monad ADT: Return | Bind
//! - `FreeProgram` - Complete program with continuation table
//!
//! # Example Usage
//!
//! ```rust,ignore
//! let prog = FreeProgram::new()
//!     .perform(EffectOp::Io, vec![Value::string("hello")])
//!     .perform(EffectOp::Console, vec![])
//!     .return_value(Value::Unit);
//!
//! while let Some((op, args)) = prog.step() {
//!     // Handle the effect operation
//! }
//! ```

use serde::{Deserialize, Serialize};

use super::ops::EffectOp;
use super::row::EffectRow;

/// Continuation identifier for defunctionalized continuations.
///
/// In F*, the continuation is `value -> free eff a`. In Rust, we use
/// an index into the program's continuation table instead.
pub type ContId = u32;

/// Special continuation ID indicating no continuation (program terminates)
pub const CONT_NONE: ContId = u32::MAX;

/// Runtime values for effect arguments and results.
///
/// Mirrors F* value type used in effect operations.
/// Kept simple to avoid circular dependencies with full expression types.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Value {
    /// Unit value `()`
    Unit,
    /// Boolean value
    Bool(bool),
    /// Integer value (i64 for simplicity)
    Int(i64),
    /// String value
    String(String),
    /// Byte array (for I/O operations)
    Bytes(Vec<u8>),
    /// Reference/pointer (abstract location ID)
    Ref(u32),
    /// Channel reference
    Chan(u32),
    /// Tuple of values
    Tuple(Vec<Value>),
    /// Tagged variant (constructor index, payload)
    Variant(u32, Box<Value>),
    /// Closure reference (function ID, captured environment)
    Closure(u32, Vec<Value>),
}

impl Value {
    /// Unit value constant
    pub const UNIT: Self = Self::Unit;

    /// Create a boolean value
    pub const fn bool(v: bool) -> Self {
        Self::Bool(v)
    }

    /// Create an integer value
    pub const fn int(v: i64) -> Self {
        Self::Int(v)
    }

    /// Create a string value
    pub fn string(s: impl Into<String>) -> Self {
        Self::String(s.into())
    }

    /// Create a byte array value
    pub fn bytes(b: impl Into<Vec<u8>>) -> Self {
        Self::Bytes(b.into())
    }

    /// Create a reference value
    pub const fn ref_val(loc: u32) -> Self {
        Self::Ref(loc)
    }

    /// Create a channel value
    pub const fn chan(id: u32) -> Self {
        Self::Chan(id)
    }

    /// Create a tuple value
    pub fn tuple(vs: Vec<Value>) -> Self {
        Self::Tuple(vs)
    }

    /// Create a variant value
    pub fn variant(tag: u32, payload: Value) -> Self {
        Self::Variant(tag, Box::new(payload))
    }

    /// Create a closure value
    pub fn closure(func_id: u32, env: Vec<Value>) -> Self {
        Self::Closure(func_id, env)
    }

    /// Check if this is unit
    pub const fn is_unit(&self) -> bool {
        matches!(self, Self::Unit)
    }

    /// Get as boolean if applicable
    pub const fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Get as integer if applicable
    pub const fn as_int(&self) -> Option<i64> {
        match self {
            Self::Int(n) => Some(*n),
            _ => None,
        }
    }

    /// Get as string if applicable
    pub fn as_string(&self) -> Option<&str> {
        match self {
            Self::String(s) => Some(s),
            _ => None,
        }
    }

    /// Discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Unit => 0,
            Self::Bool(_) => 1,
            Self::Int(_) => 2,
            Self::String(_) => 3,
            Self::Bytes(_) => 4,
            Self::Ref(_) => 5,
            Self::Chan(_) => 6,
            Self::Tuple(_) => 7,
            Self::Variant(_, _) => 8,
            Self::Closure(_, _) => 9,
        }
    }
}

impl Default for Value {
    fn default() -> Self {
        Self::Unit
    }
}

/// A single effect operation in a free monad program.
///
/// Represents `FreeBind op args cont` from F*, where `cont` is
/// defunctionalized to a continuation ID.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FreeOp {
    /// The effect operation to perform
    pub op: EffectOp,
    /// Arguments passed to the operation
    pub args: Vec<Value>,
    /// Continuation to invoke with the operation's result.
    /// Use `CONT_NONE` if this is the last operation.
    pub cont_id: ContId,
}

impl FreeOp {
    /// Create a new effect operation
    pub fn new(op: EffectOp, args: Vec<Value>, cont_id: ContId) -> Self {
        Self { op, args, cont_id }
    }

    /// Create an operation with no continuation (terminal)
    pub fn terminal(op: EffectOp, args: Vec<Value>) -> Self {
        Self {
            op,
            args,
            cont_id: CONT_NONE,
        }
    }

    /// Check if this operation has a continuation
    pub const fn has_continuation(&self) -> bool {
        self.cont_id != CONT_NONE
    }
}

/// Free monad representation for effect semantics.
///
/// Mirrors F*:
/// ```fstar
/// noeq type free (eff: effect_row) (a: Type) =
///   | FreeReturn : value:a -> free eff a
///   | FreeBind   : op:effect_op -> args:list value -> cont:(value -> free eff a) -> free eff a
/// ```
///
/// The effect row parameter is tracked separately in `FreeProgram`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Free {
    /// Return a value (pure computation complete)
    /// Corresponds to `FreeReturn value`
    Return(Value),

    /// Perform an effect operation and continue
    /// Corresponds to `FreeBind op args cont`
    Bind(FreeOp),
}

impl Free {
    /// Create a return (pure) computation.
    ///
    /// Mirrors F* `free_return`:
    /// ```fstar
    /// let free_return (#eff: effect_row) (#a: Type) (x: a) : free eff a =
    ///   FreeReturn x
    /// ```
    pub fn free_return(value: Value) -> Self {
        Self::Return(value)
    }

    /// Create a computation that performs a single effect.
    ///
    /// Mirrors F* `free_perform`:
    /// ```fstar
    /// let free_perform (#eff: effect_row) (op: effect_op) (args: list value)
    ///     : free eff value =
    ///   FreeBind op args (fun v -> FreeReturn v)
    /// ```
    ///
    /// Returns the effect's result directly (continuation returns immediately).
    pub fn free_perform(op: EffectOp, args: Vec<Value>) -> Self {
        Self::Bind(FreeOp::terminal(op, args))
    }

    /// Create a bind operation with explicit continuation
    pub fn free_bind(op: EffectOp, args: Vec<Value>, cont_id: ContId) -> Self {
        Self::Bind(FreeOp::new(op, args, cont_id))
    }

    /// Check if this is a return (computation complete)
    pub const fn is_return(&self) -> bool {
        matches!(self, Self::Return(_))
    }

    /// Check if this is a bind (has pending effect)
    pub const fn is_bind(&self) -> bool {
        matches!(self, Self::Bind(_))
    }

    /// Get the return value if this is a Return
    pub fn return_value(&self) -> Option<&Value> {
        match self {
            Self::Return(v) => Some(v),
            Self::Bind(_) => None,
        }
    }

    /// Get the operation if this is a Bind
    pub fn bind_op(&self) -> Option<&FreeOp> {
        match self {
            Self::Return(_) => None,
            Self::Bind(op) => Some(op),
        }
    }

    /// Extract the next operation to execute, if any.
    ///
    /// Returns `Some((op, args))` if there's a pending effect to handle,
    /// or `None` if the computation has completed (Return).
    pub fn step(&self) -> Option<(EffectOp, Vec<Value>)> {
        match self {
            Self::Return(_) => None,
            Self::Bind(free_op) => Some((free_op.op.clone(), free_op.args.clone())),
        }
    }
}

impl Default for Free {
    fn default() -> Self {
        Self::Return(Value::Unit)
    }
}

/// A complete free monad program with continuation table.
///
/// This structure represents a full effectful computation as a sequence
/// of effect operations connected by continuations.
///
/// # Continuation Table
///
/// Since Rust cannot represent recursive closures directly, we use a
/// defunctionalized representation. Each `FreeOp` contains a `cont_id`
/// that indexes into the `continuations` vector to find the next `Free`
/// to execute after the effect is handled.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FreeProgram {
    /// The effect row this program operates in
    pub effect_row: EffectRow,

    /// Current computation state (entry point or current position)
    pub current: Free,

    /// Continuation table: maps ContId -> continuation body
    pub continuations: Vec<Free>,

    /// Program counter for stepping
    step_count: usize,
}

impl FreeProgram {
    /// Create a new empty program with the given effect row
    pub fn new(effect_row: EffectRow) -> Self {
        Self {
            effect_row,
            current: Free::Return(Value::Unit),
            continuations: Vec::new(),
            step_count: 0,
        }
    }

    /// Create a pure program that just returns a value
    pub fn pure(value: Value) -> Self {
        Self {
            effect_row: EffectRow::pure(),
            current: Free::Return(value),
            continuations: Vec::new(),
            step_count: 0,
        }
    }

    /// Create a program from a single Free computation
    pub fn from_free(effect_row: EffectRow, free: Free) -> Self {
        Self {
            effect_row,
            current: free,
            continuations: Vec::new(),
            step_count: 0,
        }
    }

    /// Add a continuation and get its ID
    pub fn add_continuation(&mut self, cont: Free) -> ContId {
        let id = self.continuations.len() as ContId;
        self.continuations.push(cont);
        id
    }

    /// Perform an effect operation, returning to the given continuation
    pub fn perform_with_cont(&mut self, op: EffectOp, args: Vec<Value>, cont_id: ContId) {
        self.current = Free::Bind(FreeOp::new(op, args, cont_id));
    }

    /// Perform an effect operation as the final step (no continuation)
    pub fn perform_terminal(&mut self, op: EffectOp, args: Vec<Value>) {
        self.current = Free::Bind(FreeOp::terminal(op, args));
    }

    /// Set the final return value
    pub fn return_value(&mut self, value: Value) {
        self.current = Free::Return(value);
    }

    /// Check if the program has completed (current is Return)
    pub fn is_complete(&self) -> bool {
        self.current.is_return()
    }

    /// Get the final result if the program has completed
    pub fn result(&self) -> Option<&Value> {
        self.current.return_value()
    }

    /// Get the next effect operation to execute.
    ///
    /// Returns `Some((op, args))` if there's a pending effect,
    /// or `None` if the program has completed.
    pub fn step(&self) -> Option<(EffectOp, Vec<Value>)> {
        self.current.step()
    }

    /// Advance the program by providing the result of the current effect.
    ///
    /// This simulates the handler invoking the continuation with a value.
    /// Returns `true` if the program advanced, `false` if it was already complete
    /// or the continuation was not found.
    pub fn advance(&mut self, result: Value) -> bool {
        match &self.current {
            Free::Return(_) => false,
            Free::Bind(op) => {
                if op.cont_id == CONT_NONE {
                    // Terminal operation - program completes with the result
                    self.current = Free::Return(result);
                    self.step_count += 1;
                    true
                } else if let Some(cont) = self.continuations.get(op.cont_id as usize) {
                    // Look up the continuation and substitute the result
                    // Note: In a full implementation, we would substitute `result`
                    // into the continuation. For now, we just move to the next step.
                    self.current = cont.clone();
                    self.step_count += 1;
                    true
                } else {
                    // Invalid continuation ID
                    false
                }
            }
        }
    }

    /// Get the number of steps executed so far
    pub const fn step_count(&self) -> usize {
        self.step_count
    }

    /// Get all effects that may be performed by this program.
    ///
    /// Collects all effect operations from the current computation
    /// and all continuations.
    pub fn all_effects(&self) -> Vec<&EffectOp> {
        let mut effects = Vec::new();

        if let Free::Bind(op) = &self.current {
            effects.push(&op.op);
        }

        for cont in &self.continuations {
            if let Free::Bind(op) = cont {
                effects.push(&op.op);
            }
        }

        effects
    }
}

impl Default for FreeProgram {
    fn default() -> Self {
        Self::pure(Value::Unit)
    }
}

/// Builder for constructing free monad programs fluently.
///
/// Allows chaining effect operations to build up a program.
#[derive(Debug, Clone)]
pub struct FreeProgramBuilder {
    effect_row: EffectRow,
    operations: Vec<(EffectOp, Vec<Value>)>,
    final_value: Option<Value>,
}

impl FreeProgramBuilder {
    /// Create a new builder with the given effect row
    pub fn new(effect_row: EffectRow) -> Self {
        Self {
            effect_row,
            operations: Vec::new(),
            final_value: None,
        }
    }

    /// Create a builder for pure computations
    pub fn pure() -> Self {
        Self::new(EffectRow::pure())
    }

    /// Add an effect operation
    pub fn perform(mut self, op: EffectOp, args: Vec<Value>) -> Self {
        self.operations.push((op, args));
        self
    }

    /// Set the final return value
    pub fn return_val(mut self, value: Value) -> Self {
        self.final_value = Some(value);
        self
    }

    /// Build the program
    pub fn build(self) -> FreeProgram {
        let mut program = FreeProgram::new(self.effect_row);

        if self.operations.is_empty() {
            // Pure program
            program.current = Free::Return(self.final_value.unwrap_or(Value::Unit));
            return program;
        }

        // Build the continuation chain in reverse order
        // Last operation leads to Return
        let mut next_free = Free::Return(self.final_value.unwrap_or(Value::Unit));

        for (op, args) in self.operations.into_iter().rev() {
            let cont_id = program.add_continuation(next_free);
            next_free = Free::Bind(FreeOp::new(op, args, cont_id));
        }

        program.current = next_free;
        program
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effects::AbstractLoc;

    #[test]
    fn test_value_constructors() {
        assert!(Value::UNIT.is_unit());
        assert_eq!(Value::bool(true).as_bool(), Some(true));
        assert_eq!(Value::int(42).as_int(), Some(42));
        assert_eq!(Value::string("hello").as_string(), Some("hello"));
    }

    #[test]
    fn test_value_discriminants() {
        assert_eq!(Value::Unit.discriminant(), 0);
        assert_eq!(Value::Bool(true).discriminant(), 1);
        assert_eq!(Value::Int(0).discriminant(), 2);
        assert_eq!(Value::String(String::new()).discriminant(), 3);
    }

    #[test]
    fn test_free_return() {
        let free = Free::free_return(Value::int(42));
        assert!(free.is_return());
        assert!(!free.is_bind());
        assert_eq!(free.return_value(), Some(&Value::int(42)));
        assert!(free.step().is_none());
    }

    #[test]
    fn test_free_perform() {
        let free = Free::free_perform(EffectOp::Io, vec![Value::string("test")]);
        assert!(!free.is_return());
        assert!(free.is_bind());
        assert!(free.return_value().is_none());

        let (op, args) = free.step().expect("should have step");
        assert!(matches!(op, EffectOp::Io));
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn test_free_bind_with_continuation() {
        let free = Free::free_bind(EffectOp::Console, vec![], 5);

        if let Free::Bind(op) = &free {
            assert!(op.has_continuation());
            assert_eq!(op.cont_id, 5);
        } else {
            panic!("expected Bind");
        }
    }

    #[test]
    fn test_free_op_terminal() {
        let op = FreeOp::terminal(EffectOp::Panic, vec![]);
        assert!(!op.has_continuation());
        assert_eq!(op.cont_id, CONT_NONE);
    }

    #[test]
    fn test_free_program_pure() {
        let prog = FreeProgram::pure(Value::int(100));
        assert!(prog.is_complete());
        assert_eq!(prog.result(), Some(&Value::int(100)));
        assert!(prog.step().is_none());
    }

    #[test]
    fn test_free_program_step() {
        let mut prog = FreeProgram::new(EffectRow::single(EffectOp::Io));
        prog.perform_terminal(EffectOp::Io, vec![Value::string("hello")]);

        assert!(!prog.is_complete());
        let step = prog.step();
        assert!(step.is_some());

        let (op, args) = step.unwrap();
        assert!(matches!(op, EffectOp::Io));
        assert_eq!(args.len(), 1);
    }

    #[test]
    fn test_free_program_advance() {
        let mut prog = FreeProgram::new(EffectRow::single(EffectOp::Io));
        prog.perform_terminal(EffectOp::Io, vec![]);

        assert!(!prog.is_complete());

        // Advance with a result
        let advanced = prog.advance(Value::int(42));
        assert!(advanced);
        assert!(prog.is_complete());
        assert_eq!(prog.result(), Some(&Value::int(42)));
    }

    #[test]
    fn test_free_program_with_continuations() {
        let mut prog = FreeProgram::new(EffectRow::new(vec![EffectOp::Io, EffectOp::Console]));

        // Add continuation: after first effect, return value
        let final_cont = prog.add_continuation(Free::Return(Value::string("done")));

        // Add continuation: after Io, perform Console
        let console_step = Free::Bind(FreeOp::new(EffectOp::Console, vec![], final_cont));
        let io_cont = prog.add_continuation(console_step);

        // Start with Io
        prog.perform_with_cont(EffectOp::Io, vec![Value::string("input")], io_cont);

        // Step 1: Io effect
        assert!(!prog.is_complete());
        let (op1, _) = prog.step().unwrap();
        assert!(matches!(op1, EffectOp::Io));

        // Advance past Io
        prog.advance(Value::Unit);
        assert!(!prog.is_complete());

        // Step 2: Console effect
        let (op2, _) = prog.step().unwrap();
        assert!(matches!(op2, EffectOp::Console));

        // Advance past Console
        prog.advance(Value::Unit);
        assert!(prog.is_complete());
        assert_eq!(prog.result(), Some(&Value::string("done")));
    }

    #[test]
    fn test_free_program_builder() {
        let prog = FreeProgramBuilder::new(EffectRow::new(vec![EffectOp::Io, EffectOp::Console]))
            .perform(EffectOp::Io, vec![Value::string("read")])
            .perform(EffectOp::Console, vec![Value::string("write")])
            .return_val(Value::int(0))
            .build();

        // Should have first operation ready
        assert!(!prog.is_complete());
        let (op, args) = prog.step().unwrap();
        assert!(matches!(op, EffectOp::Io));
        assert_eq!(args, vec![Value::string("read")]);
    }

    #[test]
    fn test_free_program_builder_pure() {
        let prog = FreeProgramBuilder::pure()
            .return_val(Value::bool(true))
            .build();

        assert!(prog.is_complete());
        assert_eq!(prog.result(), Some(&Value::bool(true)));
    }

    #[test]
    fn test_free_program_all_effects() {
        let prog = FreeProgramBuilder::new(EffectRow::new(vec![
            EffectOp::Io,
            EffectOp::Console,
            EffectOp::Fs,
        ]))
        .perform(EffectOp::Io, vec![])
        .perform(EffectOp::Console, vec![])
        .perform(EffectOp::Fs, vec![])
        .build();

        let effects = prog.all_effects();
        assert_eq!(effects.len(), 3);
    }

    #[test]
    fn test_free_program_step_count() {
        // Build a program with 2 Io operations
        let mut prog = FreeProgramBuilder::new(EffectRow::single(EffectOp::Io))
            .perform(EffectOp::Io, vec![])
            .perform(EffectOp::Io, vec![])
            .build();

        assert_eq!(prog.step_count(), 0);
        assert!(!prog.is_complete());

        // First advance: move past first Io
        prog.advance(Value::Unit);
        assert_eq!(prog.step_count(), 1);
        assert!(!prog.is_complete());

        // Second advance: move past second Io, program completes
        prog.advance(Value::Unit);
        assert_eq!(prog.step_count(), 2);
        assert!(prog.is_complete());

        // Third advance should fail (program already complete)
        let advanced = prog.advance(Value::Unit);
        assert!(!advanced);
        assert_eq!(prog.step_count(), 2); // unchanged
    }

    #[test]
    fn test_value_complex_types() {
        // Test tuple
        let tuple = Value::tuple(vec![Value::int(1), Value::bool(true)]);
        assert_eq!(tuple.discriminant(), 7);

        // Test variant
        let variant = Value::variant(0, Value::string("payload"));
        assert_eq!(variant.discriminant(), 8);

        // Test closure
        let closure = Value::closure(42, vec![Value::int(1), Value::int(2)]);
        assert_eq!(closure.discriminant(), 9);
    }

    #[test]
    fn test_memory_effects_in_free() {
        let loc = AbstractLoc::Concrete(42);
        let prog = FreeProgramBuilder::new(EffectRow::new(vec![
            EffectOp::Read(loc.clone()),
            EffectOp::Write(loc.clone()),
        ]))
        .perform(EffectOp::Read(loc.clone()), vec![])
        .perform(EffectOp::Write(loc), vec![Value::int(100)])
        .build();

        let effects = prog.all_effects();
        assert_eq!(effects.len(), 2);
        assert!(effects[0].is_memory());
    }

    #[test]
    fn test_free_program_default() {
        let prog = FreeProgram::default();
        assert!(prog.is_complete());
        assert_eq!(prog.result(), Some(&Value::Unit));
    }

    #[test]
    fn test_advance_on_complete_program() {
        let mut prog = FreeProgram::pure(Value::int(42));
        assert!(prog.is_complete());

        // Advancing a complete program should return false
        let advanced = prog.advance(Value::int(100));
        assert!(!advanced);

        // Result should be unchanged
        assert_eq!(prog.result(), Some(&Value::int(42)));
    }
}
