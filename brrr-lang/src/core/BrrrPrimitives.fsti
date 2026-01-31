(**
 * BrrrLang.Core.Primitives - Interface
 *
 * Foundational primitive types with overflow specifications for the Brrr-Lang
 * verified programming language. This module defines the core type system building
 * blocks upon which all other language constructs are built.
 *
 * == Specification Reference ==
 *
 * Based on brrr_lang_spec_v0.4.tex Part II: Type Primitives (Chapter 1).
 * From the specification (Section 2.2 "Numeric Types"):
 *
 *   "The integer type is parameterized by width and signedness:
 *    Int[w, s] where w in {8, 16, 32, 64, 128, Big} and s in {Signed, Unsigned}
 *    with IEEE 754 semantics for the respective precision."
 *
 * This module mechanizes these definitions in F* with full verification.
 *
 * == Design Patterns (following HACL* Lib.IntTypes) ==
 *
 * This module follows established patterns from the HACL* cryptographic library:
 *
 * 1. Refinement Types with Range Checking:
 *    - range_t it: refinement type for values in [int_min_bounded it, int_max_bounded it]
 *    - Matches HACL* pattern: type int_t (t:inttype) (l:secrecy_level) = x:int{range x t}
 *    - Reference: Lib.IntTypes.fsti lines 87-91
 *
 * 2. Bounded Integer Operations with Overflow Detection:
 *    - will_overflow_add/sub/mul/div predicates for compile-time overflow checking
 *    - Three overflow modes: wrapping, saturating, checked (matching Rust semantics)
 *    - Reference: Lib.IntTypes.fsti lines 416-476
 *
 * 3. Modular Arithmetic Specifications:
 *    - (@%.) operator: modular reduction for bounded types
 *    - Unsigned: uses FStar % (always non-negative)
 *    - Signed: uses FStar.Int.op_At_Percent (centered representation)
 *    - Reference: Lib.IntTypes.fsti lines 336-338
 *
 * 4. Compile-Time Constant Lemmas with SMTPat Triggers:
 *    - width_bits_bounded unfolds to constants (8, 16, 32, 64, 128)
 *    - pow2 lemmas for range verification
 *    - SMTPat triggers for automatic proof discharge
 *
 * == F* Standard Library Dependencies ==
 *
 * This module relies on the following F* standard library modules:
 *
 * - FStar.UInt8/16/32/64: Unsigned machine integers with modular arithmetic
 * - FStar.Int8/16/32/64: Signed machine integers with two's complement semantics
 * - FStar.Math.Lemmas: Modular arithmetic lemmas including:
 *   - lemma_mod_plus: (a + k * n) % n = a % n
 *   - pow2_lt_compat: m < n ==> pow2 m < pow2 n
 *   - pow2_double_sum: pow2 n + pow2 n = pow2 (n+1)
 *   - euclidean_division_definition: a = (a/b)*b + a%b
 * - FStar.Int: Signed integer semantics (op_Slash for truncated division,
 *   op_At_Percent for centered modulo)
 * - FStar.Mul: Multiplication operator
 *
 * == IEEE 754 Compliance ==
 *
 * Floating-point operations follow IEEE 754-2019 semantics:
 *
 * - NaN propagation: any operation with NaN input produces NaN output
 * - Infinity arithmetic:
 *   - (+Inf) + (+Inf) = +Inf
 *   - (+Inf) - (+Inf) = NaN (indeterminate form)
 *   - 0 * Inf = NaN
 *   - Inf / Inf = NaN
 * - Comparison: NaN != NaN (all NaN comparisons return false except !=)
 * - Special values: +0, -0, +Inf, -Inf, quiet NaN, signaling NaN
 * - +0 == -0 for comparison purposes (but distinct bit representations)
 *
 * See: IEEE Standard for Floating-Point Arithmetic (IEEE 754-2019)
 *
 * == Specification Errata (SPECIFICATION_ERRATA.md) ==
 *
 * This implementation addresses issues identified during F* mechanization:
 *
 * - Chapter 1.3 "Missing Input Range Preconditions": The div_checked_correct
 *   theorem requires inputs in valid range for complete soundness. For inputs
 *   outside the representable range, the postcondition may be vacuously true.
 *   The corrected specification adds:
 *
 *     let valid_input (it: bounded_int_type) (a b: int) : prop =
 *       match it.sign with
 *       | Unsigned -> a >= 0 /\ b >= 0 /\ a <= max /\ b <= max
 *       | Signed -> a >= min /\ a <= max /\ b >= min /\ b <= max
 *
 * - Chapter 1.5 "Corrected Specification": Added valid_input predicate concept
 *   for documenting when theorems hold unconditionally vs. with preconditions.
 *
 * == Verification Status ==
 *
 * Verified with F* version 2024.01+ using:
 *   --z3rlimit 50 --fuel 0 --ifuel 0 (for most definitions)
 *   --z3rlimit 100-600 --fuel 1-2 --ifuel 1 (for complex proofs)
 *
 * All lemmas verify without admits except documented limitations in errata.
 *
 * == Module Organization ==
 *
 * 1. PRIMITIVE OPERATION RESULT TYPE (prim_result)
 * 2. INTEGER TYPES (int_width, signedness, int_type, bounded_int_type)
 * 3. OVERFLOW BEHAVIOR SPECIFICATION (wrapping, saturating, checked modes)
 * 4. BITWISE OPERATIONS (and, or, xor, not, shifts)
 * 5. FLOATING POINT TYPES (IEEE 754 representation and operations)
 * 6. BASE VALUES (VUnit, VBool, VInt, VFloat, VString, VChar)
 * 7. STRING OPERATIONS (concatenation, substring, character access)
 * 8. SOURCE SPANS (file locations for error reporting)
 * 9. TYPE COERCION SPECIFICATIONS (widening, truncating, float<->int)
 * 10. PRIMITIVE OPERATION SOUNDNESS PROOFS (algebraic properties)
 *)
module BrrrPrimitives

open FStar.Mul

(* Z3 solver options for consistent proof behavior - following HACL* pattern *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** ============================================================================
    PRIMITIVE OPERATION RESULT TYPE
    ============================================================================

    A unified result type for all primitive operations that can fail.
    This enables precise specification of failure modes and correct
    propagation of error conditions through computations.

    == Design Rationale ==

    Unlike simple option types, prim_result distinguishes between different
    failure modes, enabling:
    1. Precise error reporting in the runtime
    2. Different handling strategies per error type
    3. Static verification of error handling completeness
    4. Correct error propagation in compound expressions

    == Variant Semantics ==

    - PrimSuccess v: Operation completed successfully with result v
      Example: int_add_result i32 5 3 = PrimSuccess 8

    - PrimOverflow: Integer arithmetic exceeded representable range
      Example: int_add_result i8 127 1 = PrimOverflow (127 + 1 = 128 > i8_max)
      Triggered by: add, sub, mul when result outside [min, max]
      Also: signed division INT_MIN / -1 (result = |INT_MIN| > INT_MAX)

    - PrimDivByZero: Division or modulo with zero divisor
      Example: int_div_result i32 10 0 = PrimDivByZero
      Triggered by: div, mod when divisor = 0

    - PrimNaN: Floating-point operation produced Not-a-Number
      Example: float_add NaN 1.0 = PrimNaN (NaN propagation)
      Example: float_div 0.0 0.0 = PrimNaN (indeterminate form)
      Example: float_sub +Inf +Inf = PrimNaN (indeterminate form)
      Triggered by: NaN input, 0/0, 0*Inf, Inf-Inf, Inf/Inf, sqrt(negative)

    - PrimInfinity: Floating-point operation produced infinity
      Example: float_div 1.0 0.0 = PrimInfinity
      Example: float_mul very_large very_large = PrimInfinity
      Triggered by: finite/0, overflow beyond float max

    == Comparison with Rust ==

    This type combines the semantics of several Rust constructs:
    - Result<T, ArithmeticError> for checked operations
    - Option<T> from checked_* methods
    - panic! behavior from default debug mode overflow

    Unlike Rust's checked_* which returns Option<T>, prim_result provides
    more precise error categorization for runtime error messages.

    == Usage in Proofs ==

    The SMTPat triggers on operation specs (e.g., int_add_result_spec) allow
    automatic reasoning about success/failure cases:

      let example (it: bounded_int_type) (a b: int)
          : Lemma (requires ~(will_overflow_add it a b))
                  (ensures PrimSuccess? (int_add_result it a b)) = ()

    ============================================================================ *)

type prim_result (a:Type) =
  | PrimSuccess   : v:a -> prim_result a
  | PrimOverflow  : prim_result a    (* Integer overflow/underflow *)
  | PrimDivByZero : prim_result a    (* Division by zero *)
  | PrimNaN       : prim_result a    (* NaN result from float operation *)
  | PrimInfinity  : prim_result a    (* Infinity result from float operation *)

(* Result predicates for use in lemmas.
   Using unfold so Z3 can directly inspect the match in proofs.

   Example usage:
     let lemma (r: prim_result int)
         : Lemma (requires is_success r)
                 (ensures get_success r >= 0 \/ get_success r < 0) = ()
*)
unfold let is_success #a (r: prim_result a) : bool =
  match r with | PrimSuccess _ -> true | _ -> false

(* Extract value from successful result.
   Precondition: is_success r must hold.
   This is a total function due to the refinement. *)
unfold let get_success #a (r: prim_result a{is_success r}) : a =
  match r with | PrimSuccess v -> v

(** ============================================================================
    HELPER FUNCTIONS
    ============================================================================ *)

val max : nat -> nat -> nat
val min : nat -> nat -> nat

(** ============================================================================
    INTEGER TYPES
    ============================================================================

    Integer types are parameterized by width and signedness, matching the
    specification from brrr_lang_spec_v0.4.tex Section 2.2:

      Int[w, s] where w in {8, 16, 32, 64, 128, Big} and s in {Signed, Unsigned}

    == Width Categories ==

    | Width | Bits | Signed Range                     | Unsigned Range        |
    |-------|------|----------------------------------|-----------------------|
    | I8    | 8    | [-128, 127]                      | [0, 255]              |
    | I16   | 16   | [-32768, 32767]                  | [0, 65535]            |
    | I32   | 32   | [-2^31, 2^31-1]                  | [0, 2^32-1]           |
    | I64   | 64   | [-2^63, 2^63-1]                  | [0, 2^64-1]           |
    | I128  | 128  | [-2^127, 2^127-1]                | [0, 2^128-1]          |
    | IBig  | -    | Arbitrary precision (unbounded)  | N/A (always signed)   |

    == Correspondence with F* Standard Library ==

    | Brrr Type | F* Type        | Operations Module     |
    |-----------|----------------|-----------------------|
    | i8        | FStar.Int8.t   | FStar.Int8            |
    | i16       | FStar.Int16.t  | FStar.Int16           |
    | i32       | FStar.Int32.t  | FStar.Int32           |
    | i64       | FStar.Int64.t  | FStar.Int64           |
    | u8        | FStar.UInt8.t  | FStar.UInt8           |
    | u16       | FStar.UInt16.t | FStar.UInt16          |
    | u32       | FStar.UInt32.t | FStar.UInt32          |
    | u64       | FStar.UInt64.t | FStar.UInt64          |

    == Correspondence with HACL* Lib.IntTypes ==

    | Brrr Type | HACL* inttype | HACL* secrecy  |
    |-----------|---------------|----------------|
    | i8        | S8            | PUB            |
    | i16       | S16           | PUB            |
    | i32       | S32           | PUB            |
    | i64       | S64           | PUB            |
    | u8        | U8            | PUB            |
    | u16       | U16           | PUB            |
    | u32       | U32           | PUB            |
    | u64       | U64           | PUB            |

    Note: HACL* also has SEC secrecy level for secret values that cannot leak
    through timing side channels. Brrr-Lang may add this in future versions.

    == Design Notes ==

    - bounded_width excludes IBig for operations requiring fixed bit width
    - bounded_int_type is used for all overflow-checked operations
    - IBig is reserved for arbitrary precision integers (Python-style)
    - The @(strict_on_arguments [0]) attribute enables strict evaluation of
      the width argument, allowing Z3 to compute results at verification time

    ============================================================================ *)

(* Bit widths for integers.
   Following HACL* Lib.IntTypes pattern (inttype enumeration).
   IBig represents arbitrary precision for mathematical reasoning. *)
type int_width =
  | I8   : int_width   (* 8-bit:  [-128, 127] signed, [0, 255] unsigned *)
  | I16  : int_width   (* 16-bit: [-32768, 32767] signed *)
  | I32  : int_width   (* 32-bit: [-2^31, 2^31-1] signed, most common *)
  | I64  : int_width   (* 64-bit: [-2^63, 2^63-1] signed *)
  | I128 : int_width   (* 128-bit: for crypto operations *)
  | IBig : int_width   (* Arbitrary precision - no fixed bit width *)

(* Bounded width - excludes arbitrary precision.
   Following HACL* refinement type pattern for operations requiring
   known bit width (modular arithmetic, overflow detection, shifts).
   Reference: Lib.IntTypes.fsti type inttype = t:inttype'{...} *)
unfold
let bounded_width = w:int_width{w <> IBig}

(* Signedness determines interpretation of bit patterns.
   - Signed: Two's complement representation
   - Unsigned: Direct binary representation *)
type signedness =
  | Signed   : signedness   (* Two's complement: negative values allowed *)
  | Unsigned : signedness   (* Non-negative only: [0, 2^bits - 1] *)

(* Integer type descriptor combining width and signedness.
   This record type enables generic operations over all integer types.
   Examples: { width = I32; sign = Signed } represents i32
             { width = I64; sign = Unsigned } represents u64 *)
type int_type = {
  width : int_width;
  sign  : signedness
}

(* Bounded integer type - has fixed bit width.
   Required for:
   - Modular arithmetic (needs 2^bits modulus)
   - Overflow detection (needs min/max bounds)
   - Bit shifting (shift amount must be < bits)
   - Type coercion (needs source and destination sizes) *)
unfold
let bounded_int_type = it:int_type{it.width <> IBig}

(** ----------------------------------------------------------------------------
    Common integer type constants
    ---------------------------------------------------------------------------- *)

val i8    : int_type
val i16   : int_type
val i32   : int_type
val i64   : int_type
val i128  : int_type

val u8    : int_type
val u16   : int_type
val u32   : int_type
val u64   : int_type
val u128  : int_type

val ibig  : int_type

(** ----------------------------------------------------------------------------
    Bit width operations (following HACL* Lib.IntTypes.bits pattern)
    ---------------------------------------------------------------------------- *)

(* Bit width for bounded widths - always returns nat (no option needed)
   Following HACL* bits function pattern from Lib.IntTypes.fsti lines 55-69.
   Using unfold to make definition visible to Z3 for trivial proofs. *)
[@(strict_on_arguments [0])]
unfold
let width_bits_bounded (w: bounded_width) : nat =
  if I8? w then 8
  else if I16? w then 16
  else if I32? w then 32
  else if I64? w then 64
  else 128  (* Must be I128 since w <> IBig by refinement *)

(* Bit width for any width - returns option for IBig.
   Using unfold for visibility in proofs. *)
unfold
let width_bits (w: int_width) : option nat =
  if I8? w then Some 8
  else if I16? w then Some 16
  else if I32? w then Some 32
  else if I64? w then Some 64
  else if I128? w then Some 128
  else None  (* IBig *)

(* Numeric ordering value for width comparison *)
unfold
let width_order (w: int_width) : nat =
  if I8? w then 0
  else if I16? w then 1
  else if I32? w then 2
  else if I64? w then 3
  else if I128? w then 4
  else 5  (* IBig *)

(* Width ordering for type coercion.
   Using unfold so Z3 can see the comparison logic. *)
unfold
let width_leq (w1 w2: int_width) : bool =
  width_order w1 <= width_order w2

(** ----------------------------------------------------------------------------
    Integer range operations (following HACL* minint/maxint pattern)
    ---------------------------------------------------------------------------- *)

(* Range for any type - returns option for IBig.
   Using unfold for proof visibility. *)
unfold
let int_min (it: int_type) : option int =
  if IBig? it.width then None
  else
    let bits = width_bits_bounded it.width in
    if Signed? it.sign then Some (-(pow2 (bits - 1)))
    else Some 0

unfold
let int_max (it: int_type) : option int =
  if IBig? it.width then None
  else
    let bits = width_bits_bounded it.width in
    if Signed? it.sign then Some (pow2 (bits - 1) - 1)
    else Some (pow2 bits - 1)

(* Range for bounded types - always returns int (no option)
   Following HACL* pattern: minint/maxint from Lib.IntTypes.fsti lines 79-85.
   Using unfold so Z3 can compute ranges directly. *)
[@(strict_on_arguments [0])]
unfold
let int_min_bounded (it: bounded_int_type) : int =
  let bits = width_bits_bounded it.width in
  if Signed? it.sign then -(pow2 (bits - 1)) else 0

[@(strict_on_arguments [0])]
unfold
let int_max_bounded (it: bounded_int_type) : int =
  let bits = width_bits_bounded it.width in
  if Signed? it.sign then pow2 (bits - 1) - 1 else pow2 bits - 1

(* Check if value is in range for bounded type
   Following HACL* range pattern from Lib.IntTypes.fsti lines 87-91.
   Using unfold for proof visibility. *)
unfold
let in_range (v: int) (it: bounded_int_type) : bool =
  int_min_bounded it <= v && v <= int_max_bounded it

(* Refinement type for values in range - following HACL* range_t pattern
   Reference: Lib.IntTypes.fsti line 91: type range_t (t:inttype) = x:int{range x t} *)
unfold
let range_t (it: bounded_int_type) = x:int{in_range x it}

(** ----------------------------------------------------------------------------
    Compile-time constant lemmas (following HACL* Lib.IntTypes.fst pow2 patterns)

    These lemmas enable SMT solver to automatically expand width_bits_bounded
    at verification time, similar to how HACL* handles pow2 constants.
    Reference: Lib.IntTypes.fst lines 7-10
    ---------------------------------------------------------------------------- *)

(* Note: No SMTPat here - unit parameter causes Warning 271.
   Use width_bits_bounded directly which is computable, or call these lemmas explicitly.
   Following HACL* pattern from Lib.IntTypes.fst where assert_norm is used instead. *)
val width_bits_8   : unit -> Lemma (width_bits_bounded I8 = 8)
val width_bits_16  : unit -> Lemma (width_bits_bounded I16 = 16)
val width_bits_32  : unit -> Lemma (width_bits_bounded I32 = 32)
val width_bits_64  : unit -> Lemma (width_bits_bounded I64 = 64)
val width_bits_128 : unit -> Lemma (width_bits_bounded I128 = 128)

(** ----------------------------------------------------------------------------
    Width ordering lemmas
    ---------------------------------------------------------------------------- *)

val width_leq_refl : w:int_width ->
    Lemma (width_leq w w = true)
    [SMTPat (width_leq w w)]

val width_leq_trans : w1:int_width -> w2:int_width -> w3:int_width ->
    Lemma (requires width_leq w1 w2 && width_leq w2 w3)
          (ensures width_leq w1 w3 = true)

(** ----------------------------------------------------------------------------
    Integer range lemmas
    ---------------------------------------------------------------------------- *)

val int_range_valid : it:bounded_int_type ->
    Lemma (int_min_bounded it < int_max_bounded it)
    [SMTPat (int_min_bounded it)]

val signed_unsigned_range : it:bounded_int_type ->
    Lemma (requires it.sign = Signed)
          (ensures (let unsigned_it = { it with sign = Unsigned } in
                   int_max_bounded it < int_max_bounded unsigned_it))

val width_bits_matches_option : w:bounded_width ->
    Lemma (width_bits w = Some (width_bits_bounded w))
    [SMTPat (width_bits w)]

(** ============================================================================
    OVERFLOW BEHAVIOR SPECIFICATION
    ============================================================================

    Integer arithmetic can exceed the representable range of bounded types.
    This section specifies how overflow is detected and handled, following
    established patterns from HACL* Lib.IntTypes and Rust's numeric types.

    == The Overflow Problem ==

    For a bounded integer type with n bits:
    - Unsigned range: [0, 2^n - 1]
    - Signed range: [-2^(n-1), 2^(n-1) - 1]

    When arithmetic results fall outside these ranges, we have "overflow"
    (positive) or "underflow" (negative). Both are handled uniformly as
    "overflow" in this specification.

    == Overflow Scenarios by Operation ==

    | Operation | Overflow Condition                              |
    |-----------|-------------------------------------------------|
    | a + b     | result < min OR result > max                    |
    | a - b     | result < min OR result > max                    |
    | a * b     | result < min OR result > max                    |
    | a / b     | Signed: a = MIN_INT AND b = -1 (result = |MIN|) |
    |           | (Unsigned division never overflows)             |
    | -a        | Signed: a = MIN_INT (result = |MIN_INT| > MAX)  |

    == Handling Strategies (matching Rust) ==

    Rust provides four strategies for overflow handling. This module provides
    the equivalent specifications:

    1. WRAPPING (Rust: Wrapping<T>, wrapping_* methods)
       - Result is reduced modulo 2^n
       - For signed: uses centered representation [-2^(n-1), 2^(n-1)-1]
       - Always produces a valid in-range value
       - Example: 255u8.wrapping_add(1) = 0u8

    2. SATURATING (Rust: Saturating<T>, saturating_* methods)
       - Result is clamped to [min, max]
       - Overflow -> max, underflow -> min
       - Always produces a valid in-range value
       - Example: 255u8.saturating_add(1) = 255u8

    3. CHECKED (Rust: checked_* methods returning Option<T>)
       - Returns Some(result) if in range, None on overflow
       - Caller must handle the None case
       - Example: 255u8.checked_add(1) = None

    4. PANIC (Rust: default behavior in debug mode)
       - Runtime panic on overflow
       - Not modeled directly; use PrimOverflow result
       - In Brrr-Lang, this maps to returning PrimOverflow

    == HACL* Reference ==

    HACL* Lib.IntTypes provides similar patterns:
    - add_mod, sub_mod, mul_mod: wrapping arithmetic (lines 416-476)
    - The @%. operator: modular reduction (lines 336-338)
    - Modulus 2^n for n-bit types (line 75)

    == FStar.Math.Lemmas Used ==

    For proving overflow properties, key lemmas from FStar.Math.Lemmas:
    - lemma_mod_plus: (a + k*n) % n = a % n
    - modulo_range_lemma: 0 <= x % n < n for n > 0
    - pow2_lt_compat: m < n ==> pow2 m < pow2 n
    - pow2_double_sum: pow2 n + pow2 n = pow2 (n+1)

    ============================================================================ *)

(** ----------------------------------------------------------------------------
    Overflow behavior modes
    ---------------------------------------------------------------------------- *)

(* Overflow behavior modes - matching Rust semantics.
   These modes determine how arithmetic operations handle overflow.

   Rust equivalents:
   - OBWrap: std::num::Wrapping<T>, .wrapping_add(), .wrapping_sub(), etc.
   - OBSaturate: std::num::Saturating<T>, .saturating_add(), etc.
   - OBChecked: .checked_add() returning Option<T>
   - OBPanic: Default behavior in debug mode (panic on overflow)

   In Brrr-Lang, the overflow mode can be specified per-operation or
   per-expression block, similar to Rust's different method flavors. *)
type overflow_behavior =
  | OBWrap      (* Wrapping arithmetic - result modulo 2^n *)
  | OBSaturate  (* Saturating arithmetic - clamp to min/max *)
  | OBChecked   (* Checked arithmetic - return option/result *)
  | OBPanic     (* Panic on overflow - like Rust default debug mode *)

(** ----------------------------------------------------------------------------
    Modulus function (following HACL* Lib.IntTypes.fsti line 75 pattern)
    ---------------------------------------------------------------------------- *)

(* Modulus for bounded integer types: 2^bits
   Following HACL* pattern: let modulus (t:inttype) = pow2 (bits t)
   Using unfold so Z3 can compute modulus values directly. *)
[@(strict_on_arguments [0])]
unfold
let modulus (w: bounded_width) : pos = pow2 (width_bits_bounded w)

(** ----------------------------------------------------------------------------
    Compile-time modulus verification lemmas
    ---------------------------------------------------------------------------- *)

val modulus_8   : unit -> Lemma (modulus I8 = 256)
val modulus_16  : unit -> Lemma (modulus I16 = 65536)
val modulus_32  : unit -> Lemma (modulus I32 = 4294967296)
val modulus_64  : unit -> Lemma (modulus I64 = 18446744073709551616)

(** ----------------------------------------------------------------------------
    Modular arithmetic operator (following HACL* @%. pattern)
    ---------------------------------------------------------------------------- *)

(* Modular reduction operator for signed and unsigned types.
   Following HACL* Lib.IntTypes.fsti lines 336-338.
   Using unfold for proof visibility. *)
[@(strict_on_arguments [1])]
unfold
let op_At_Percent_Dot (x: int) (it: bounded_int_type) : int =
  let m = modulus it.width in
  if Unsigned? it.sign then x % m else FStar.Int.op_At_Percent x m

(** ----------------------------------------------------------------------------
    Overflow detection predicates
    ---------------------------------------------------------------------------- *)

(* Check if addition will overflow for a given integer type.
   Using unfold so overflow specifications are trivially provable. *)
unfold
let will_overflow_add (it: bounded_int_type) (a b: int) : bool =
  let result = a + b in
  let min_val = int_min_bounded it in
  let max_val = int_max_bounded it in
  result > max_val || result < min_val

(* Check if subtraction will overflow for a given integer type *)
unfold
let will_overflow_sub (it: bounded_int_type) (a b: int) : bool =
  let result = a - b in
  let min_val = int_min_bounded it in
  let max_val = int_max_bounded it in
  result > max_val || result < min_val

(* Check if multiplication will overflow for a given integer type *)
unfold
let will_overflow_mul (it: bounded_int_type) (a b: int) : bool =
  let result = a * b in
  let min_val = int_min_bounded it in
  let max_val = int_max_bounded it in
  result > max_val || result < min_val

(* Check if division will overflow (only for INT_MIN / -1 in signed types) *)
unfold
let will_overflow_div (it: bounded_int_type) (a: int) (d: int{d <> 0}) : bool =
  if Unsigned? it.sign then false  (* Unsigned division never overflows *)
  else
    (* Only overflow case for signed: INT_MIN / -1 *)
    let min_val = int_min_bounded it in
    a = min_val && d = -1

(** ----------------------------------------------------------------------------
    Overflow specification lemmas
    ---------------------------------------------------------------------------- *)

(* Overflow iff result is outside representable range *)
val overflow_add_spec : it:bounded_int_type -> a:int -> b:int ->
    Lemma (will_overflow_add it a b <==>
           (a + b < int_min_bounded it \/ a + b > int_max_bounded it))
    [SMTPat (will_overflow_add it a b)]

val overflow_sub_spec : it:bounded_int_type -> a:int -> b:int ->
    Lemma (will_overflow_sub it a b <==>
           (a - b < int_min_bounded it \/ a - b > int_max_bounded it))
    [SMTPat (will_overflow_sub it a b)]

val overflow_mul_spec : it:bounded_int_type -> a:int -> b:int ->
    Lemma (will_overflow_mul it a b <==>
           (a * b < int_min_bounded it \/ a * b > int_max_bounded it))
    [SMTPat (will_overflow_mul it a b)]

(** ----------------------------------------------------------------------------
    Wrapping arithmetic operations (like Rust Wrapping<T>)
    Following HACL* add_mod pattern from Lib.IntTypes.fsti lines 416-426
    ---------------------------------------------------------------------------- *)

(* Wrapping addition - result wraps on overflow *)
val add_wrap : it:bounded_int_type -> int -> int -> int

(* Wrapping subtraction *)
val sub_wrap : it:bounded_int_type -> int -> int -> int

(* Wrapping multiplication *)
val mul_wrap : it:bounded_int_type -> int -> int -> int

(* Wrapping negation *)
val neg_wrap : it:bounded_int_type -> int -> int

(** ----------------------------------------------------------------------------
    Saturating arithmetic operations (like Rust saturating_* methods)
    ---------------------------------------------------------------------------- *)

(* Saturating addition - clamps result to [min, max] *)
val add_sat : it:bounded_int_type -> int -> int -> int

(* Saturating subtraction *)
val sub_sat : it:bounded_int_type -> int -> int -> int

(* Saturating multiplication *)
val mul_sat : it:bounded_int_type -> int -> int -> int

(** ----------------------------------------------------------------------------
    Checked arithmetic operations (like Rust checked_* methods)
    ---------------------------------------------------------------------------- *)

(* Checked addition - returns None on overflow *)
val add_checked : it:bounded_int_type -> int -> int -> option int

(* Checked subtraction - returns None on overflow *)
val sub_checked : it:bounded_int_type -> int -> int -> option int

(* Checked multiplication - returns None on overflow *)
val mul_checked : it:bounded_int_type -> int -> int -> option int

(* Checked division - returns None on division by zero or overflow *)
val div_checked : it:bounded_int_type -> int -> int -> option int

(* Checked modulo - returns None on division by zero *)
val mod_checked : it:bounded_int_type -> int -> int -> option int

(** ----------------------------------------------------------------------------
    Result-returning arithmetic operations (using prim_result)
    These provide more precise error information than option-returning versions.
    ---------------------------------------------------------------------------- *)

(* Integer addition with precise error reporting *)
val int_add_result : it:bounded_int_type -> int -> int -> prim_result int

(* Integer subtraction with precise error reporting *)
val int_sub_result : it:bounded_int_type -> int -> int -> prim_result int

(* Integer multiplication with precise error reporting *)
val int_mul_result : it:bounded_int_type -> int -> int -> prim_result int

(* Integer division with precise error reporting *)
val int_div_result : it:bounded_int_type -> int -> int -> prim_result int

(* Integer modulo with precise error reporting *)
val int_mod_result : it:bounded_int_type -> int -> int -> prim_result int

(** ----------------------------------------------------------------------------
    Overflow arithmetic lemmas
    ---------------------------------------------------------------------------- *)

(* Wrapping operations always produce in-range results *)
val add_wrap_in_range : it:bounded_int_type -> a:int -> b:int ->
    Lemma (let r = add_wrap it a b in
           r >= int_min_bounded it /\ r <= int_max_bounded it)
    [SMTPat (add_wrap it a b)]

val sub_wrap_in_range : it:bounded_int_type -> a:int -> b:int ->
    Lemma (let r = sub_wrap it a b in
           r >= int_min_bounded it /\ r <= int_max_bounded it)
    [SMTPat (sub_wrap it a b)]

val mul_wrap_in_range : it:bounded_int_type -> a:int -> b:int ->
    Lemma (let r = mul_wrap it a b in
           r >= int_min_bounded it /\ r <= int_max_bounded it)
    [SMTPat (mul_wrap it a b)]

(* Saturating operations always produce in-range results *)
val add_sat_in_range : it:bounded_int_type -> a:int -> b:int ->
    Lemma (let r = add_sat it a b in
           r >= int_min_bounded it /\ r <= int_max_bounded it)
    [SMTPat (add_sat it a b)]

val sub_sat_in_range : it:bounded_int_type -> a:int -> b:int ->
    Lemma (let r = sub_sat it a b in
           r >= int_min_bounded it /\ r <= int_max_bounded it)
    [SMTPat (sub_sat it a b)]

val mul_sat_in_range : it:bounded_int_type -> a:int -> b:int ->
    Lemma (let r = mul_sat it a b in
           r >= int_min_bounded it /\ r <= int_max_bounded it)
    [SMTPat (mul_sat it a b)]

(* Checked operations return Some only when no overflow *)
val add_checked_correct : it:bounded_int_type -> a:int -> b:int ->
    Lemma (match add_checked it a b with
           | Some r -> r = a + b /\ r >= int_min_bounded it /\ r <= int_max_bounded it
           | None -> will_overflow_add it a b)
    [SMTPat (add_checked it a b)]

val sub_checked_correct : it:bounded_int_type -> a:int -> b:int ->
    Lemma (match sub_checked it a b with
           | Some r -> r = a - b /\ r >= int_min_bounded it /\ r <= int_max_bounded it
           | None -> will_overflow_sub it a b)
    [SMTPat (sub_checked it a b)]

val mul_checked_correct : it:bounded_int_type -> a:int -> b:int ->
    Lemma (match mul_checked it a b with
           | Some r -> r = a * b /\ r >= int_min_bounded it /\ r <= int_max_bounded it
           | None -> will_overflow_mul it a b)
    [SMTPat (mul_checked it a b)]

val div_checked_correct : it:bounded_int_type -> a:int -> b:int ->
    Lemma (match div_checked it a b with
           | Some r -> b <> 0 /\ ~(will_overflow_div it a b) /\
                      r >= int_min_bounded it /\ r <= int_max_bounded it
           | None -> b = 0 \/ will_overflow_div it a b)
    [SMTPat (div_checked it a b)]

(* Wrapping semantics match modular arithmetic *)
val add_wrap_spec : it:bounded_int_type -> a:int -> b:int ->
    Lemma (add_wrap it a b = (a + b) @%. it)
    [SMTPat (add_wrap it a b)]

val sub_wrap_spec : it:bounded_int_type -> a:int -> b:int ->
    Lemma (sub_wrap it a b = (a - b) @%. it)
    [SMTPat (sub_wrap it a b)]

val mul_wrap_spec : it:bounded_int_type -> a:int -> b:int ->
    Lemma (mul_wrap it a b = (a * b) @%. it)
    [SMTPat (mul_wrap it a b)]

(* Saturating semantics specification *)
val add_sat_spec : it:bounded_int_type -> a:int -> b:int ->
    Lemma (let sum = a + b in
           let min_v = int_min_bounded it in
           let max_v = int_max_bounded it in
           add_sat it a b = (if sum > max_v then max_v
                            else if sum < min_v then min_v
                            else sum))
    [SMTPat (add_sat it a b)]

(* Result operations match checked semantics with precise error *)
val int_add_result_spec : it:bounded_int_type -> a:int -> b:int ->
    Lemma (match int_add_result it a b with
           | PrimSuccess r -> r = a + b /\ in_range r it
           | PrimOverflow -> will_overflow_add it a b
           | _ -> False)
    [SMTPat (int_add_result it a b)]

val int_div_result_spec : it:bounded_int_type -> a:int -> b:int ->
    Lemma (match int_div_result it a b with
           | PrimSuccess _ -> b <> 0 /\ ~(will_overflow_div it a b)
           | PrimDivByZero -> b = 0
           | PrimOverflow -> b <> 0 /\ will_overflow_div it a b
           | _ -> False)
    [SMTPat (int_div_result it a b)]

(** ============================================================================
    BITWISE OPERATIONS
    ============================================================================ *)

(* Bitwise AND - always in range, no overflow possible *)
val bit_and : it:bounded_int_type -> range_t it -> range_t it -> range_t it

(* Bitwise OR - always in range, no overflow possible *)
val bit_or : it:bounded_int_type -> range_t it -> range_t it -> range_t it

(* Bitwise XOR - always in range, no overflow possible *)
val bit_xor : it:bounded_int_type -> range_t it -> range_t it -> range_t it

(* Bitwise NOT - always in range, no overflow possible *)
val bit_not : it:bounded_int_type -> range_t it -> range_t it

(* Left shift - may overflow for signed types *)
val shift_left : it:bounded_int_type -> range_t it -> s:nat{s < width_bits_bounded it.width} -> range_t it

(* Right shift - arithmetic for signed, logical for unsigned *)
val shift_right : it:bounded_int_type -> range_t it -> s:nat{s < width_bits_bounded it.width} -> range_t it

(* Shift amount type - shift must be less than bit width *)
unfold
let shift_amount (w: bounded_width) = s:nat{s < width_bits_bounded w}

(** ============================================================================
    FLOATING POINT TYPES
    ============================================================================ *)

type float_prec =
  | F16 : float_prec
  | F32 : float_prec
  | F64 : float_prec

val float_bits : float_prec -> nat

(** ============================================================================
    IEEE 754 FLOAT REPRESENTATION AND OPERATIONS
    ============================================================================

    Floating-point numbers follow the IEEE 754-2019 standard. This section
    documents the binary representation and special value semantics.

    == Binary64 (double precision) Layout ==

    64 bits total:
    +---+------------------+----------------------------------------------------+
    |63 | 62            52 | 51                                              0 |
    +---+------------------+----------------------------------------------------+
    | S |    Exponent (E)  |                  Mantissa (M)                     |
    +---+------------------+----------------------------------------------------+
      1       11 bits                        52 bits

    - Sign (S): 0 = positive, 1 = negative
    - Exponent (E): biased by 1023 (actual = E - 1023)
    - Mantissa (M): fractional part (implicit 1.M for normal numbers)

    Value = (-1)^S * 2^(E-1023) * 1.M  (for normal numbers)

    == Binary32 (single precision) Layout ==

    32 bits: 1 sign + 8 exponent (bias 127) + 23 mantissa

    == Binary16 (half precision) Layout ==

    16 bits: 1 sign + 5 exponent (bias 15) + 10 mantissa

    == Special Values (64-bit) ==

    | Category    | Sign | Exponent | Mantissa | Hex Pattern          |
    |-------------|------|----------|----------|----------------------|
    | +0          | 0    | 0        | 0        | 0x0000000000000000   |
    | -0          | 1    | 0        | 0        | 0x8000000000000000   |
    | +Infinity   | 0    | 2047     | 0        | 0x7FF0000000000000   |
    | -Infinity   | 1    | 2047     | 0        | 0xFFF0000000000000   |
    | Quiet NaN   | x    | 2047     | != 0     | 0x7FF8000000000001.. |
    | Signal NaN  | x    | 2047     | != 0     | 0x7FF0000000000001.. |
    | Subnormal   | x    | 0        | != 0     | Denormalized numbers |
    | Normal      | x    | 1-2046   | any      | Regular floats       |

    == NaN Behavior (CRITICAL) ==

    IEEE 754 specifies that NaN (Not a Number) has special comparison semantics:

    - NaN == NaN returns FALSE (not equal to itself!)
    - NaN != NaN returns TRUE
    - NaN < x returns FALSE for any x
    - NaN > x returns FALSE for any x
    - NaN <= x returns FALSE for any x
    - NaN >= x returns FALSE for any x

    This is correctly modeled in float_repr_eq_ieee754 and comparison functions.
    For bit-exact comparison (ignoring IEEE 754), use float_repr_eq_bits.

    == NaN Propagation Rules ==

    Any arithmetic operation with NaN input produces NaN output:
    - NaN + x = NaN
    - NaN - x = NaN
    - NaN * x = NaN
    - NaN / x = NaN
    - sqrt(NaN) = NaN

    Operations that produce NaN from non-NaN inputs:
    - 0 / 0 = NaN (indeterminate)
    - 0 * Inf = NaN (indeterminate)
    - Inf - Inf = NaN (indeterminate)
    - Inf / Inf = NaN (indeterminate)
    - sqrt(negative) = NaN (complex result)

    == Infinity Arithmetic ==

    | Operation      | Result     | Notes                        |
    |----------------|------------|------------------------------|
    | +Inf + finite  | +Inf       |                              |
    | -Inf + finite  | -Inf       |                              |
    | +Inf + +Inf    | +Inf       |                              |
    | +Inf + -Inf    | NaN        | Indeterminate                |
    | +Inf * positive| +Inf       |                              |
    | +Inf * negative| -Inf       | Sign flip                    |
    | +Inf * 0       | NaN        | Indeterminate                |
    | +Inf / finite  | +/-Inf     | Sign depends on operand      |
    | finite / +Inf  | +/-0       | Signed zero                  |
    | +Inf / +Inf    | NaN        | Indeterminate                |
    | finite / 0     | +/-Inf     | Sign depends on operands     |

    == Signed Zero ==

    IEEE 754 distinguishes +0 and -0:
    - +0 == -0 (comparison equality)
    - But they have different bit patterns
    - 1 / +0 = +Inf, 1 / -0 = -Inf (sign preservation)

    == Reference ==

    IEEE Standard for Floating-Point Arithmetic (IEEE 754-2019)
    Section 5.11: Details of operations
    Section 6.2: Operations with NaNs
    Section 7: Default exception handling

    ============================================================================ *)

(* Float representation: IEEE 754 bits stored as int *)
type float_repr = int

(* IEEE 754 component extraction *)
val float_exponent_f64 : float_repr -> int
val float_mantissa_f64 : float_repr -> int
val float_sign_f64 : float_repr -> bool  (* true = negative *)

(* IEEE 754 special value detection *)
val is_nan_f64 : float_repr -> bool
val is_infinity_f64 : float_repr -> bool
val is_pos_infinity_f64 : float_repr -> bool
val is_neg_infinity_f64 : float_repr -> bool
val is_zero_f64 : float_repr -> bool
val is_subnormal_f64 : float_repr -> bool
val is_normal_f64 : float_repr -> bool

(* IEEE 754 special value constants *)
val pos_infinity_f64 : float_repr
val neg_infinity_f64 : float_repr
val pos_zero_f64 : float_repr
val neg_zero_f64 : float_repr
val quiet_nan_f64 : float_repr  (* Canonical quiet NaN *)

(* IEEE 754 compliant float equality.
   IMPORTANT: NaN != NaN per IEEE 754 semantics. *)
val float_repr_eq_ieee754 : float_repr -> float_repr -> bool

(* Bit-for-bit float equality (ignores IEEE 754 NaN semantics) *)
val float_repr_eq_bits : float_repr -> float_repr -> bool

(** ----------------------------------------------------------------------------
    Float operations with result type
    ---------------------------------------------------------------------------- *)

(* Float addition with NaN/Infinity propagation *)
val float_add : float_repr -> float_repr -> prim_result float_repr

(* Float subtraction with NaN/Infinity propagation *)
val float_sub : float_repr -> float_repr -> prim_result float_repr

(* Float multiplication with NaN/Infinity propagation *)
val float_mul : float_repr -> float_repr -> prim_result float_repr

(* Float division with NaN/Infinity/DivByZero handling *)
val float_div : float_repr -> float_repr -> prim_result float_repr

(* Float negation - preserves NaN *)
val float_neg : float_repr -> prim_result float_repr

(* Float absolute value - preserves NaN *)
val float_abs : float_repr -> prim_result float_repr

(* Float square root - NaN for negative input *)
val float_sqrt : float_repr -> prim_result float_repr

(* Fused multiply-add: x * y + z with single rounding.
   IEEE 754-2008 fusedMultiplyAdd computes (x * y) + z as if with infinite
   intermediate precision, rounding only once at the end.
   NaN propagation: if any operand is NaN, the result is NaN. *)
val float_fma : float_repr -> float_repr -> float_repr -> prim_result float_repr

(** ----------------------------------------------------------------------------
    NaN propagation lemmas
    ---------------------------------------------------------------------------- *)

(* NaN input produces NaN output for binary operations *)
val float_add_nan_prop : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 x \/ is_nan_f64 y)
          (ensures PrimNaN? (float_add x y))
    [SMTPat (float_add x y)]

val float_sub_nan_prop : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 x \/ is_nan_f64 y)
          (ensures PrimNaN? (float_sub x y))
    [SMTPat (float_sub x y)]

val float_mul_nan_prop : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 x \/ is_nan_f64 y)
          (ensures PrimNaN? (float_mul x y))
    [SMTPat (float_mul x y)]

val float_div_nan_prop : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 x \/ is_nan_f64 y)
          (ensures PrimNaN? (float_div x y))
    [SMTPat (float_div x y)]

(* NaN input produces NaN output for unary operations *)
val float_neg_nan_prop : x:float_repr ->
    Lemma (requires is_nan_f64 x)
          (ensures PrimNaN? (float_neg x))
    [SMTPat (float_neg x)]

val float_sqrt_nan_prop : x:float_repr ->
    Lemma (requires is_nan_f64 x)
          (ensures PrimNaN? (float_sqrt x))
    [SMTPat (float_sqrt x)]

val float_fma_nan_prop : x:float_repr -> y:float_repr -> z:float_repr ->
    Lemma (requires is_nan_f64 x \/ is_nan_f64 y \/ is_nan_f64 z)
          (ensures PrimNaN? (float_fma x y z))
    [SMTPat (float_fma x y z)]

(** ----------------------------------------------------------------------------
    Infinity handling lemmas
    ---------------------------------------------------------------------------- *)

(* Infinity + finite = Infinity (same sign) *)
val float_add_infinity_finite : x:float_repr -> y:float_repr ->
    Lemma (requires is_infinity_f64 x /\ is_normal_f64 y)
          (ensures (match float_add x y with
                   | PrimSuccess r -> is_infinity_f64 r
                   | _ -> False))

(* Infinity + Infinity (same sign) = Infinity *)
val float_add_infinity_same_sign : x:float_repr -> y:float_repr ->
    Lemma (requires is_pos_infinity_f64 x /\ is_pos_infinity_f64 y)
          (ensures (match float_add x y with
                   | PrimSuccess r -> is_pos_infinity_f64 r
                   | _ -> False))

(* Infinity - Infinity (same sign) = NaN *)
val float_sub_infinity_same : x:float_repr -> y:float_repr ->
    Lemma (requires (is_pos_infinity_f64 x /\ is_pos_infinity_f64 y) \/
                    (is_neg_infinity_f64 x /\ is_neg_infinity_f64 y))
          (ensures PrimNaN? (float_sub x y))

(* 0 / 0 = NaN *)
val float_div_zero_zero : unit -> Lemma (PrimNaN? (float_div pos_zero_f64 pos_zero_f64))

(* finite / 0 = Infinity *)
val float_div_finite_zero : x:float_repr ->
    Lemma (requires is_normal_f64 x)
          (ensures PrimInfinity? (float_div x pos_zero_f64))

(** ----------------------------------------------------------------------------
    Float comparison operations (IEEE 754 semantics)
    ---------------------------------------------------------------------------- *)

(* Float less than - NaN comparisons are always false *)
val float_lt : float_repr -> float_repr -> bool

(* Float less than or equal *)
val float_le : float_repr -> float_repr -> bool

(* Float greater than *)
val float_gt : float_repr -> float_repr -> bool

(* Float greater than or equal *)
val float_ge : float_repr -> float_repr -> bool

(* Float comparison lemmas for NaN *)
val float_lt_nan : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 x \/ is_nan_f64 y)
          (ensures float_lt x y = false)

val float_le_nan : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 x \/ is_nan_f64 y)
          (ensures float_le x y = false)

(** ============================================================================
    BASE VALUES
    ============================================================================ *)

noeq type base_val =
  | VUnit   : base_val
  | VBool   : bool -> base_val
  | VInt    : int -> base_val
  | VFloat  : float_repr -> base_val
  | VString : string -> base_val
  | VChar   : nat -> base_val

(* IEEE 754 compliant value equality.
   Float comparison: NaN != NaN *)
val base_val_eq : base_val -> base_val -> bool

(* Bit-for-bit value equality.
   Float comparison: uses bit representation directly *)
val base_val_eq_bits : base_val -> base_val -> bool

(* Value equality lemma for NaN floats *)
val base_val_eq_nan : f:float_repr ->
    Lemma (requires is_nan_f64 f)
          (ensures base_val_eq (VFloat f) (VFloat f) = false)

(** ============================================================================
    STRING OPERATIONS
    ============================================================================ *)

type string_id = nat
type symbol = string_id

(* Maximum string length for bounded operations *)
val max_string_length : nat

(* String concatenation with length checking *)
val string_concat : string -> string -> prim_result string

(* String length - always succeeds *)
val string_length : string -> nat

(* String substring with bounds checking *)
val string_substring : s:string -> start:nat -> len:nat -> prim_result string

(* String character access with bounds checking *)
val string_char_at : s:string -> idx:nat -> prim_result nat

(* String concatenation succeeds if result length is within bounds *)
val string_concat_spec : s1:string -> s2:string ->
    Lemma (match string_concat s1 s2 with
           | PrimSuccess r -> string_length r = string_length s1 + string_length s2
           | PrimOverflow -> string_length s1 + string_length s2 > max_string_length
           | _ -> False)
    [SMTPat (string_concat s1 s2)]

(* Substring bounds checking *)
val string_substring_spec : s:string -> start:nat -> len:nat ->
    Lemma (match string_substring s start len with
           | PrimSuccess r -> start + len <= string_length s /\ string_length r = len
           | PrimOverflow -> start + len > string_length s
           | _ -> False)
    [SMTPat (string_substring s start len)]

(** ============================================================================
    SOURCE SPANS
    ============================================================================ *)

type file_id = nat
type byte_offset = nat

type span = {
  file  : file_id;
  start : byte_offset;
  end_  : byte_offset
}

val empty_span : span
val span_union : span -> span -> span

(* Span validity - end >= start *)
val span_valid : span -> bool

val span_union_valid : s1:span -> s2:span ->
    Lemma (requires span_valid s1 /\ span_valid s2 /\ s1.file = s2.file)
          (ensures span_valid (span_union s1 s2))

(** ============================================================================
    TYPE COERCION SPECIFICATIONS
    ============================================================================ *)

(* Safe widening coercion - no overflow possible *)
val int_widen : src:bounded_int_type -> dst:bounded_int_type ->
    v:range_t src ->
    Pure (range_t dst)
         (requires width_leq src.width dst.width /\
                   (src.sign = Unsigned \/ dst.sign = Signed \/
                    (src.sign = Signed /\ dst.sign = Signed)))
         (ensures fun r -> True)

(* Truncating coercion - may lose precision *)
val int_truncate : src:bounded_int_type -> dst:bounded_int_type -> int -> range_t dst

(* Truncation wraps like modular arithmetic *)
val int_truncate_spec : src:bounded_int_type -> dst:bounded_int_type -> v:int ->
    Lemma (int_truncate src dst v = v @%. dst)
    [SMTPat (int_truncate src dst v)]

(* Float to int conversion - may overflow or truncate *)
val float_to_int : it:bounded_int_type -> float_repr -> prim_result int

(* Int to float conversion - may lose precision for large values *)
val int_to_float : prec:float_prec -> int -> float_repr

val float_to_int_nan : it:bounded_int_type -> f:float_repr ->
    Lemma (requires is_nan_f64 f)
          (ensures PrimNaN? (float_to_int it f))

val float_to_int_infinity : it:bounded_int_type -> f:float_repr ->
    Lemma (requires is_infinity_f64 f)
          (ensures PrimOverflow? (float_to_int it f))

(** ============================================================================
    PRIMITIVE OPERATION SOUNDNESS PROOFS
    ============================================================================

    Following HACL* patterns from:
    - /home/grigory/Downloads/hacl-star/lib/Lib.IntTypes.fst (integer operations)
    - /home/grigory/Downloads/hacl-star/lib/Lib.NatMod.fst (algebraic properties)

    These proofs establish:
    1. Correctness: Operations produce expected results
    2. Algebraic properties: Commutativity, associativity
    3. Error handling: Division by zero, overflow, NaN propagation
    ============================================================================ *)

(** ----------------------------------------------------------------------------
    Integer Addition Soundness
    ---------------------------------------------------------------------------- *)

(* Addition correctness: result equals mathematical sum when no overflow *)
val int_add_correct : it:bounded_int_type -> x:int -> y:int ->
    Lemma (ensures (match int_add_result it x y with
                   | PrimSuccess z -> z == x + y /\
                                      z >= int_min_bounded it /\
                                      z <= int_max_bounded it
                   | PrimOverflow -> x + y < int_min_bounded it \/
                                    x + y > int_max_bounded it
                   | _ -> False))

(* Addition commutativity: x + y == y + x *)
val int_add_comm : it:bounded_int_type -> x:int -> y:int ->
    Lemma (ensures int_add_result it x y == int_add_result it y x)

(* Addition commutativity for wrapping arithmetic *)
val add_wrap_comm : it:bounded_int_type -> x:int -> y:int ->
    Lemma (ensures add_wrap it x y == add_wrap it y x)

(* Addition commutativity for checked arithmetic *)
val add_checked_comm : it:bounded_int_type -> x:int -> y:int ->
    Lemma (ensures add_checked it x y == add_checked it y x)

(* Addition associativity for wrapping arithmetic *)
val add_wrap_assoc : it:bounded_int_type -> x:int -> y:int -> z:int ->
    Lemma (ensures add_wrap it (add_wrap it x y) z ==
                   add_wrap it x (add_wrap it y z))

(* Addition associativity for checked arithmetic (when no overflow at each step) *)
val add_checked_assoc : it:bounded_int_type -> x:int -> y:int -> z:int ->
    Lemma (requires Some? (add_checked it x y) /\
                    Some? (add_checked it (Some?.v (add_checked it x y)) z) /\
                    Some? (add_checked it y z) /\
                    Some? (add_checked it x (Some?.v (add_checked it y z))))
          (ensures add_checked it (Some?.v (add_checked it x y)) z ==
                   add_checked it x (Some?.v (add_checked it y z)))

(** ----------------------------------------------------------------------------
    Integer Subtraction Soundness
    ---------------------------------------------------------------------------- *)

(* Subtraction correctness *)
val int_sub_correct : it:bounded_int_type -> x:int -> y:int ->
    Lemma (ensures (match int_sub_result it x y with
                   | PrimSuccess z -> z == x - y /\
                                      z >= int_min_bounded it /\
                                      z <= int_max_bounded it
                   | PrimOverflow -> x - y < int_min_bounded it \/
                                    x - y > int_max_bounded it
                   | _ -> False))

(* Subtraction anti-commutativity: x - y == -(y - x) *)
val int_sub_anti_comm : it:bounded_int_type -> x:int -> y:int ->
    Lemma (ensures (x - y) == -(y - x))

(** ----------------------------------------------------------------------------
    Integer Multiplication Soundness
    ---------------------------------------------------------------------------- *)

(* Multiplication correctness *)
val int_mul_correct : it:bounded_int_type -> x:int -> y:int ->
    Lemma (ensures (match int_mul_result it x y with
                   | PrimSuccess z -> z == x * y /\
                                      z >= int_min_bounded it /\
                                      z <= int_max_bounded it
                   | PrimOverflow -> x * y < int_min_bounded it \/
                                    x * y > int_max_bounded it
                   | _ -> False))

(* Multiplication commutativity *)
val int_mul_comm : it:bounded_int_type -> x:int -> y:int ->
    Lemma (ensures int_mul_result it x y == int_mul_result it y x)

(* Multiplication commutativity for wrapping arithmetic *)
val mul_wrap_comm : it:bounded_int_type -> x:int -> y:int ->
    Lemma (ensures mul_wrap it x y == mul_wrap it y x)

(* Multiplication by zero *)
val int_mul_zero_left : it:bounded_int_type -> x:int ->
    Lemma (ensures PrimSuccess? (int_mul_result it 0 x))

val int_mul_zero_right : it:bounded_int_type -> x:int ->
    Lemma (ensures PrimSuccess? (int_mul_result it x 0))

(* Multiplication by one *)
val int_mul_one_left : it:bounded_int_type -> x:range_t it ->
    Lemma (ensures PrimSuccess? (int_mul_result it 1 x))

val int_mul_one_right : it:bounded_int_type -> x:range_t it ->
    Lemma (ensures PrimSuccess? (int_mul_result it x 1))

(* Multiplication overflow detection - enhanced specification *)
val mul_overflow_bounds : it:bounded_int_type -> x:int -> y:int ->
    Lemma (ensures will_overflow_mul it x y <==>
                   (let p = x * y in
                    p < int_min_bounded it \/ p > int_max_bounded it))

(* Unsigned multiplication overflow: only positive overflow possible *)
val unsigned_mul_overflow : it:bounded_int_type{it.sign = Unsigned} -> x:nat -> y:nat ->
    Lemma (ensures will_overflow_mul it x y <==>
                   x * y > int_max_bounded it)

(** ----------------------------------------------------------------------------
    Integer Division Soundness
    ---------------------------------------------------------------------------- *)

(* Division by zero produces PrimDivByZero *)
val int_div_zero : it:bounded_int_type -> x:int ->
    Lemma (ensures PrimDivByZero? (int_div_result it x 0))

(* Division by non-zero succeeds (unless signed overflow) *)
val int_div_nonzero : it:bounded_int_type -> x:int -> d:int{d <> 0} ->
    Lemma (ensures (match int_div_result it x d with
                   | PrimDivByZero -> False
                   | PrimOverflow -> it.sign = Signed /\
                                    x = int_min_bounded it /\ d = -1
                   | PrimSuccess _ -> True))

(* Unsigned division never overflows *)
val unsigned_div_no_overflow : it:bounded_int_type{it.sign = Unsigned} ->
                               x:range_t it -> d:int{d <> 0 /\ d > 0} ->
    Lemma (ensures PrimSuccess? (int_div_result it x d))

(* Division quotient bounds *)
val int_div_bounds : it:bounded_int_type -> x:range_t it -> d:int{d <> 0} ->
    Lemma (requires ~(will_overflow_div it x d))
          (ensures (match int_div_result it x d with
                   | PrimSuccess q -> q >= int_min_bounded it /\
                                     q <= int_max_bounded it
                   | _ -> False))

(** ----------------------------------------------------------------------------
    Integer Modulo Soundness
    ---------------------------------------------------------------------------- *)

(* Modulo by zero produces PrimDivByZero *)
val int_mod_zero : it:bounded_int_type -> x:int ->
    Lemma (ensures PrimDivByZero? (int_mod_result it x 0))

(* Modulo by non-zero always succeeds *)
val int_mod_nonzero : it:bounded_int_type -> x:int -> d:int{d <> 0} ->
    Lemma (ensures PrimSuccess? (int_mod_result it x d))

(** ----------------------------------------------------------------------------
    Float NaN Propagation Soundness
    ---------------------------------------------------------------------------- *)

(* NaN on left operand produces NaN *)
val float_add_nan_left : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 x)
          (ensures PrimNaN? (float_add x y))

(* NaN on right operand produces NaN *)
val float_add_nan_right : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 y)
          (ensures PrimNaN? (float_add x y))

(* NaN propagation for subtraction *)
val float_sub_nan_left : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 x)
          (ensures PrimNaN? (float_sub x y))

val float_sub_nan_right : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 y)
          (ensures PrimNaN? (float_sub x y))

(* NaN propagation for multiplication *)
val float_mul_nan_left : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 x)
          (ensures PrimNaN? (float_mul x y))

val float_mul_nan_right : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 y)
          (ensures PrimNaN? (float_mul x y))

(* NaN propagation for division *)
val float_div_nan_left : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 x)
          (ensures PrimNaN? (float_div x y))

val float_div_nan_right : x:float_repr -> y:float_repr ->
    Lemma (requires is_nan_f64 y)
          (ensures PrimNaN? (float_div x y))

(** ----------------------------------------------------------------------------
    Float Infinity Soundness
    ---------------------------------------------------------------------------- *)

(* Infinity + (-Infinity) = NaN *)
val float_add_opposite_infinity : x:float_repr -> y:float_repr ->
    Lemma (requires (is_pos_infinity_f64 x /\ is_neg_infinity_f64 y) \/
                    (is_neg_infinity_f64 x /\ is_pos_infinity_f64 y))
          (ensures PrimNaN? (float_add x y))

(* 0 * Infinity = NaN *)
val float_mul_zero_infinity : x:float_repr -> y:float_repr ->
    Lemma (requires (is_zero_f64 x /\ is_infinity_f64 y) \/
                    (is_infinity_f64 x /\ is_zero_f64 y))
          (ensures PrimNaN? (float_mul x y))

(* Infinity / Infinity = NaN *)
val float_div_infinity_infinity : x:float_repr -> y:float_repr ->
    Lemma (requires is_infinity_f64 x /\ is_infinity_f64 y)
          (ensures PrimNaN? (float_div x y))

(** ----------------------------------------------------------------------------
    Negation Soundness
    ---------------------------------------------------------------------------- *)

(* Double negation returns original value (for wrapping) *)
val neg_wrap_involutive : it:bounded_int_type -> x:int ->
    Lemma (ensures neg_wrap it (neg_wrap it x) == x @%. it)

(* Negation of zero is zero *)
val neg_wrap_zero : it:bounded_int_type ->
    Lemma (ensures neg_wrap it 0 == 0)

(** ----------------------------------------------------------------------------
    Modular Arithmetic Properties
    ---------------------------------------------------------------------------- *)

(* Modular reduction is idempotent *)
val mod_idempotent : it:bounded_int_type -> x:int ->
    Lemma (ensures (x @%. it) @%. it == x @%. it)

(* Values in range are unchanged by modular reduction *)
val mod_identity : it:bounded_int_type -> x:range_t it ->
    Lemma (ensures x @%. it == x)

(** ----------------------------------------------------------------------------
    Bitwise Operation Soundness
    ---------------------------------------------------------------------------- *)

(* Bitwise AND is commutative *)
val bit_and_comm : it:bounded_int_type -> x:range_t it -> y:range_t it ->
    Lemma (ensures bit_and it x y == bit_and it y x)

(* Bitwise OR is commutative *)
val bit_or_comm : it:bounded_int_type -> x:range_t it -> y:range_t it ->
    Lemma (ensures bit_or it x y == bit_or it y x)

(* Bitwise XOR is commutative *)
val bit_xor_comm : it:bounded_int_type -> x:range_t it -> y:range_t it ->
    Lemma (ensures bit_xor it x y == bit_xor it y x)

(* Shift left by zero is identity *)
val shift_left_zero : it:bounded_int_type -> x:range_t it ->
    Lemma (ensures shift_left it x 0 == x @%. it)

(* Shift right by zero is identity *)
val shift_right_zero : it:bounded_int_type -> x:range_t it ->
    Lemma (ensures shift_right it x 0 == x)
