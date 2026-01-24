(**
 * BrrrLang.Core.Primitives - Interface
 *
 * Foundational primitive types with overflow specifications.
 * Based on brrr_lang_spec_v0.4.tex Part II.
 *
 * Following HACL* Lib.IntTypes patterns for:
 * - Refinement types with range checking
 * - Bounded integer operations with overflow detection
 * - Modular arithmetic specifications
 * - Compile-time constant lemmas with SMTPat triggers
 *
 * Reference: /home/grigory/Downloads/hacl-star/lib/Lib.IntTypes.fsti
 *)
module Primitives

open FStar.Mul

(* Z3 solver options for consistent proof behavior - following HACL* pattern *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** ============================================================================
    PRIMITIVE OPERATION RESULT TYPE
    ============================================================================

    A unified result type for all primitive operations that can fail.
    This enables precise specification of failure modes and correct
    propagation of error conditions through computations.
    ============================================================================ *)

type prim_result (a:Type) =
  | PrimSuccess   : v:a -> prim_result a
  | PrimOverflow  : prim_result a    (* Integer overflow/underflow *)
  | PrimDivByZero : prim_result a    (* Division by zero *)
  | PrimNaN       : prim_result a    (* NaN result from float operation *)
  | PrimInfinity  : prim_result a    (* Infinity result from float operation *)

(* Result predicates for use in lemmas *)
unfold let is_success #a (r: prim_result a) : bool =
  match r with | PrimSuccess _ -> true | _ -> false

unfold let get_success #a (r: prim_result a{is_success r}) : a =
  match r with | PrimSuccess v -> v

(** ============================================================================
    HELPER FUNCTIONS
    ============================================================================ *)

val max : nat -> nat -> nat
val min : nat -> nat -> nat

(** ============================================================================
    INTEGER TYPES
    ============================================================================ *)

(* Bit widths for integers *)
type int_width =
  | I8   : int_width
  | I16  : int_width
  | I32  : int_width
  | I64  : int_width
  | I128 : int_width
  | IBig : int_width  (* Arbitrary precision *)

(* Bounded width - excludes arbitrary precision, following HACL* refinement type pattern *)
unfold
let bounded_width = w:int_width{w <> IBig}

(* Signedness *)
type signedness =
  | Signed   : signedness
  | Unsigned : signedness

(* Integer type descriptor *)
type int_type = {
  width : int_width;
  sign  : signedness
}

(* Bounded integer type - has fixed bit width *)
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
   Following HACL* bits function pattern from Lib.IntTypes.fsti lines 55-69. *)
[@(strict_on_arguments [0])]
val width_bits_bounded : bounded_width -> nat

(* Bit width for any width - returns option for IBig *)
val width_bits : int_width -> option nat

(* Width ordering for type coercion *)
val width_leq : int_width -> int_width -> bool

(** ----------------------------------------------------------------------------
    Integer range operations (following HACL* minint/maxint pattern)
    ---------------------------------------------------------------------------- *)

(* Range for any type - returns option for IBig *)
val int_min : int_type -> option int
val int_max : int_type -> option int

(* Range for bounded types - always returns int (no option)
   Following HACL* pattern: minint/maxint from Lib.IntTypes.fsti lines 79-85 *)
val int_min_bounded : bounded_int_type -> int
val int_max_bounded : bounded_int_type -> int

(* Check if value is in range for bounded type
   Following HACL* range pattern from Lib.IntTypes.fsti lines 87-91 *)
val in_range : int -> bounded_int_type -> bool

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

val width_bits_8   : unit -> Lemma (width_bits_bounded I8 = 8)   [SMTPat (width_bits_bounded I8)]
val width_bits_16  : unit -> Lemma (width_bits_bounded I16 = 16) [SMTPat (width_bits_bounded I16)]
val width_bits_32  : unit -> Lemma (width_bits_bounded I32 = 32) [SMTPat (width_bits_bounded I32)]
val width_bits_64  : unit -> Lemma (width_bits_bounded I64 = 64) [SMTPat (width_bits_bounded I64)]
val width_bits_128 : unit -> Lemma (width_bits_bounded I128 = 128) [SMTPat (width_bits_bounded I128)]

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

    Following HACL* Lib.IntTypes patterns for modular arithmetic and overflow.
    These types and functions specify how integer arithmetic overflow is handled,
    matching Rust's Wrapping<T>, Saturating<T>, and checked_* operations.

    Reference: Lib.IntTypes.fsti lines 416-476 for add_mod, mul_mod, etc.
    ============================================================================ *)

(** ----------------------------------------------------------------------------
    Overflow behavior modes
    ---------------------------------------------------------------------------- *)

(* Overflow behavior modes - matching Rust semantics *)
type overflow_behavior =
  | OBWrap      (* Wrapping arithmetic - like Rust Wrapping<T> *)
  | OBSaturate  (* Saturating arithmetic - clamp to min/max *)
  | OBChecked   (* Checked arithmetic - return option *)
  | OBPanic     (* Panic on overflow - like Rust default debug mode *)

(** ----------------------------------------------------------------------------
    Modulus function (following HACL* Lib.IntTypes.fsti line 75 pattern)
    ---------------------------------------------------------------------------- *)

(* Modulus for bounded integer types: 2^bits
   Following HACL* pattern: let modulus (t:inttype) = pow2 (bits t) *)
[@(strict_on_arguments [0])]
val modulus : bounded_width -> pos

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
   Following HACL* Lib.IntTypes.fsti lines 336-338:
   let op_At_Percent_Dot x t =
     if unsigned t then x % modulus t
     else FStar.Int.(x @% modulus t) *)
[@(strict_on_arguments [1])]
val op_At_Percent_Dot : int -> bounded_int_type -> int

(** ----------------------------------------------------------------------------
    Overflow detection predicates
    ---------------------------------------------------------------------------- *)

(* Check if addition will overflow for a given integer type *)
val will_overflow_add : bounded_int_type -> int -> int -> bool

(* Check if subtraction will overflow for a given integer type *)
val will_overflow_sub : bounded_int_type -> int -> int -> bool

(* Check if multiplication will overflow for a given integer type *)
val will_overflow_mul : bounded_int_type -> int -> int -> bool

(* Check if division will overflow (only for INT_MIN / -1 in signed types) *)
val will_overflow_div : bounded_int_type -> int -> d:int{d <> 0} -> bool

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

    IEEE 754 floating point representation (64-bit double precision):
    - Sign bit: bit 63
    - Exponent: bits 52-62 (11 bits, biased by 1023)
    - Mantissa: bits 0-51 (52 bits)

    Special values:
    - Infinity: exponent = 0x7FF (2047), mantissa = 0
    - NaN: exponent = 0x7FF (2047), mantissa != 0
    - Zero: exponent = 0, mantissa = 0 (positive or negative)
    - Subnormal: exponent = 0, mantissa != 0

    CRITICAL: NaN != NaN in IEEE 754. Any comparison involving NaN
    returns false (except !=, which returns true).
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

(** ----------------------------------------------------------------------------
    Infinity handling lemmas
    ---------------------------------------------------------------------------- *)

(* Infinity + finite = Infinity (same sign) *)
val float_add_infinity_finite : x:float_repr -> y:float_repr ->
    Lemma (requires is_infinity_f64 x /\ is_normal_f64 y)
          (ensures match float_add x y with
                   | PrimSuccess r -> is_infinity_f64 r
                   | _ -> False)

(* Infinity + Infinity (same sign) = Infinity *)
val float_add_infinity_same_sign : x:float_repr -> y:float_repr ->
    Lemma (requires is_pos_infinity_f64 x /\ is_pos_infinity_f64 y)
          (ensures match float_add x y with
                   | PrimSuccess r -> is_pos_infinity_f64 r
                   | _ -> False)

(* Infinity - Infinity (same sign) = NaN *)
val float_sub_infinity_same : x:float_repr -> y:float_repr ->
    Lemma (requires (is_pos_infinity_f64 x /\ is_pos_infinity_f64 y) \/
                    (is_neg_infinity_f64 x /\ is_neg_infinity_f64 y))
          (ensures PrimNaN? (float_sub x y))

(* 0 / 0 = NaN *)
val float_div_zero_zero :
    Lemma (PrimNaN? (float_div pos_zero_f64 pos_zero_f64))

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
    Lemma (ensures match int_add_result it x y with
                   | PrimSuccess z -> z == x + y /\
                                      z >= int_min_bounded it /\
                                      z <= int_max_bounded it
                   | PrimOverflow -> x + y < int_min_bounded it \/
                                    x + y > int_max_bounded it
                   | _ -> False)

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
    Lemma (ensures match int_sub_result it x y with
                   | PrimSuccess z -> z == x - y /\
                                      z >= int_min_bounded it /\
                                      z <= int_max_bounded it
                   | PrimOverflow -> x - y < int_min_bounded it \/
                                    x - y > int_max_bounded it
                   | _ -> False)

(* Subtraction anti-commutativity: x - y == -(y - x) *)
val int_sub_anti_comm : it:bounded_int_type -> x:int -> y:int ->
    Lemma (ensures (x - y) == -(y - x))

(** ----------------------------------------------------------------------------
    Integer Multiplication Soundness
    ---------------------------------------------------------------------------- *)

(* Multiplication correctness *)
val int_mul_correct : it:bounded_int_type -> x:int -> y:int ->
    Lemma (ensures match int_mul_result it x y with
                   | PrimSuccess z -> z == x * y /\
                                      z >= int_min_bounded it /\
                                      z <= int_max_bounded it
                   | PrimOverflow -> x * y < int_min_bounded it \/
                                    x * y > int_max_bounded it
                   | _ -> False)

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
    Lemma (ensures match int_div_result it x d with
                   | PrimDivByZero -> False
                   | PrimOverflow -> it.sign = Signed /\
                                    x = int_min_bounded it /\ d = -1
                   | PrimSuccess _ -> True)

(* Unsigned division never overflows *)
val unsigned_div_no_overflow : it:bounded_int_type{it.sign = Unsigned} ->
                               x:range_t it -> d:int{d <> 0 /\ d > 0} ->
    Lemma (ensures PrimSuccess? (int_div_result it x d))

(* Division quotient bounds *)
val int_div_bounds : it:bounded_int_type -> x:range_t it -> d:int{d <> 0} ->
    Lemma (requires ~(will_overflow_div it x d))
          (ensures match int_div_result it x d with
                   | PrimSuccess q -> q >= int_min_bounded it /\
                                     q <= int_max_bounded it
                   | _ -> False)

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
