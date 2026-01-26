(**
 * Primitives.Theorems.fst - Formal Theorems for Integer Arithmetic
 *
 * This module collects and documents provable theorems about primitive
 * integer operations from AXIOMS_REPORT_v2.md Part III. Each theorem
 * can and must be proven from definitions - they are NOT axioms.
 *
 * THEOREM IDENTIFIERS (from AXIOMS_REPORT_v2.md):
 *   T-2.10: mod_identity           (P2, 2-4 hours) - Modular identity for in-range values
 *   T-3.6:  neg_wrap_involutive    (P3, 3-5 hours) - Wrapped negation is involutive
 *   T-4.3:  div_checked_correct    (P4, 4-6 hours) - Checked division correctness
 *   T-4.4:  int_div_result_spec    (P4, 4-6 hours) - Integer division result bounds
 *
 * EDGE CASES AND CRITICAL CONCERNS:
 *   - Signed vs unsigned arithmetic semantics differ fundamentally
 *   - MIN_INT / -1 causes signed overflow (undefined in C, wraps in some languages)
 *   - Two's complement representation: -MIN_INT == MIN_INT for fixed-width signed
 *   - FStar.Int.op_At_Percent semantics differ from F* built-in % for negatives
 *   - Modular reduction for signed types uses centered representation [-m/2, m/2-1]
 *
 * LITERATURE REFERENCES:
 *   - HACL* Lib.IntTypes.fst: Modular arithmetic patterns, overflow handling
 *   - HACL* Lib.NatMod.fst: Algebraic properties of modular operations
 *   - FStar.Math.Lemmas: Core modular arithmetic lemmas (small_mod, lemma_mod_lt)
 *   - C11 Standard 6.5.5: Division and remainder behavior
 *   - Rust Reference: Wrapping<T> semantics, checked_* methods
 *
 * Classification: DeferredProof (provable but requires mechanization effort)
 *
 * @author brrr-lang team
 * @version 2.0
 * @since 2026-01-26
 *)
module Primitives.Theorems

open FStar.Mul
open FStar.Math.Lemmas
open Primitives

(* Z3 configuration matching Primitives.fst for consistent proof behavior *)
#set-options "--z3rlimit 100 --fuel 1 --ifuel 1"


(** ============================================================================
    PRIORITY 2: MEDIUM EFFORT (2-6 hours each)
    ============================================================================
    These theorems require careful reasoning about modular arithmetic semantics
    and the distinction between signed and unsigned representations.
    ============================================================================ *)

(**
 * T-2.10: Modular Identity for In-Range Values
 *
 * When a value x is already within the representable range [0, n) for unsigned
 * or [-(n/2), n/2-1] for signed, modular reduction is the identity.
 *
 * Mathematical Statement (unsigned):
 *   forall x n. 0 <= x < n ==> x % n == x
 *
 * Mathematical Statement (signed, two's complement):
 *   forall x m. -(m/2) <= x < m/2 ==> x @% m == x
 *
 * Location: Primitives.fst:1334-1348
 * Effort: 2-4 hours
 * Proof Strategy:
 *   - Unsigned case: Direct application of FStar.Math.Lemmas.small_mod
 *   - Signed case: Requires reasoning about FStar.Int.op_At_Percent semantics
 *     and the centered representation used for signed modular reduction.
 *     The key insight is that for x in [-(m/2), m/2-1], the adjustment by m
 *     (if x < 0) results in a value in [0, m-1], and subtracting m when
 *     result >= m/2 brings it back to x.
 *
 * Edge Cases to Handle:
 *   - x = 0: Both signed and unsigned identity trivial
 *   - x = n-1 (unsigned max): Must show (n-1) % n == n-1
 *   - x = -(m/2) (signed min): Critical - this is MIN_INT
 *   - x = m/2 - 1 (signed max): Must show identity holds
 *
 * Dependencies:
 *   - FStar.Math.Lemmas.small_mod: a:nat -> n:pos -> Lemma (requires a < n) (ensures a % n == a)
 *   - FStar.Math.Lemmas.modulo_range_lemma: For bound checking
 *
 * Classification: DeferredProof
 *)
val theorem_mod_identity_unsigned : x:nat -> n:pos ->
  Lemma (requires x < n)
        (ensures x % n == x)

let theorem_mod_identity_unsigned x n =
  (* Unsigned case: Direct application of FStar.Math.Lemmas.small_mod
   * small_mod states: a < n ==> a % n == a
   * This is the definition of modular reduction for in-range values.
   *
   * Proof is trivial - Z3 can discharge this automatically with the library lemma.
   *)
  FStar.Math.Lemmas.small_mod x n


(**
 * T-2.10 (continued): Modular Identity for Bounded Integer Types
 *
 * Generalization to bounded_int_type using the @%. operator.
 * For any value x in the representable range of type it, x @%. it == x.
 *
 * This connects the mathematical property to the actual brrr-lang types.
 *)
val theorem_mod_identity_bounded : it:bounded_int_type -> x:range_t it ->
  Lemma (ensures x @%. it == x)

let theorem_mod_identity_bounded it x =
  (* DeferredProof: Modular identity for bounded integer types
   *
   * For the unsigned case:
   *   - range_t it = [0, 2^bits - 1]
   *   - modulus it.width = 2^bits
   *   - x @%. it = x % modulus = x (by small_mod, since x < modulus)
   *
   * For the signed case:
   *   - range_t it = [-(2^(bits-1)), 2^(bits-1) - 1]
   *   - FStar.Int.op_At_Percent implements centered modular reduction
   *   - For x in this range, op_At_Percent returns x unchanged
   *
   * The signed case is non-trivial because op_At_Percent has the semantics:
   *   let r = x % m in
   *   if r >= m/2 then r - m else if r < -m/2 then r + m else r
   *
   * For x in [-(m/2), m/2 - 1]:
   *   - If x >= 0: x % m = x (by small_mod), and x < m/2, so result = x
   *   - If x < 0: x % m may be x + m (F* definition), need careful case analysis
   *
   * Key insight: The signed range is designed to match op_At_Percent's fixed point.
   *
   * Estimated effort: 2-4 hours for full proof
   *)
  admit ()


(** ============================================================================
    PRIORITY 3: SUBSTANTIAL EFFORT (3-8 hours each)
    ============================================================================
    These theorems require careful treatment of modular arithmetic properties
    including involutivity and edge cases at type boundaries.
    ============================================================================ *)

(**
 * T-3.6: Wrapped Negation is Involutive
 *
 * For wrapping arithmetic, negating twice returns the original value
 * (after modular reduction).
 *
 * Mathematical Statement:
 *   neg_wrap it (neg_wrap it x) == x @%. it
 *
 * This says: -(-x mod m) mod m == x mod m
 *
 * Location: Primitives.fst:1292-1307
 * Effort: 3-5 hours
 * Proof Strategy:
 *   - Unsigned case: Use FStar.Math.Lemmas.lemma_mod_sub twice
 *     Show that (0 - ((0 - x) % m)) % m == x % m
 *   - Signed case: Requires reasoning about FStar.Int.op_At_Percent
 *     The key insight is that negation in a modular group is its own inverse:
 *     In Z_m, -(-x) = x because negation is the additive inverse operation.
 *
 * Edge Cases to Handle:
 *   - x = 0: -(-0) = -0 = 0 (trivial)
 *   - x = MIN_INT (signed): -MIN_INT == MIN_INT in two's complement!
 *     This is the critical edge case where -x overflows to x.
 *     The theorem holds because MIN_INT @%. it == MIN_INT, and
 *     neg_wrap it MIN_INT == MIN_INT @%. it == MIN_INT.
 *   - x = MAX_INT (unsigned): -(-(2^n - 1) % 2^n) % 2^n
 *     = -((2^n - (2^n - 1)) % 2^n) % 2^n = -(1 % 2^n) % 2^n = -1 % 2^n = 2^n - 1
 *
 * Critical Note on MIN_INT:
 *   For signed types, MIN_INT = -(2^(bits-1)).
 *   In two's complement: -MIN_INT = MIN_INT (because MIN_INT + MIN_INT = 0 mod 2^bits)
 *   This means neg_wrap it MIN_INT = (0 - MIN_INT) @%. it = MIN_INT @%. it
 *   And neg_wrap it (neg_wrap it MIN_INT) = neg_wrap it MIN_INT = MIN_INT @%. it
 *   So the theorem holds even at this boundary.
 *
 * Dependencies:
 *   - FStar.Math.Lemmas.lemma_mod_sub: (a - b) % n properties
 *   - Modular group theory: Negation is involutive in Z_m
 *
 * Classification: DeferredProof
 *)
val theorem_neg_wrap_involutive : it:bounded_int_type -> x:int ->
  Lemma (ensures neg_wrap it (neg_wrap it x) == x @%. it)

let theorem_neg_wrap_involutive it x =
  (* DeferredProof: Wrapped negation involutivity
   *
   * For unsigned types:
   *   neg_wrap it x = (0 - x) @%. it = (0 - x) % m  where m = modulus it.width
   *   neg_wrap it (neg_wrap it x) = (0 - ((0 - x) % m)) % m
   *
   *   Let y = (0 - x) % m = (m - (x % m)) % m  when x >= 0
   *                       = (m - ((x % m + m) % m)) % m  when x < 0
   *
   *   The key lemma is:
   *     (m - ((m - (x % m)) % m)) % m == x % m
   *
   *   Proof sketch:
   *   - Let r = x % m, so 0 <= r < m
   *   - (m - r) % m = m - r when r > 0, = 0 when r = 0
   *   - (m - (m - r)) % m = r % m = r when r > 0
   *   - For r = 0: (m - 0) % m = 0 = r
   *
   * For signed types:
   *   The proof is more complex due to op_At_Percent semantics.
   *   The mathematical truth is that negation is involutive in any group,
   *   and the signed integers modulo m form a group under addition.
   *
   * The Primitives.fst implementation has:
   *   - Unsigned case: proven using FStar.Math.Lemmas.lemma_mod_sub
   *   - Signed case: currently admits
   *
   * Estimated effort: 3-5 hours for complete proof
   *)
  admit ()


(**
 * T-3.6 (auxiliary): Double negation for values in range
 *
 * Special case: when x is already in range, double negation returns x.
 *)
val theorem_neg_wrap_involutive_in_range : it:bounded_int_type -> x:range_t it ->
  Lemma (ensures neg_wrap it (neg_wrap it x) == x)

let theorem_neg_wrap_involutive_in_range it x =
  (* This follows from theorem_neg_wrap_involutive and theorem_mod_identity_bounded:
   *   neg_wrap it (neg_wrap it x) == x @%. it == x
   *
   * The second equality uses theorem_mod_identity_bounded since x is range_t it.
   *)
  theorem_neg_wrap_involutive it x;
  theorem_mod_identity_bounded it x;
  admit () (* Need to connect the two results *)


(** ============================================================================
    PRIORITY 4: HIGH EFFORT (4-16 hours each)
    ============================================================================
    These theorems require complex case analysis involving division semantics,
    overflow conditions, and the subtle MIN_INT / -1 edge case.
    ============================================================================ *)

(**
 * T-4.3: Checked Division Correctness
 *
 * The div_checked function returns Some (x / y) when division is safe,
 * and None when division would fail (divide by zero) or overflow
 * (signed MIN_INT / -1).
 *
 * Mathematical Statement:
 *   div_checked it x y == Some r <==>
 *     y <> 0 /\ ~(will_overflow_div it x y) /\ r == div(x, y) /\ in_range r it
 *
 * Where div(x, y) is truncated division (towards zero), matching C/Rust semantics.
 *
 * Location: Primitives.fst:223-238, 421-426
 * Effort: 4-6 hours
 * Proof Strategy:
 *   Case 1: y = 0 -> div_checked returns None (division by zero)
 *   Case 2: y <> 0, unsigned type -> always succeeds (no overflow possible)
 *   Case 3: y <> 0, signed type:
 *     - If x = MIN_INT and y = -1 -> returns None (overflow)
 *     - Otherwise -> returns Some (truncated quotient)
 *
 * Edge Cases to Handle:
 *   - Division by zero: y = 0 must return None
 *   - Signed MIN_INT / -1: The only signed division that overflows
 *     MIN_INT = -(2^(bits-1)), and -MIN_INT = 2^(bits-1) > MAX_INT = 2^(bits-1) - 1
 *   - Unsigned division: x/y is always in [0, x] when x, y >= 0, so no overflow
 *   - Negative quotients (signed): Result is in range by truncation towards zero
 *
 * Truncated Division Semantics (C11 6.5.5, matching FStar.Int.op_Slash):
 *   - Quotient is truncated towards zero
 *   - (-7) / 3 = -2 (not -3)
 *   - 7 / (-3) = -2 (not -3)
 *   - (-7) / (-3) = 2
 *
 * Dependencies:
 *   - FStar.Int.op_Slash: Truncated division for signed integers
 *   - will_overflow_div: Overflow predicate for division
 *
 * Classification: DeferredProof
 *)
val theorem_div_checked_correct : it:bounded_int_type -> a:int -> b:int ->
  Lemma (ensures (match div_checked it a b with
                  | Some r -> b <> 0 /\ ~(will_overflow_div it a b) /\
                             r >= int_min_bounded it /\ r <= int_max_bounded it
                  | None -> b = 0 \/ will_overflow_div it a b))

let theorem_div_checked_correct it a b =
  (* DeferredProof: Checked division correctness
   *
   * Case analysis based on div_checked implementation:
   *
   * Case b = 0:
   *   div_checked it a 0 = None
   *   Postcondition: b = 0 \/ will_overflow_div it a b
   *   Satisfied by left disjunct.
   *
   * Case b <> 0, Unsigned type:
   *   div_checked computes a / b
   *   For a >= 0, b > 0: a / b in [0, a], which is in range
   *   Returns Some (a / b)
   *   will_overflow_div it a b = false for unsigned (by definition)
   *   Postcondition satisfied.
   *
   * Case b <> 0, Signed type:
   *   Sub-case a = MIN_INT and b = -1:
   *     div_checked returns None
   *     will_overflow_div it MIN_INT (-1) = true
   *     Postcondition: b = 0 \/ will_overflow_div it a b
   *     Satisfied by right disjunct.
   *
   *   Sub-case not (a = MIN_INT and b = -1):
   *     div_checked computes FStar.Int.op_Slash a b
   *     The quotient is truncated towards zero
   *     Result is in [MIN_INT, MAX_INT] because:
   *       - Maximum positive: MAX_INT / 1 = MAX_INT
   *       - Minimum negative: MIN_INT / 1 = MIN_INT
   *       - Division by larger number reduces magnitude
   *       - MIN_INT / -1 case is excluded above
   *     Returns Some (truncated quotient)
   *     Postcondition satisfied.
   *
   * Estimated effort: 4-6 hours for complete proof with all cases
   *)
  admit ()


(**
 * T-4.4: Integer Division Result Specification
 *
 * The int_div_result function provides precise error categorization:
 * - PrimDivByZero when divisor is zero
 * - PrimOverflow when signed MIN_INT / -1 would overflow
 * - PrimSuccess when division succeeds
 *
 * Mathematical Statement:
 *   match int_div_result it x y with
 *   | PrimSuccess r -> y <> 0 /\ ~(will_overflow_div it x y) /\ in_range r it
 *   | PrimDivByZero -> y = 0
 *   | PrimOverflow -> y <> 0 /\ will_overflow_div it x y
 *
 * Location: Primitives.fst:283-299, 461-467
 * Effort: 4-6 hours
 * Proof Strategy:
 *   Same case analysis as T-4.3, but tracking the precise error condition.
 *   The key insight is that int_div_result distinguishes the two failure modes
 *   (divide by zero vs overflow) while div_checked conflates them into None.
 *
 * Edge Cases to Handle:
 *   - y = 0: Must return PrimDivByZero (not PrimOverflow)
 *   - MIN_INT / -1: Must return PrimOverflow (not PrimDivByZero)
 *   - Normal division: Must return PrimSuccess with correct quotient
 *
 * Note on Result Specification:
 *   When PrimSuccess r is returned:
 *   - For unsigned: r = a / b (mathematical division, always exact for integers)
 *   - For signed: r = FStar.Int.op_Slash a b (truncated towards zero)
 *
 * Classification: DeferredProof
 *)
val theorem_int_div_result_spec : it:bounded_int_type -> a:int -> b:int ->
  Lemma (ensures (match int_div_result it a b with
                  | PrimSuccess _ -> b <> 0 /\ ~(will_overflow_div it a b)
                  | PrimDivByZero -> b = 0
                  | PrimOverflow -> b <> 0 /\ will_overflow_div it a b
                  | _ -> False))

let theorem_int_div_result_spec it a b =
  (* DeferredProof: Integer division result specification
   *
   * Case analysis following int_div_result implementation:
   *
   * First check: b = 0
   *   Returns PrimDivByZero
   *   Postcondition: b = 0 (satisfied)
   *
   * Second check: b <> 0, Unsigned type
   *   Computes a / b (mathematical division)
   *   Check: result >= 0 && result <= int_max_bounded it
   *   For unsigned with a in range and b > 0:
   *     a / b <= a <= MAX_INT, so check passes
   *   Returns PrimSuccess (a / b)
   *   Postcondition: b <> 0 /\ ~(will_overflow_div it a b)
   *     will_overflow_div for unsigned is always false (by definition)
   *   Satisfied.
   *
   * Third check: b <> 0, Signed type
   *   Sub-case a = MIN_INT and b = -1:
   *     Returns PrimOverflow
   *     Postcondition: b <> 0 /\ will_overflow_div it a b
   *       b = -1 <> 0 (satisfied)
   *       will_overflow_div it MIN_INT (-1) = true (by definition)
   *     Satisfied.
   *
   *   Sub-case not (a = MIN_INT and b = -1):
   *     Computes FStar.Int.op_Slash a b
   *     Checks result in [MIN_INT, MAX_INT]
   *     This check should always pass because:
   *       - The excluded case MIN_INT / -1 is the only one that can exceed MAX_INT
   *       - All other quotients have magnitude <= max(|a|, |b|)
   *       - For a, b in range, quotient is in range
   *     Returns PrimSuccess (truncated quotient)
   *     Postcondition satisfied.
   *
   * Note: The implementation has a redundant range check for signed that
   * could theoretically fail for out-of-range inputs, but for range_t inputs
   * it always succeeds (excluding MIN_INT/-1).
   *
   * Estimated effort: 4-6 hours for complete proof
   *)
  admit ()


(**
 * T-4.4 (auxiliary): Division result is correct quotient
 *
 * When int_div_result succeeds, the result equals the mathematical quotient
 * (for unsigned) or the truncated quotient (for signed).
 *)
val theorem_int_div_result_value : it:bounded_int_type -> a:int -> b:int{b <> 0} ->
  Lemma (requires ~(will_overflow_div it a b))
        (ensures (match int_div_result it a b with
                  | PrimSuccess r ->
                      (if Unsigned? it.sign then r = a / b
                       else r = FStar.Int.op_Slash a b)
                  | _ -> False))

let theorem_int_div_result_value it a b =
  (* DeferredProof: The success result is the correct quotient
   *
   * For unsigned:
   *   int_div_result computes a / b (F* integer division)
   *   and returns PrimSuccess (a / b) after range check.
   *
   * For signed:
   *   int_div_result computes FStar.Int.op_Slash a b
   *   (truncated division towards zero) and returns it.
   *
   * The range check is verified separately by theorem_int_div_result_spec.
   *)
  admit ()


(** ============================================================================
    AUXILIARY LEMMAS
    ============================================================================
    Supporting lemmas that help establish the main theorems.
    ============================================================================ *)

(**
 * AUX-1: Unsigned division never overflows
 *
 * For unsigned types, division cannot overflow because the quotient
 * is always smaller than or equal to the dividend.
 *)
val lemma_unsigned_div_no_overflow : it:bounded_int_type{it.sign = Unsigned} ->
  x:range_t it -> y:int{y <> 0 /\ y > 0} ->
  Lemma (ensures will_overflow_div it x y = false)

let lemma_unsigned_div_no_overflow it x y =
  (* will_overflow_div for unsigned is defined to return false *)
  ()


(**
 * AUX-2: Signed MIN_INT / -1 is the only overflow case
 *
 * For signed division, overflow occurs if and only if
 * we divide MIN_INT by -1.
 *)
val lemma_signed_overflow_iff_min_div_neg1 : it:bounded_int_type{it.sign = Signed} ->
  x:int -> y:int{y <> 0} ->
  Lemma (ensures will_overflow_div it x y = (x = int_min_bounded it && y = -1))

let lemma_signed_overflow_iff_min_div_neg1 it x y =
  (* Direct from definition of will_overflow_div for signed types *)
  ()


(**
 * AUX-3: Small unsigned modulo identity
 *
 * For any n:nat less than m:pos, n % m == n.
 * This is FStar.Math.Lemmas.small_mod wrapped for explicit use.
 *)
val lemma_small_mod : n:nat -> m:pos ->
  Lemma (requires n < m)
        (ensures n % m == n)

let lemma_small_mod n m =
  FStar.Math.Lemmas.small_mod n m


(**
 * AUX-4: Modular negation in unsigned arithmetic
 *
 * For unsigned modular arithmetic, (m - x) % m gives the additive inverse.
 *)
val lemma_unsigned_neg_mod : m:pos -> x:nat{x < m} ->
  Lemma (ensures (m - x) % m == (if x = 0 then 0 else m - x))

let lemma_unsigned_neg_mod m x =
  if x = 0 then
    FStar.Math.Lemmas.small_mod m m
  else begin
    assert (0 < m - x);
    assert (m - x < m);
    FStar.Math.Lemmas.small_mod (m - x) m
  end


(**
 * AUX-5: Truncated division bounds for signed types
 *
 * For signed division (excluding MIN_INT/-1), the quotient is bounded.
 *)
val lemma_signed_div_bounds : bits:pos{bits >= 8} ->
  a:int{-(pow2 (bits - 1)) <= a /\ a < pow2 (bits - 1)} ->
  b:int{b <> 0 /\ ~(a = -(pow2 (bits - 1)) /\ b = -1)} ->
  Lemma (ensures (let q = FStar.Int.op_Slash a b in
                  -(pow2 (bits - 1)) <= q /\ q < pow2 (bits - 1)))

let lemma_signed_div_bounds bits a b =
  (* DeferredProof: Signed division bounds
   *
   * The quotient |q| <= |a| when |b| >= 1.
   * Since a is in range, q is in range (except for MIN_INT/-1).
   * The excluded case is the only one where |q| = |MIN_INT| = -MIN_INT > MAX_INT.
   *)
  admit ()


(** ============================================================================
    THEOREM SUMMARY
    ============================================================================

    Priority 2 (Medium Effort, 2-6h each):
      T-2.10: theorem_mod_identity_unsigned     - PROVEN (uses FStar.Math.Lemmas.small_mod)
      T-2.10: theorem_mod_identity_bounded      - 2-4 hours (signed case needs work)

    Priority 3 (Substantial Effort, 3-8h each):
      T-3.6:  theorem_neg_wrap_involutive       - 3-5 hours (signed edge cases)
      T-3.6:  theorem_neg_wrap_involutive_in_range - 1 hour (follows from above)

    Priority 4 (High Effort, 4-16h each):
      T-4.3:  theorem_div_checked_correct       - 4-6 hours (complex case analysis)
      T-4.4:  theorem_int_div_result_spec       - 4-6 hours (same structure as T-4.3)
      T-4.4:  theorem_int_div_result_value      - 1-2 hours (value correctness)

    Auxiliary Lemmas:
      lemma_unsigned_div_no_overflow             - PROVEN (trivial)
      lemma_signed_overflow_iff_min_div_neg1     - PROVEN (trivial)
      lemma_small_mod                            - PROVEN (uses FStar.Math.Lemmas)
      lemma_unsigned_neg_mod                     - PROVEN
      lemma_signed_div_bounds                    - 2-3 hours

    TOTAL ESTIMATED EFFORT: 17-29 hours

    CRITICAL EDGE CASES:
    1. MIN_INT arithmetic: The most dangerous corner case
       - MIN_INT = -(2^(bits-1)) has no positive counterpart in two's complement
       - -MIN_INT == MIN_INT (overflow wraps around)
       - MIN_INT / -1 overflows (result would be 2^(bits-1) > MAX_INT)
       - MIN_INT % -1 == 0 (well-defined, no overflow)

    2. Signed modular reduction:
       - FStar.Int.op_At_Percent uses centered representation
       - Different from mathematical modulo for negative numbers
       - Result is in [-(m/2), m/2 - 1], not [0, m-1]

    3. Zero handling:
       - Division by zero: Always error
       - 0 / x == 0 for any x <> 0
       - x % 0 is undefined (error)
       - 0 % x == 0 for any x <> 0

    DEPENDENCIES:
    - Primitives.fst/fsti: Type definitions, operation implementations
    - FStar.Math.Lemmas: small_mod, lemma_mod_lt, modulo_range_lemma
    - FStar.Int: op_Slash (truncated division), op_At_Percent (centered modulo)

    ============================================================================ *)
