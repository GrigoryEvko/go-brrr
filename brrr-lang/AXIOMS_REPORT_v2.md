# Brrr-Lang Axioms Report v2

## Rigorous Separation of Axioms, Definitions, and Theorems

**Version:** 2.0
**Generated:** 2026-01-26
**Methodology:** Systematic classification using formal criteria

---

## Classification Criteria

### What is a TRUE AXIOM?
A statement that **cannot be proven** within any formal system because:
1. **Undecidability** - Reduces to Halting Problem (Turing 1936)
2. **External Trust** - Depends on unverified external systems
3. **Gödel Incompleteness** - Self-referential consistency claims
4. **Foundational Math** - On same level as Peano/ZFC axioms
5. **Semantic Gap** - Bridges syntax to programmer intent

### What is a DEFINITION?
A statement that **establishes meaning** - it cannot be "wrong" because it defines what a concept IS:
- Algebraic data type declarations
- Semantic equivalence relations
- Design choice specifications
- Naming conventions

### What is a THEOREM?
A statement that **can and must be proven** from definitions and axioms:
- Properties of defined structures
- Soundness/completeness results
- Preservation lemmas
- Simulation relations

---

# PART I: TRUE AXIOMS (36 Total)

These form the **Irreducible Trusted Computing Base**.

---

## A. Computational Undecidability (18 Axioms)

These arise from fundamental limits of computation. No formal system can decide them.

### A.1 Program Termination

**ID:** `AXIOM-HALT-001`
**Statement:** For arbitrary expression `e` and state `st`, determining whether sufficient fuel exists for evaluation to complete is undecidable.
**Location:** `Eval.fst:2014`
**Why Unprovable:** Halting Problem (Turing 1936)
**Impact:** Fuel-based evaluation is necessarily incomplete.

```fstar
(* We cannot prove this - it IS the Halting Problem *)
val eval_terminates : e:expr -> st:eval_state ->
  (exists (fuel:nat). ~(RDiv? (fst (eval_expr fuel e st))))
```

---

### A.2 Interleaved Dyck Reachability

**ID:** `AXIOM-HALT-002`
**Statement:** Combined context-sensitive and field-sensitive pointer analysis is undecidable.
**Location:** `synthesis_appendices.tex:351`
**Why Unprovable:** Reduces to Post Correspondence Problem
**Impact:** Must use MCFL or SPDS approximation.

---

### A.3 Exhaustiveness with Guards

**ID:** `AXIOM-HALT-003`
**Statement:** Pattern exhaustiveness with arbitrary guards is undecidable.
**Location:** `brrr_lang_spec_v0.4.tex:3505-3517`
**Why Unprovable:** Guard `e` encodes arbitrary computation
**Impact:** Conservative approximation required.

---

### A.4 Loop Divergence

**ID:** `AXIOM-HALT-004`
**Statement:** Determining whether a while loop terminates is undecidable.
**Location:** `brrr_lang_spec_v0.4.tex:2676-2680`
**Why Unprovable:** Direct instance of Halting Problem
**Impact:** All while loops carry `Div` effect conservatively.

---

### A.5 General Deadlock Detection

**ID:** `AXIOM-HALT-005`
**Statement:** Deadlock detection for programs with unbounded state is undecidable.
**Location:** `synthesis_part6.tex:518`, `synthesis_part14.tex:1910-1913`
**Why Unprovable:** State space exploration is unbounded
**Impact:** Deadlock analysis is necessarily incomplete.

---

### A.6 Liveness Properties

**ID:** `AXIOM-HALT-006`
**Statement:** Liveness ("something good eventually happens") is undecidable for general processes.
**Location:** `synthesis_part14.tex:1910-1913`
**Why Unprovable:** Rice's Theorem - non-trivial semantic property
**Impact:** Cannot guarantee eventual progress.

---

### A.7 Termination Channels

**ID:** `AXIOM-HALT-007`
**Statement:** Detecting all termination-based covert channels is undecidable.
**Location:** `synthesis_part8.tex:689-693, 1099-1103`
**Why Unprovable:** Requires determining if loops terminate differently for different secrets
**Impact:** TSNI is undecidable.

---

### A.8 Timing Channel Freedom

**ID:** `AXIOM-HALT-008`
**Statement:** Determining whether two code paths take exactly the same time is undecidable.
**Location:** `synthesis_part8.tex:1124-1138`
**Why Unprovable:** Requires solving halting + modeling microarchitecture
**Impact:** Constant-time verification is approximate.

---

### A.9 Ranking Function Synthesis

**ID:** `AXIOM-HALT-009`
**Statement:** Automatically synthesizing ranking functions is undecidable.
**Location:** `synthesis_part7.tex:1455-1461`
**Why Unprovable:** Equivalent to proving termination
**Impact:** Liveness proofs require human-provided ranking functions.

---

### A.10 Linearizability Checking

**ID:** `AXIOM-HALT-010`
**Statement:** Determining whether a valid linearization exists is NP-complete.
**Location:** `synthesis_part7.tex:1316-1323`
**Why Unprovable:** Gibbons & Korach 1997 - exhaustive search intractable
**Impact:** Bounded exploration used.

---

### A.11 Magic Wand Reasoning

**ID:** `AXIOM-HALT-011`
**Statement:** Full magic wand (-*) reasoning in separation logic is PSPACE-complete.
**Location:** `synthesis_part7.tex:1664`
**Why Unprovable:** Reynolds - no polynomial algorithm (assuming P ≠ PSPACE)
**Impact:** Restricted separation logic fragments used.

---

### A.12 Widening Termination

**ID:** `AXIOM-HALT-012`
**Statement:** Verifying that arbitrary widening operators satisfy ascending chain condition is undecidable.
**Location:** `synthesis_part2.tex:828-834`, `synthesis_part12.tex:1436-1447`
**Why Unprovable:** Second-order property over all iterations
**Impact:** Widening operators are trusted by design.

---

### A.13 Transfer Function Monotonicity

**ID:** `AXIOM-HALT-013`
**Statement:** Verifying that an arbitrary function is monotonic is undecidable.
**Location:** `synthesis_part2.tex:737-741`
**Why Unprovable:** Rice's Theorem
**Impact:** Transfer functions assumed monotonic.

---

### A.14 Call Graph Completeness

**ID:** `AXIOM-HALT-014`
**Statement:** Computing a complete call graph (no false negatives) is undecidable.
**Location:** `synthesis_part12.tex:768-769`
**Why Unprovable:** Requires knowing reachability + resolving indirect calls
**Impact:** Call graphs are over-approximate.

---

### A.15 Points-To Soundness

**ID:** `AXIOM-HALT-015`
**Statement:** "May alias" is a non-trivial semantic property - undecidable by Rice.
**Location:** `synthesis_part12.tex:686-687, 785-787`
**Why Unprovable:** Rice's Theorem
**Impact:** Points-to analysis is sound but incomplete.

---

### A.16 Data-Race Freedom

**ID:** `AXIOM-HALT-016`
**Statement:** DRF checking for programs with unbounded threads/state is undecidable.
**Location:** `synthesis_part12.tex:541`
**Why Unprovable:** State space is infinite
**Impact:** DRF-SC is conditional on DRF determination.

---

### A.17 Divergence Absence

**ID:** `AXIOM-HALT-017`
**Statement:** Proving `LDiv` effect is absent is undecidable.
**Location:** `synthesis_part12.tex:617-625`
**Why Unprovable:** `LDiv` absence = termination = Halting
**Impact:** Divergence conservatively assumed.

---

### A.18 Taint Completeness

**ID:** `AXIOM-HALT-018`
**Statement:** Universal quantification over all executions is undecidable.
**Location:** `synthesis_part12.tex:141-147`
**Why Unprovable:** Infinite paths; Rice's Theorem
**Impact:** Taint analysis has false negatives for unreachable paths.

---

## B. External System Trust (10 Axioms)

We trust these external systems because we cannot verify them.

### B.1 SMT Solver (Z3)

**ID:** `AXIOM-EXT-001`
**Statement:** Z3 returns UNSAT only for unsatisfiable formulas.
**Why Unprovable:** Z3 is ~500K lines of unverified C++
**Mitigation:** Battle-tested, used by F*, Dafny, etc.

```
Trust: Z3 UNSAT ⟹ formula unsatisfiable
```

---

### B.2 F* Soundness

**ID:** `AXIOM-EXT-002`
**Statement:** Well-typed F* programs don't go wrong.
**Why Unprovable:** Gödel's Second Incompleteness - F* cannot prove its own consistency
**Mitigation:** F* is well-studied, extracted to OCaml.

```
Trust: ⊢_F* e : τ ⟹ e does not get stuck
```

---

### B.3 Memory Model Correspondence

**ID:** `AXIOM-EXT-003`
**Statement:** Abstract memory operations equal concrete memory behavior.
**Why Unprovable:** Hardware is not formally verified
**Note:** This UNIFIES all memory models (GC, manual, etc.)

```
Trust:
  read(write(m, l, v), l) = v
  read(write(m, l, v), l') = read(m, l')  when l ≠ l'
  fresh(m) returns location not in domain(m)
```

---

### B.4 Parser Correctness (Tree-sitter)

**ID:** `AXIOM-EXT-004`
**Statement:** Tree-sitter grammars produce ASTs matching language grammars.
**Why Unprovable:** Grammars are external unverified code
**Note:** Even CompCert trusts its parser.

```
Trust: parse(source) produces AST matching grammar
```

---

### B.5 Language Frontend Correctness

**ID:** `AXIOM-EXT-005`
**Statement:** Language frontends (clang, tsc, etc.) produce correct typed ASTs.
**Why Unprovable:** Multi-million line codebases

```
Trust: Frontend produces correct typed AST
```

---

### B.6 Hardware Atomicity

**ID:** `AXIOM-EXT-006`
**Statement:** CPU atomic operations behave according to memory model specs.
**Why Unprovable:** Cannot verify cache coherence protocols

```
Trust: CAS, load-acquire, store-release have specified semantics
```

---

### B.7 IEEE 754 Floating Point

**ID:** `AXIOM-EXT-007`
**Statement:** Hardware implements IEEE 754 correctly.
**Why Unprovable:** Hardware is not formally verified

```
Trust: Float ops match IEEE 754 spec
```

---

### B.8 Memory Ordering Models

**ID:** `AXIOM-EXT-008`
**Statement:** Hardware memory models (x86-TSO, ARM) match documented behavior.
**Why Unprovable:** Reverse-engineered from observations; errata exist

```
Trust: Promising Semantics ⊆ hardware behaviors
```

---

### B.9 Compiler Preservation

**ID:** `AXIOM-EXT-009`
**Statement:** Compilers preserve source semantics.
**Why Unprovable:** GCC/Clang/rustc are not verified (CompCert is, but only for C)

```
Trust: Compiled code ≡ source semantics
```

---

### B.10 ABI/Platform Behavior

**ID:** `AXIOM-EXT-010`
**Statement:** Platform ABIs are correctly implemented.
**Why Unprovable:** External specifications

```
Trust: Runtime follows platform ABI
```

---

## C. Programmer Intent (4 Axioms)

These bridge the semantic gap between syntax and meaning.

### C.1 Declassification Intentionality

**ID:** `AXIOM-INTENT-001`
**Statement:** Programmer's `declassify()` placement reflects actual security policy.
**Why Unprovable:** Intent exists in programmer's mind
**Literature:** Chong & Myers 2004 - "Sound analysis can ENFORCE a policy, but cannot DERIVE the policy."

```
Trust: declassify() annotations reflect actual intent
```

---

### C.2 Taint Source/Sink Completeness

**ID:** `AXIOM-INTENT-002`
**Statement:** The enumeration of sources/sinks is complete for the target environment.
**Why Unprovable:** Environment-dependent; new APIs emerge
**Literature:** Livshits & Lam 2005

```
Trust: All untrusted data enters through enumerated sources
Trust: All dangerous operations are enumerated sinks
```

---

### C.3 Sanitizer Effectiveness

**ID:** `AXIOM-INTENT-003`
**Statement:** Sanitizer implementations correctly neutralize threat classes.
**Why Unprovable:** External library + context-specific + attack model completeness
**Literature:** Sabelfeld & Myers 2003

```
Trust: SanHtmlEscape blocks XSS in HTML contexts
Trust: SanSqlEscape blocks SQL injection
```

---

### C.4 Security Policy Validity

**ID:** `AXIOM-INTENT-004`
**Statement:** User-provided security policy reflects actual security needs.
**Why Unprovable:** Policy is a specification, not a theorem
**Literature:** Myers 1997 (DLM)

```
Trust: Labels correctly capture confidentiality/integrity requirements
```

---

## D. Foundational Mathematics (1 Axiom)

### D.1 Kolmogorov Probability Axioms

**ID:** `AXIOM-MATH-001`
**Statement:** Probability measures satisfy non-negativity, unitarity, and countable additivity.
**Why Unprovable:** Foundational - on same level as Peano axioms
**Used For:** Probabilistic abstract interpretation

```fstar
type prob_space (omega : Type) = {
  measure_nonneg : forall e. measure e >= 0;
  measure_total : measure omega == 1;
  measure_countable_additive :
    forall (es : nat -> event). pairwise_disjoint es ==>
    measure (countable_union es) == series (fun i -> measure (es i));
}
```

---

## E. Runtime Trust for FFI (3 Axioms)

### E.1 Pointer Conversion Soundness

**ID:** `AXIOM-FFI-001`
**Statement:** Cross-language pointer conversion preserves aliasing invariants.
**Why Unprovable:** Memory model bridging - Rust `&mut` noalias vs C `*` can alias
**Not Covered by B.10:** ABI specifies layout, not aliasing semantics

```
Trust: Converting Rust &mut to C *mut and back preserves exclusivity
```

---

### E.2 Python/Rust Runtime Interop

**ID:** `AXIOM-FFI-002`
**Statement:** CPython C API functions behave correctly.
**Why Unprovable:** Runtime API trust (not platform ABI)
**Not Covered by B.10:** CPython is a runtime, not platform ABI

```
Trust: PyLong_AsLong, PyList_GetItem, etc. behave as documented
```

---

### E.3 Dynamic Dispatch Resolution

**ID:** `AXIOM-FFI-003`
**Statement:** Runtime dispatch mechanisms (vtables, MRO, prototypes) follow language specs.
**Why Unprovable:** Runtime semantics (not parsing)
**Not Covered by B.5:** B.5 is static parsing; E.3 is dynamic dispatch

```
Trust: Python MRO, Java vtables, JS prototype chain work correctly
```

---

# PART II: DEFINITIONS (Not Axioms)

These **establish meaning**. They cannot be "wrong" because they define what concepts ARE.

---

## D.1 Memory Model Definitions

### D.1.1 Camera/RA Structure

**Statement:** A camera is a tuple `(M, ⋅, ε, ⌊-⌋)` satisfying associativity, commutativity, etc.
**Why DEFINITION:** From Iris (Jung 2018): "verify that this RA satisfies the RA axioms" - you PROVE instances satisfy the definition.

```fstar
(* This DEFINES what a camera is - not an assumption *)
type camera (m:Type) = {
  op: m -> m -> m;
  valid: m -> prop;
  core: m -> option m;

  (* Laws are PROOF OBLIGATIONS when constructing instances *)
  op_assoc: forall x y z. op x (op y z) == op (op x y) z;
  op_comm: forall x y. op x y == op y x;
  ...
}
```

---

### D.1.2 Coherence Predicates

**Statement:** Coherence axioms (CoRR, CoWW, CoRW, CoWR) define what "consistent execution" means.
**Why DEFINITION:** Batty 2011: "define what constitutes a valid/consistent execution"

```
(* These FILTER candidate executions - they don't assume anything *)
CoRR: rf^-1; mo ⊆ rb
CoWW: mo is total on writes to same location
CoRW: rf; rb ⊆ mo
CoWR: rb; rf^-1 ⊆ mo
```

---

### D.1.3 Exclusive Composition

**Statement:** `x ⋅ x = ⊥` for exclusive resources.
**Why DEFINITION:** This IS the definition of what "exclusive" means.

---

### D.1.4 Fractional Sum Constraint

**Statement:** Sum of fractions ≤ 1 for fractional permissions.
**Why DEFINITION:** Property of the Frac camera CONSTRUCTION.

---

## D.2 Effect System Definitions

### D.2.1 Effect Row Equivalence

**Statement:** Effect rows are equivalent up to permutation and duplicate elimination.
**Why DEFINITION:** Leijen 2014 (Koka): "One possible design choice..."
**Note:** Different systems (Koka, Frank, brrr-lang) make different choices.

```fstar
(* We DEFINE row equality - no proof needed *)
let row_equiv (r1 r2: effect_row) : prop =
  forall (e:effect_op). has_effect e r1 = has_effect e r2
```

---

### D.2.2 Effect Ordering (CPG Labels)

**Statement:** `EffectOrder` labels represent control flow order.
**Why DEFINITION:** This is how we DEFINE CPG construction.

---

### D.2.3 Effect Conflict (Over-approximation)

**Statement:** `EffectConflict` may over-report conflicts.
**Why DEFINITION:** Design choice for soundness (Cousot 1977).

---

### D.2.4 Handler Coverage Labels

**Statement:** `EffectCause` labels represent operational semantics edges.
**Why DEFINITION:** Graph labeling convention - could be called `EffectEnables`.

---

## D.3 Security Definitions

### D.3.1 TINI (Termination-Insensitive Noninterference)

**Statement:**
```
forall s1 s2. low_equiv(s1, s2) /\ terminates(e, s1) /\ terminates(e, s2)
  ==> low_equiv(eval(e, s1), eval(e, s2))
```
**Why DEFINITION:** This DEFINES the security condition we aim for.

---

### D.3.2 TSNI (Termination-Sensitive Noninterference)

**Statement:**
```
forall s1 s2. low_equiv(s1, s2) ==>
  (terminates(e, s1) <=> terminates(e, s2)) /\ ...
```
**Why DEFINITION:** Alternative security condition definition.
**Note:** TSNI undecidability is covered by AXIOM-HALT-007.

---

### D.3.3 0% False Positive Rate

**Statement:** Under-approximation removes false positives.
**Why DEFINITION:** O'Hearn 2020: "this is definitional, not a theorem to prove"

---

### D.3.4 Attacker Model (~_L relation)

**Statement:** Attacker observational power characterized by low equivalence relation.
**Why DEFINITION:** We CHOOSE the attacker model; proving NI given the model is a theorem.

---

## D.4 Type System Definitions

### D.4.1 Dynamic Type Consistency

**Statement:** `? ~ t` for any type `t`.
**Why DEFINITION:** Garcia 2016 (AGT): This IS the definition of dynamic type.

```fstar
(* We DEFINE consistency - ? is consistent with everything *)
| TPrim PDynamic, _ -> true
| _, TPrim PDynamic -> true
```

---

### D.4.2 Gradual Guarantee

**Statement:** Precision changes preserve behavior.
**Why DEFINITION:** AGT DERIVES this from Galois connections.

---

### D.4.3 Cast Preservation

**Statement:** Casts have specified semantics.
**Why DEFINITION:** Design choice for gradual typing.

---

### D.4.4 Gamma Concretization

**Statement:** `gamma(G) = { static types T | G ~ T }`.
**Why DEFINITION:** Definition of concretization function.

---

## D.5 Session Type Definitions

> **IMPORTANT HISTORICAL NOTE:** The foundational MPST paper Honda et al. 2008 (and JACM 2016) contained flawed proofs discovered by Scalas & Yoshida 2019. The flaws were:
> 1. The **consistency requirement** is overly restrictive - rejects valid protocols
> 2. **Full merging projection** produces contexts that violate the consistency assumption in subject reduction proofs
> 3. The claim "projecting a global type yields consistent context" is **false** for full merging
>
> **Two corrected approaches exist:**
> - **Bottom-up (Scalas & Yoshida 2019):** Uses behavioral safety property, no global types required
> - **Top-down (Yoshida & Hou 2024):** Uses association relation with **subtyping** (G |> p <= Gamma(s[p])) not equality
>
> The definitions below follow Honda 2008 but proofs should use the corrected formulations.

### D.5.1 Process ADT

**Statement:**
```fstar
noeq type process =
  | PSend : channel:channel_name -> payload:brrr_type -> continuation:process -> process
  | PRecv : channel:channel_name -> var:string -> continuation:process -> process
  | PSelect : ...
```
**Why DEFINITION:** This is a concrete algebraic data type, not an assumption.

---

### D.5.2 Session Type ADT

**Statement:**
```fstar
type session_type =
  | STEnd
  | STSend : t:brrr_type -> cont:session_type -> session_type
  | STRecv : t:brrr_type -> cont:session_type -> session_type
  | ...
```
**Why DEFINITION:** Concrete ADT.

---

### D.5.3 Duality

**Statement:** `dual(dual(S)) = S`
**Why DEFINITION + THEOREM:** Definition of dual; involution is a theorem (proven in F*).

---

## D.6 Analysis Definitions

### D.6.1 Galois Connection

**Statement:** `(α, γ)` form a Galois connection iff `α(c) ⊑ a ⟺ c ⊆ γ(a)`.
**Why DEFINITION:** Cousot 1977: This IS the definition - you PROVE instances satisfy it.

---

### D.6.2 Soundness Condition

**Statement:** `α(f^♯(c)) ⊑ f^♭(α(c))`
**Why DEFINITION:** Schema that defines what "sound abstraction" means.

---

### D.6.3 Language Feature Matrix

**Statement:** `Rust: Affine, Static, Option, ...`
**Why DEFINITION:** Classification scheme - external input to system.

---

### D.6.4 Boundary Reconciliation Function

**Statement:** `R(L1, L2) = { p in Properties | p preserved across L1 -> L2 }`
**Why DEFINITION:** Patterson realizability DEFINES boundaries.

---

## D.7 Concurrency Definitions

### D.7.1 Channel Commutativity

**Statement:** Channel operations are commutative in certain contexts.
**Why DEFINITION:** Design choice for channel semantics.

---

### D.7.2 DRedL Finite Height

**Statement:** Lattice has finite height for termination.
**Why DEFINITION:** Property of lattice WE construct.

---

---

# PART III: THEOREMS TO PROVE (Exhaustive List)

These are statements that **can and must be proven**. Organized by priority.

---

## Priority 0: Critical Infrastructure (Already Proven or Trivial)

### T-0.1 Dual Involution

**Statement:** `dual(dual(S)) = S`
**Location:** `SessionTypes.fst:413-423`
**Status:** ✓ PROVEN
**Proof:** Structural induction on session types.

---

### T-0.2 Session Equality Reflexivity

**Statement:** `session_eq S S = true`
**Location:** `SessionTypes.fst:502+`
**Status:** ✓ PROVEN

---

### T-0.3 Dual Communication Safety

**Statement:** `dual S` is communication-safe if `S` is.
**Location:** `SessionTypes.fsti:1047-1049`
**Status:** ✓ PROVEN

---

### T-0.4 Well-Formed Has Progress

**Statement:** Well-formed processes don't get stuck.
**Location:** `SessionTypes.fsti:1064-1067`
**Status:** ✓ PROVEN

---

### T-0.5 Well-Formed Implies Projectable

**Statement:** Well-formed global types can be projected.
**Location:** `MultipartySession.fst:1283-1286`
**Status:** ✓ PROVEN

---

### T-0.6 Deadlock Freedom

**Statement:** Well-typed sessions are deadlock-free.
**Location:** `MultipartySession.fst:1302-1305`
**Status:** ✓ PROVEN

---

### T-0.7 Linear Exclusivity

**Statement:** `split_ctx` produces exclusive contexts for linear vars.
**Location:** `Modes.fst:466-485`
**Status:** ✓ PROVEN (by construction)

---

## Priority 1: Low-Hanging Fruit (≤2 hours each)

### T-1.1 Taint Set Union Subset Left

**Statement:** `A ⊆ A ∪ B`
**Location:** `TaintEffects.fst:656`
**Effort:** 30 min
**Proof:** Basic set theory.

```fstar
val taint_set_union_subset_left : a:taint_set -> b:taint_set ->
  Lemma (forall t. t `mem` a ==> t `mem` (union a b))
```

---

### T-1.2 Filter Produces Nonempty

**Statement:** If filter finds element, result is nonempty.
**Location:** `TaintEffects.fst:782`
**Effort:** 1 hour
**Proof:** List induction.

```fstar
val filter_produces_element_nonempty : f:(a -> bool) -> l:list a -> x:a ->
  Lemma (requires f x /\ x `mem` l)
        (ensures length (filter f l) > 0)
```

---

### T-1.3 Fresh Variable Specification

**Statement:** `fresh_var` returns variable not in given set.
**Location:** `Expressions.fst:1963`
**Effort:** 1 hour
**Proof:** Construction proof.

```fstar
val fresh_var_spec : vars:set string ->
  Lemma (not (fresh_var vars `mem` vars))
```

---

### T-1.4 Merge Ranges Contains Left

**Statement:** Merged range contains left input.
**Location:** `Expressions.fst:215`
**Effort:** 1-2 hours
**Proof:** Position case analysis.

```fstar
val merge_ranges_contains_left : r1:range -> r2:range ->
  Lemma (contains (merge_ranges r1 r2) r1)
```

---

### T-1.5 Merge Ranges Contains Right

**Statement:** Merged range contains right input.
**Location:** `Expressions.fst:220`
**Effort:** 1-2 hours
**Proof:** Position case analysis.

```fstar
val merge_ranges_contains_right : r1:range -> r2:range ->
  Lemma (contains (merge_ranges r1 r2) r2)
```

---

### T-1.6 Eval Let Binding

**Statement:** Let binding evaluation is correct.
**Location:** `Eval.fst:2332`
**Effort:** 1-2 hours
**Proof:** match_pattern reasoning.

```fstar
val eval_let_binding : p:pattern -> v:value -> e:expr -> st:state ->
  Lemma (eval (ELet p (ELit v) e) st ==
         eval (subst_pattern p v e) st)
```

---

## Priority 2: Medium Effort (2-6 hours each)

### T-2.1 Subexpression Transitivity

**Statement:** `is_subexpr` is transitive.
**Location:** `Expressions.fst:1780`
**Effort:** 2-4 hours
**Proof:** Induction with existsb lemma.

```fstar
val is_subexpr_trans : e1:expr -> e2:expr -> e3:expr ->
  Lemma (requires is_subexpr e1 e2 /\ is_subexpr e2 e3)
        (ensures is_subexpr e1 e3)
```

---

### T-2.2 Free Variables in Subexpression

**Statement:** Subexpressions have subset of free variables.
**Location:** `Expressions.fst:1944`
**Effort:** 2-3 hours
**Proof:** Case analysis on parent.

```fstar
val free_vars_subexpr : e:expr -> sub:expr ->
  Lemma (requires is_subexpr sub e)
        (ensures free_vars sub `subset` free_vars e)
```

---

### T-2.3 Substitution Non-Free

**Statement:** Substituting for non-free variable is identity.
**Location:** `Expressions.fst:2117`
**Effort:** 2-3 hours
**Proof:** Structural induction.

```fstar
val subst_expr_non_free : x:string -> v:expr -> e:expr ->
  Lemma (requires not (x `mem` free_vars e))
        (ensures subst x v e == e)
```

---

### T-2.4 Split Ensures Exclusivity

**Statement:** Context splitting preserves linear exclusivity.
**Location:** `Modes.fst:469`
**Effort:** 2-3 hours
**Proof:** for_all/map interaction.

```fstar
val split_ensures_exclusivity : ctx:context ->
  Lemma (linear_exclusive (fst (split_ctx ctx)) (snd (split_ctx ctx)))
```

---

### T-2.5 Valid Context Linear Mode

**Statement:** Valid contexts have linear modes only for linear types.
**Location:** `Modes.fst:499`
**Effort:** 2-3 hours
**Proof:** Same infrastructure as T-2.4.

```fstar
val valid_ctx_linear_mode : ctx:context -> x:string ->
  Lemma (requires valid_ctx ctx /\ lookup x ctx = Some (t, MLinear))
        (ensures is_linear_type t)
```

---

### T-2.6 Join Preserves Valid

**Statement:** Context join preserves validity.
**Location:** `Modes.fst:523`
**Effort:** 2-3 hours
**Proof:** Use mode_join_linear_closed.

```fstar
val join_preserves_valid : ctx1:context -> ctx2:context ->
  Lemma (requires valid_ctx ctx1 /\ valid_ctx ctx2)
        (ensures valid_ctx (join_ctx ctx1 ctx2))
```

---

### T-2.7 Normalize Expression Idempotent

**Statement:** Normalization is idempotent.
**Location:** `Expressions.fst:2281`
**Effort:** 2-3 hours
**Proof:** Structural analysis.

```fstar
val normalize_expr_idempotent : e:expr ->
  Lemma (normalize (normalize e) == normalize e)
```

---

### T-2.8 Collect Source Taints Sound

**Statement:** Source taint collection is sound.
**Location:** `TaintEffects.fst:836`
**Effort:** 2-3 hours
**Proof:** Induction on expression.

```fstar
val collect_source_taints_sound : e:expr -> env:taint_env ->
  Lemma (forall t. is_taint_source e t ==> t `mem` collect_source_taints e env)
```

---

### T-2.9 Propagate Through Row Sound

**Statement:** Taint propagation through rows is sound.
**Location:** `TaintEffects.fst:881`
**Effort:** 2 hours
**Proof:** Use sec_label_leq_trans.

```fstar
val propagate_through_row_sound : row:effect_row -> taint:taint_state ->
  Lemma (forall flow. actual_flow row ==> flow `leq` propagate row taint)
```

---

### T-2.10 Mod Identity

**Statement:** `x % n = x` when `0 <= x < n`.
**Location:** `Primitives.fst:1348`
**Effort:** 2-4 hours
**Proof:** Signed range identity.

```fstar
val mod_identity : x:int -> n:pos ->
  Lemma (requires 0 <= x /\ x < n)
        (ensures x % n == x)
```

---

## Priority 3: Substantial Effort (3-8 hours each)

### T-3.1 Substitution Well-Formed

**Statement:** Substitution preserves well-formedness.
**Location:** `Expressions.fst:2103`
**Effort:** 3-5 hours
**Proof:** Structural induction.

```fstar
val subst_expr_wf : x:string -> v:expr -> e:expr ->
  Lemma (requires wf_expr e /\ wf_expr v)
        (ensures wf_expr (subst x v e))
```

---

### T-3.2 Substitution Free Variables

**Statement:** Free variables after substitution.
**Location:** `Expressions.fst:2111`
**Effort:** 3-5 hours
**Proof:** Structural induction.

```fstar
val subst_expr_free_vars : x:string -> v:expr -> e:expr ->
  Lemma (free_vars (subst x v e) ==
         (free_vars e `remove` x) `union`
         (if x `mem` free_vars e then free_vars v else empty))
```

---

### T-3.3 Eval Preserves Valid Locations

**Statement:** Evaluation preserves location validity.
**Location:** `Eval.fst:2249`
**Effort:** 3-5 hours
**Proof:** Heap helper lemmas.

```fstar
val eval_preserves_valid_locs : fuel:nat -> e:expr -> st:state ->
  Lemma (requires valid_locs st)
        (ensures valid_locs (snd (eval_expr fuel e st)))
```

---

### T-3.4 Import Preserves Types

**Statement:** Module imports preserve type kinds.
**Location:** `ModuleSystem.fst:4357`
**Effort:** 3-4 hours
**Proof:** Kind monotonicity.

```fstar
val import_preserves_types : m1:module -> m2:module -> name:string ->
  Lemma (requires imports m1 m2 /\ exports m2 name)
        (ensures type_of m1 name == type_of m2 name)
```

---

### T-3.5 Detect Violations Strict Complete

**Statement:** Strict violation detection is complete.
**Location:** `TaintEffects.fst:926`
**Effort:** 3-4 hours
**Proof:** Complex induction.

```fstar
val detect_violations_strict_complete : cpg:cpg -> policy:sec_policy ->
  Lemma (forall v. actual_violation cpg policy v ==>
         v `mem` detect_violations_strict cpg policy)
```

---

### T-3.6 Neg Wrap Involutive

**Statement:** Wrapped negation is involutive.
**Location:** `Primitives.fst:1306`
**Effort:** 3-5 hours
**Proof:** op_At_Percent lemmas.

```fstar
val neg_wrap_involutive : w:width -> x:int_t w ->
  Lemma (neg_wrap (neg_wrap x) == x)
```

---

### T-3.7 Handler Termination (Conditional)

**Statement:** IF operations terminate AND continuation is linear, THEN handler terminates.
**Location:** `Effects.fst` (implicit)
**Effort:** 4-8 hours
**Literature:** Plotkin-Pretnar 2009 Section 8
**Proof:** Structural induction on well-founded effect signatures.

```fstar
val handler_termination : h:handler -> ops:list operation ->
  Lemma (requires all_terminate ops /\ linear_continuation h)
        (ensures terminates (handle h))
```

---

## Priority 4: High Effort (4-16 hours each)

### T-4.1 Normalize Expression Equivalence

**Statement:** Normalization preserves semantics.
**Location:** `Expressions.fst:2276`
**Effort:** 4-6 hours
**Proof:** Alpha equivalence.

```fstar
val normalize_expr_equiv : e:expr -> st:state ->
  Lemma (eval e st == eval (normalize e) st)
```

---

### T-4.2 Eval Closed Environment Irrelevant

**Statement:** Closed expressions ignore environment.
**Location:** `Eval.fst:2188`
**Effort:** 4-6 hours
**Proof:** Structural induction.

```fstar
val eval_closed_env_irrelevant : e:expr -> env1:env -> env2:env -> st:state ->
  Lemma (requires closed e)
        (ensures eval_with_env e env1 st == eval_with_env e env2 st)
```

---

### T-4.3 Division Checked Correct

**Statement:** Checked division is correct.
**Location:** `Primitives.fst:426`
**Effort:** 4-6 hours
**Proof:** Complex case analysis.

```fstar
val div_checked_correct : x:int -> y:int ->
  Lemma (requires y <> 0)
        (ensures div_checked x y == Some (x / y))
```

---

### T-4.4 Int Division Result Spec

**Statement:** Integer division result specification.
**Location:** `Primitives.fst:467`
**Effort:** 4-6 hours
**Proof:** Complex case analysis (same as T-4.3).

```fstar
val int_div_result_spec : w:width -> x:int_t w -> y:int_t w ->
  Lemma (requires y <> 0 /\ not (x == min_int /\ y == -1))
        (ensures in_range w (v x / v y))
```

---

### T-4.5 Module Dependencies Acyclic

**Statement:** Module dependency graph is acyclic.
**Location:** `ModuleSystem.fst:4290`
**Effort:** 4-6 hours
**Proof:** Graph theory.

```fstar
val module_deps_acyclic : modules:list module ->
  Lemma (requires well_formed_modules modules)
        (ensures acyclic (build_dep_graph modules))
```

---

### T-4.6 Coherence Decidability

**Statement:** Session type coherence is decidable.
**Location:** `MultipartySession.fst`
**Effort:** 4-8 hours
**Literature:** Honda 2008 + Tirore 2025 (Coq template), **see also Scalas & Yoshida 2019 and Yoshida & Hou 2024 for proof corrections**
**Proof:** Constructive - projection algorithm terminates.

**IMPORTANT CAVEAT:** The original Honda 2008 coherence definition used exact equality between projections and local types. This has been corrected by Yoshida & Hou 2024 to use the **association relation** with **subtyping**: `G |> p <= Gamma(s[p])` instead of `G |> p = Gamma(s[p])`. The original consistency requirement was shown to be overly restrictive by Scalas & Yoshida 2019.

```fstar
val coherence_decidable : g:global_type ->
  Lemma (decidable (coherent g))
```

---

### T-4.7 Protocol Projection Preservation

**Statement:** Projection preserves protocol semantics.
**Location:** `MultipartySession.fst`
**Effort:** 4-8 hours
**Literature:** Honda 2008 + Tirore 2025, **corrected by Yoshida & Hou 2024**
**Proof:** Simulation relation via association (Theorems 1 and 2 in Yoshida & Hou 2024).

**NOTE:** The corrected proof uses the association relation `G ⊑_s Gamma` which allows for subtyping. The soundness theorem (Theorem 1) is "weak" in that it may involve different message labels due to subtyping. Completeness (Theorem 2) is exact.

```fstar
val projection_preserves_semantics : g:global_type -> p:participant ->
  Lemma (forall trace. global_trace g trace ==>
         local_trace (project g p) (restrict trace p))
```

---

### T-4.8 Stack Filtering Correctness

**Statement:** IFDS stack filtering doesn't lose facts.
**Location:** `synthesis_part12.tex:1938-1945`
**Effort:** 4-8 hours
**Literature:** Horwitz 1990
**Proof:** Given call graph completeness (Axiom A.14).

```fstar
val stack_filtering_correct : cfg:cfg -> cg:call_graph -> pts:points_to ->
  Lemma (requires complete_call_graph cg)
        (ensures forall loc. loc `in` filtered ==> loc `in` concrete_pts)
```

---

### T-4.9 Qilin Algorithm Soundness

**Statement:** Qilin points-to analysis is sound.
**Location:** `synthesis_part13.tex:737-754`
**Effort:** 4-8 hours
**Literature:** Tan 2022
**Proof:** Given call graph correctness.

```fstar
val qilin_sound : program:program -> cg:call_graph ->
  Lemma (requires sound_call_graph cg)
        (ensures forall (p q:ptr). may_alias p q ==>
                 overlap (qilin_pts p) (qilin_pts q))
```

---

## Priority 5: Research-Grade (8-80 hours each)

### T-5.1 Session Progress

**Statement:** Well-typed sessions make progress.
**Location:** `SessionTypes.fst` (theorem statement)
**Effort:** 8-16 hours
**Literature:** Honda 2008 Theorem 5.12 + Tirore 2025 (Coq mechanization)
**Proof:** Port from Tirore 2025's 16K lines of Coq.

**IMPORTANT:** The original Honda 2008 proofs had flaws (Scalas & Yoshida 2019). Two valid proof approaches:
1. **Bottom-up (Scalas 2019):** Use safety property phi directly, no global types needed
2. **Top-down (Yoshida & Hou 2024):** Use association relation with subtyping

Tirore 2023/2025 mechanizes a **restricted fragment** - verify the fragment covers your use case.

```fstar
val session_progress : p:process -> delta:session_ctx ->
  Lemma (requires typed delta p)
        (ensures p == PEnd \/ (exists p'. step p p'))
```

---

### T-5.2 Session Fidelity

**Statement:** Well-typed processes follow their session types.
**Location:** `SessionTypes.fst` (theorem statement)
**Effort:** 8-16 hours
**Literature:** Honda 2008 Corollary 5.6 + Tirore 2025, **see Scalas & Yoshida 2019 Theorem 5.4 for corrected formulation**
**Proof:** Port from Tirore 2025.

**NOTE:** The corrected session fidelity (Scalas 2019 Theorem 5.4, Yoshida & Hou 2024 Theorem 6) states that the process **chooses** which typing context reduction to follow (due to subtyping allowing type refinement). Key property: safety is preserved through reductions.

```fstar
val session_fidelity : p:process -> s:session_type ->
  Lemma (requires typed_session p s)
        (ensures forall trace. execution_trace p trace ==>
                 conforms trace s)
```

---

### T-5.3 Convertibility Soundness

**Statement:** Cross-language type convertibility is sound.
**Location:** `synthesis_part11.tex:732-738`
**Effort:** 8-16 hours
**Literature:** Patterson 2022 Lemma 3.1

```fstar
val convertibility_sound : tau_A:type -> tau_B:type -> v:value ->
  Lemma (requires convertible tau_A tau_B /\ realizes source_lang tau_A v)
        (ensures realizes target_lang tau_B (convert v))
```

---

### T-5.4 Matthews-Findler Boundary Soundness

**Statement:** Multi-language boundary terms are type-sound.
**Location:** `synthesis_part13.tex`
**Effort:** 8-16 hours
**Literature:** Matthews-Findler 2007 Theorems 1-6

```fstar
val boundary_soundness : e:multi_expr -> tau:type ->
  Lemma (requires typed_multi e tau)
        (ensures e -->* v \/ e -->* Error \/ diverges e)
```

---

### T-5.5 Noninterference

**Statement:** Well-typed programs satisfy noninterference.
**Location:** `InformationFlow.fst` (theorem statement)
**Effort:** 40-80 hours
**Literature:** Volpano 1996

```fstar
val noninterference : e:expr -> pc:level ->
  Lemma (requires typed_IFC pc e)
        (ensures forall s1 s2. low_equiv s1 s2 /\ terminates e s1 /\ terminates e s2 ==>
                 low_equiv (eval e s1) (eval e s2))
```

---

### T-5.6 Blame Soundness

**Statement:** Blame correctly identifies contract violators.
**Location:** `Contracts.fst` (theorem statement)
**Effort:** 16-32 hours
**Literature:** Wadler-Findler 2009

```fstar
val blame_soundness : e:expr -> contract:contract ->
  Lemma (blame (check e contract) = Some party ==>
         party violates contract)
```

---

### T-5.7 Parametricity (Abstraction Theorem)

**Statement:** Related inputs produce related outputs.
**Location:** `TypeChecker.fst` (theorem statement)
**Effort:** 16-32 hours
**Literature:** Reynolds 1983, Bernardy 2010 (Agda mechanization)

```fstar
val parametricity : f:(forall a. a -> a) ->
  Lemma (forall a (x:a). f x == x)
```

---

### T-5.8 Occurrence Typing Soundness

**Statement:** Type narrowing after predicates is sound.
**Location:** `TypeChecker.fst`
**Effort:** 8-16 hours
**Literature:** Tobin-Hochstadt 2008 (Isabelle/HOL mechanization)

```fstar
val occurrence_typing_sound : e:expr -> pred:(value -> bool) ->
  Lemma (requires typeof e = Union [T1; T2] /\ pred filters T1)
        (ensures typeof (refine e pred) = T1)
```

---

### T-5.9 Round-Trip Preservation

**Statement:** parse -> IR -> pretty-print preserves semantics.
**Location:** `synthesis_part13.tex:209-211`
**Effort:** 40-80 hours (per language)
**Literature:** CompCert-style proof

```fstar
val round_trip : source:string ->
  Lemma (eval (parse source) == eval (parse (pretty_print (to_ir (parse source)))))
```

---

### T-5.10 Control Flow Modeling

**Statement:** CFG correctly models all control flow constructs.
**Location:** `synthesis_part13.tex:212-213`
**Effort:** 8-16 hours
**Proof:** Show implementation matches language spec.

```fstar
val cfg_complete : program:program -> cfg:cfg ->
  Lemma (requires cfg = build_cfg program)
        (ensures forall path. execution_path program path ==>
                 cfg_path cfg path)
```

---

### T-5.11 DRF-SC Theorem

**Statement:** DRF programs have SC semantics.
**Location:** `Concurrency.fst` (theorem statement)
**Effort:** 20-40 hours
**Literature:** Boehm-Adve 2008 Theorem 7.1, Promising 2.0 (30K Coq)

```fstar
val drf_sc : program:program ->
  Lemma (requires data_race_free program)
        (ensures all_executions_sc program)
```

---

### T-5.12 Frame Rule Soundness

**Statement:** `{P} C {Q}` and `C` doesn't modify `R` implies `{P * R} C {Q * R}`.
**Location:** `SeparationLogic.fst` (theorem statement)
**Effort:** 8-16 hours
**Literature:** Reynolds 2002, Iris (Coq mechanized)

```fstar
val frame_rule : p:assertion -> c:command -> q:assertion -> r:assertion ->
  Lemma (requires hoare_triple p c q /\ frame_safe c r)
        (ensures hoare_triple (p * r) c (q * r))
```

---

### T-5.13 No Thin-Air Values

**Statement:** Memory model prevents thin-air reads.
**Location:** `Concurrency.fst` (theorem statement)
**Effort:** 20-40 hours
**Literature:** Kang 2017, Lee 2020 (Promising 2.0 - 30K Coq)

```fstar
val no_thin_air : execution:execution ->
  Lemma (requires valid_execution execution)
        (ensures no_oota_reads execution)
```

---

### T-5.14 Bi-Abduction Soundness

**Statement:** Bi-abduction computes correct frames.
**Location:** `SeparationLogic.fst` (theorem statement)
**Effort:** 8-16 hours
**Literature:** Calcagno 2009 Theorems 4, 5, 9

```fstar
val biabduction_sound : pre:assertion -> post:assertion -> anti_frame:assertion -> frame:assertion ->
  Lemma (requires biabduct pre post = (anti_frame, frame))
        (ensures (pre * anti_frame) -* post /\ frame * pre ⊢ post)
```

---

## Summary Statistics

### By Priority

| Priority | Count | Total Effort (hours) |
|----------|-------|---------------------|
| P0 (Done) | 7 | 0 (already proven) |
| P1 (≤2h) | 6 | 6-11 |
| P2 (2-6h) | 10 | 22-35 |
| P3 (3-8h) | 7 | 24-47 |
| P4 (4-16h) | 9 | 40-86 |
| P5 (8-80h) | 14 | 200-520 |
| **Total** | **53** | **292-699** |

### By Category

| Category | Theorems | Notes |
|----------|----------|-------|
| Expressions | 10 | Substitution, free vars, normalization |
| Modes | 3 | Linear exclusivity, context validity |
| Primitives | 4 | Division, overflow, wrapping |
| Evaluation | 4 | Preservation, environment |
| Modules | 2 | Dependencies, imports |
| Taint | 5 | Soundness, completeness |
| Effects | 1 | Handler termination |
| Sessions | 6 | Progress, fidelity, projection |
| FFI | 4 | Boundaries, conversion |
| Security | 3 | Noninterference, blame, parametricity |
| Memory | 4 | Frame, DRF-SC, thin-air, bi-abduction |
| Control Flow | 2 | CFG, round-trip |

---

## Critical Bugs (Must Fix Before Theorems)

### BUG-001: Hardcoded Hoare Logic Condition

**Location:** `Contracts.fst:348`
**Severity:** CRITICAL
```fstar
let cond_expr = ELit (LitBool true) in  (* HARDCODED! Should be actual condition *)
```
**Impact:** Cannot reason about if-then-else.
**Fix:** Pass actual branch condition.

---

### BUG-002: Hardcoded While Condition

**Location:** `Contracts.fst:356`
**Severity:** CRITICAL
```fstar
let cond_expr = ELit (LitBool true) in  (* HARDCODED! Should be actual condition *)
```
**Impact:** Cannot verify any loops.
**Fix:** Pass actual loop condition.

---

## Appendix: Proof Templates

### A. Structural Induction Template

```fstar
let rec theorem_by_induction (e: expr) : Lemma (property e) =
  match e with
  | ELit _ -> ()  (* Base case *)
  | EVar _ -> ()  (* Base case *)
  | EApp e1 e2 ->
      theorem_by_induction e1;
      theorem_by_induction e2;
      (* Combine results *)
  | ELam x body ->
      theorem_by_induction body
  | ...
```

### B. Logical Relations Template (for Parametricity)

```fstar
let rec related (R: rel) (v1 v2: value) : prop =
  match v1, v2 with
  | VInt n1, VInt n2 -> n1 == n2
  | VFun f1, VFun f2 ->
      forall x1 x2. R x1 x2 ==> related R (f1 x1) (f2 x2)
  | ...

let parametricity_fundamental (e: expr) (env1 env2: env) (R: rel) :
  Lemma (requires env_related R env1 env2)
        (ensures related R (eval e env1) (eval e env2)) =
  ...
```

### C. Simulation Relation Template (for Compiler Correctness)

```fstar
let simulation (s: source_state) (t: target_state) : prop = ...

let simulation_preserved (s: source_state) (t: target_state) :
  Lemma (requires simulation s t /\ source_step s s')
        (ensures exists t'. target_step* t t' /\ simulation s' t') =
  ...
```

---

## Document History

- **v1.0** (2026-01-26): Initial report with 154 axioms
- **v2.0** (2026-01-26): Rigorous separation into 36 axioms, definitions, 53 theorems

---

*Report generated by systematic analysis of brrr-lang codebase, synthesis documents, and academic literature.*
