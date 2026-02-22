(**
 * BrrrLang.Core.SecurityTypeChecker - Interface File
 *
 * Security-aware type checker for Brrr-Lang IR implementing Information Flow
 * Control (IFC) with lattice-based security labels.
 *
 * This module implements the security type system based on Dorothy Denning's
 * foundational work on secure information flow (Denning 1976, 1977). The key
 * insight is that security can be modeled as a LATTICE where information
 * labeled l1 may flow to a location labeled l2 iff l1 <= l2 in the lattice.
 *
 * The module provides:
 *   - Security context with label tracking (sec_ctx_binding, security_ctx)
 *   - PC (program counter) label for implicit flow prevention
 *   - Security-typed inference and checking (sec_infer, sec_check)
 *   - Taint propagation through expressions
 *   - Effect-based taint tracking
 *   - Source/Sink/Sanitizer annotation checking
 *   - Context merging after branches (merge_security_ctx)
 *   - Noninterference theorem statement
 *
 * References:
 *   - Denning 1976/1977 (Information Flow Lattices)
 *   - Volpano, Smith, Irvine 1996 (Security Type System)
 *   - Sabelfeld & Myers 2003 (Language-Based Information-Flow Security)
 *   - brrr_lang_spec_v0.4.tex Part IX (Chapters 18-20)
 *)
module BrrrSecurityTypeChecker

open FStar.List.Tot
open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrSecurityTypes
open BrrrTaintEffects

(** ============================================================================
    SECURITY TYPE CONTEXT
    ============================================================================ *)

(**
 * Security context entry.
 * Each entry binds a variable name to its security-typed type and usage mode.
 *
 * Fields:
 *   scb_name - Variable identifier
 *   scb_type - Base type + security label (from SecurityTypes)
 *   scb_mode - Usage mode: MZero (consumed), MOne (linear), MOmega (unrestricted)
 *)
noeq type sec_ctx_binding = {
  scb_name  : var_id;
  scb_type  : sec_type;
  scb_mode  : mode;
}

(**
 * Security type context - list of bindings from variables to security-typed types.
 *)
type security_ctx = list sec_ctx_binding

(**
 * Empty security context.
 *)
val empty_security_ctx : security_ctx

(**
 * Extend security context with a new binding.
 *
 * @param x Variable identifier
 * @param st Security-typed type
 * @param m Usage mode
 * @param ctx Current context
 * @return Extended context with new binding at the front
 *)
val extend_security_ctx : x:var_id -> st:sec_type -> m:mode -> ctx:security_ctx -> security_ctx

(**
 * Lookup a variable in the security context.
 *
 * @param x Variable identifier to find
 * @param ctx Security context to search
 * @return Some (type, mode) if found, None otherwise
 *)
val lookup_security_ctx : x:var_id -> ctx:security_ctx -> option (sec_type & mode)

(**
 * Merge two security contexts after branch divergence.
 *
 * CRITICAL FOR SOUNDNESS: After an if-then-else or match expression, variables
 * may have been assigned different values (with different labels) in each branch.
 * To maintain soundness, we must JOIN their labels so that the merged context
 * reflects ALL possible security levels the variable could have.
 *
 * Related to Denning's "Combining Rule":
 *   label(x after branch) = label(x in then) join label(x in else)
 *
 * @param ctx1 Context from first branch
 * @param ctx2 Context from second branch
 * @return Merged context with joined labels
 *)
val merge_security_ctx : ctx1:security_ctx -> ctx2:security_ctx -> security_ctx

(**
 * Consume a linear variable in security context.
 *
 * Marks a MOne (linear) variable as consumed (MZero).
 * MOmega variables can be used multiple times without consumption.
 *
 * @param x Variable to consume
 * @param ctx Current context
 * @return Some updated_context if consumption successful, None if variable
 *         not found or already consumed
 *)
val consume_sec_var : x:var_id -> ctx:security_ctx -> option security_ctx

(** ============================================================================
    SECURITY TYPING RESULTS
    ============================================================================ *)

(**
 * Result of security type checking.
 *   - STyOk: Success with inferred type, updated context, and effects
 *   - STyError: Failure with error message
 *)
type sec_typing_result =
  | STyOk    : sec_type -> security_ctx -> effect_row -> sec_typing_result
  | STyError : string -> sec_typing_result

(**
 * Result of security type checking for expression lists.
 * Used for tuples, function arguments, and block expressions.
 *)
type sec_list_result =
  | STyOk'    : list sec_type -> security_ctx -> effect_row -> sec_list_result
  | STyError' : string -> sec_list_result

(**
 * Combine effects from sequential expressions.
 * Effects are joined using the effect row lattice join operation.
 *
 * @param e1 Effects from first expression
 * @param e2 Effects from second expression
 * @return Combined effects
 *)
val seq_effects : e1:effect_row -> e2:effect_row -> effect_row

(** ============================================================================
    LITERAL AND OPERATOR TYPE INFERENCE
    ============================================================================ *)

(**
 * Infer base type of a literal.
 *
 * @param lit The literal to type
 * @return The base Brrr type of the literal
 *)
val literal_base_type : lit:literal -> brrr_type

(**
 * Infer security type of a literal (always untainted).
 * Literals are constant values that don't come from any external source.
 *
 * @param lit The literal to type
 * @return Security-typed type with untainted/public label
 *)
val infer_literal_sec : lit:literal -> sec_type

(**
 * Infer type of unary operation.
 * Result has same security label as operand.
 *
 * @param op The unary operator
 * @param st The security type of the operand
 * @return Some result_type if operation is valid, None otherwise
 *)
val infer_unary_sec : op:unary_op -> st:sec_type -> option sec_type

(**
 * Infer type of binary operation.
 * Result has join of both operand security labels.
 *
 * @param op The binary operator
 * @param st1 Security type of left operand
 * @param st2 Security type of right operand
 * @return Some result_type if operation is valid, None otherwise
 *)
val infer_binary_sec : op:binary_op -> st1:sec_type -> st2:sec_type -> option sec_type

(** ============================================================================
    SECURITY TYPE INFERENCE (MAIN ALGORITHM)
    ============================================================================ *)

(**
 * Infer security type of expression.
 * Main entry point for security type checking with PC label tracking.
 *
 * The algorithm is SYNTAX-DIRECTED, analyzing each expression form and
 * applying the appropriate security typing rule based on Denning's
 * information flow analysis.
 *
 * Key rules:
 *   - RULE-IF: raise PC and join with branch labels
 *   - RULE-LET: bound variable inherits PC
 *   - RULE-ASSIGN: check flow constraint (pc join rhs_label <= lhs_label)
 *
 * @param ctx Security context mapping variables to security-typed types
 * @param pc Current program counter label (tracks control flow security)
 * @param e Expression to type-check
 * @return STyOk(st, ctx', eff) on success, STyError(msg) on failure
 *)
val sec_infer :
    ctx:security_ctx ->
    pc:pc_label ->
    e:expr ->
    Tot sec_typing_result (decreases e)

(**
 * Infer security types for a list of expressions.
 *
 * @param ctx Security context
 * @param pc Current program counter label
 * @param es List of expressions to type
 * @return STyOk'(types, ctx', eff) on success, STyError'(msg) on failure
 *)
val sec_infer_list :
    ctx:security_ctx ->
    pc:pc_label ->
    es:list expr ->
    Tot sec_list_result (decreases es)

(**
 * Infer security type of a block (sequence of expressions).
 *
 * @param ctx Security context
 * @param pc Current program counter label
 * @param es Expressions in the block
 * @return STyOk(type, ctx', eff) for last expression, or error
 *)
val sec_infer_block :
    ctx:security_ctx ->
    pc:pc_label ->
    es:list expr ->
    Tot sec_typing_result (decreases es)

(**
 * Infer security type for match arms.
 * Each arm's body is checked under the raised PC.
 *
 * CRITICAL: Result label MUST include PC because match arms execute under
 * the PC raised by the scrutinee. The choice of which arm executes leaks
 * information about the scrutinee's value.
 *
 * @param ctx Security context
 * @param pc Program counter label (already raised by scrutinee)
 * @param arms List of match arms
 * @return Some (result_type, merged_ctx, effects) or None on error
 *)
val sec_infer_match_arms :
    ctx:security_ctx ->
    pc:pc_label ->
    arms:list match_arm ->
    option (sec_type & security_ctx & effect_row)

(** ============================================================================
    FUNCTION SECURITY CHECKING
    ============================================================================ *)

(**
 * Check function against security role.
 *
 * Verifies that a function's inferred types match its declared security role.
 *
 * Role-specific checks:
 *   - SrSource: Return label must contain ALL declared taint kinds
 *   - SrSink: NO parameter can have ANY rejected taint kinds
 *   - SrSanitizer: Output should not have declared taints
 *   - SrValidator: No strict check (partial sanitizers)
 *
 * @param func_st Security-typed function type with parameters, return, and role
 * @param effects Effects produced by the function body
 * @return None if role constraints satisfied, Some(message) if violation found
 *)
val check_function_role : func_st:sec_func_type -> effects:effect_row -> option string

(** ============================================================================
    EFFECT-BASED TAINT CHECKING
    ============================================================================ *)

(**
 * Check expression effects for taint safety.
 *
 * Analyzes the effect row produced by type checking and detects any
 * taint violations (tainted data reaching unsafe sinks).
 *
 * @param input_taint The initial taint state (usually sec_public_trusted)
 * @param effects The effects produced by the expression
 * @return None if no violations found, Some(message) if violation detected
 *)
val check_effect_taint_safety : input_taint:sec_label -> effects:effect_row -> option string

(** ============================================================================
    SECURITY ANNOTATION CHECKING
    ============================================================================ *)

(**
 * Check if function call respects sink annotations.
 *
 * A sink annotation specifies which parameter indices must NOT have
 * certain taint kinds.
 *
 * @param snk Sink annotation with rejected taints and parameter indices
 * @param arg_types Security types of the arguments
 * @return True if no rejected taints present in specified parameters
 *)
val check_sink_annotation : snk:sink_annotation -> arg_types:list sec_type -> bool

(**
 * Check if result matches source annotation.
 *
 * A source annotation specifies which taint kinds the source introduces.
 * The return value must have ALL specified taint kinds.
 *
 * @param src Source annotation with declared taints and origin
 * @param result_type Security type of the return value
 * @return True if all declared taint kinds are present
 *)
val check_source_annotation : src:source_annotation -> result_type:sec_type -> bool

(** ============================================================================
    SECURITY TYPE CHECKING ENTRY POINTS
    ============================================================================ *)

(**
 * Full security check for an expression.
 *
 * This is the main entry point for expression-level security analysis.
 *
 * @param ctx Security context with variable bindings
 * @param e Expression to check
 * @return None if the expression is secure, Some(message) if violation found
 *)
val security_check : ctx:security_ctx -> e:expr -> option string

(**
 * Security check for a function body.
 *
 * This is the main entry point for function-level security analysis.
 *
 * @param params Function parameters with security types and modes
 * @param body Function body expression
 * @param role Security role of the function (source/sink/sanitizer/none)
 * @return None if the function is secure, Some(message) if violation found
 *)
val security_check_function :
    params:list sec_param ->
    body:expr ->
    role:sec_role ->
    option string

(** ============================================================================
    NON-INTERFERENCE DEFINITIONS AND THEOREMS
    ============================================================================ *)

(**
 * Check if a security label is observable at a given observation level.
 *
 * @param l The label to check
 * @param obs The observation level
 * @return True if l <= obs in the security lattice
 *)
val is_observable : l:sec_label -> obs:sec_label -> bool

(**
 * Check if two security context entries are low-equivalent at observation level.
 *
 * @param obs Observation level
 * @param b1 First binding
 * @param b2 Second binding
 * @return True if entries are equivalent from observer's perspective
 *)
val ctx_entry_low_equiv : obs:sec_label -> b1:sec_ctx_binding -> b2:sec_ctx_binding -> bool

(**
 * Check if two security contexts are low-equivalent at observation level.
 *
 * Two contexts are low-equivalent if for every observable variable,
 * both contexts agree on the variable's type and label.
 *
 * @param obs Observation level
 * @param ctx1 First context
 * @param ctx2 Second context
 * @return True if contexts are equivalent from observer's perspective
 *)
val low_equiv : obs:sec_label -> ctx1:security_ctx -> ctx2:security_ctx -> bool

(**
 * Check if two security types are low-equivalent at observation level.
 *
 * @param obs Observation level
 * @param st1 First security type
 * @param st2 Second security type
 * @return True if types are equivalent from observer's perspective
 *)
val sec_type_low_equiv : obs:sec_label -> st1:sec_type -> st2:sec_type -> bool

(**
 * Non-interference theorem.
 *
 * If two contexts are low-equivalent at observation level obs, and the PC
 * is NOT observable (we're in a secret branch), then evaluation produces
 * low-equivalent results.
 *
 * This is the fundamental security property: high (secret) data cannot
 * influence what an observer at level obs can see.
 *)
val noninterference :
  ctx1:security_ctx ->
  ctx2:security_ctx ->
  pc:pc_label ->
  e:expr ->
  obs:sec_label ->
  Lemma (requires
           low_equiv obs ctx1 ctx2 = true /\
           sec_label_leq pc obs = false)
        (ensures
           (match sec_infer ctx1 pc e, sec_infer ctx2 pc e with
            | STyOk st1 ctx1' _, STyOk st2 ctx2' _ ->
                sec_type_low_equiv obs st1 st2 = true /\
                low_equiv obs ctx1' ctx2' = true
            | STyError _, STyError _ -> true
            | _, _ -> true))

(**
 * Non-interference corollary for low PC.
 *
 * When PC is observable (low), and contexts are low-equiv,
 * then observable results are identical.
 *)
val noninterference_low_pc :
  ctx1:security_ctx ->
  ctx2:security_ctx ->
  pc:pc_label ->
  e:expr ->
  obs:sec_label ->
  Lemma (requires
           low_equiv obs ctx1 ctx2 = true /\
           sec_label_leq pc obs = true)
        (ensures
           (match sec_infer ctx1 pc e, sec_infer ctx2 pc e with
            | STyOk st1 ctx1' _, STyOk st2 ctx2' _ ->
                (is_observable st1.label obs ==>
                   sec_type_low_equiv obs st1 st2 = true) /\
                low_equiv obs ctx1' ctx2' = true
            | STyError _, STyError _ -> true
            | _, _ -> true))

(** ============================================================================
    PC LABEL PROPAGATION INVARIANTS
    ============================================================================ *)

(**
 * Verify that a typing result respects PC propagation invariant.
 *
 * The result label must be at least as high as PC, ensuring
 * values computed under high control flow have high labels.
 *
 * @param pc Current program counter label
 * @param st Security type of the result
 * @return True if pc <= st.label
 *)
val pc_invariant_holds : pc:pc_label -> st:sec_type -> bool
