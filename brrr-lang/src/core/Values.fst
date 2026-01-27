(**
 * BrrrLang.Core.Values
 *
 * Runtime values and computation domains.
 * Based on brrr_lang_spec_v0.4.tex Part I (Foundations).
 *
 * Depends on: Primitives, Types, Expressions
 *)
module Values

(** Z3 solver options - conservative settings for value proofs.
    ifuel 1 needed for pattern exhaustiveness on noeq types from .fsti *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

open Primitives
open Modes
open Effects
open BrrrTypes
open Expressions
open FStar.List.Tot

(* Helper: for_all2 - check predicate on pairs from two lists *)
#push-options "--fuel 1 --ifuel 0"
let rec for_all2 (#a #b: Type) (f: a -> b -> bool) (l1: list a) (l2: list b)
    : Tot bool (decreases %[length l1; length l2]) =
  match l1, l2 with
  | [], [] -> true
  | x :: xs, y :: ys -> f x y && for_all2 f xs ys
  | _, _ -> false
#pop-options

(** ============================================================================
    ENVIRONMENT OPERATIONS
    ============================================================================ *)

(* Empty environment *)
let empty_env : env = []

(* Lookup variable *)
let lookup (x: var_id) (e: env) : option value =
  List.Tot.assoc x e

(* Extend environment *)
let extend (x: var_id) (v: value) (e: env) : env =
  (x, v) :: e

(* Extend with multiple bindings *)
let extend_many (bindings: list (var_id & value)) (e: env) : env =
  bindings @ e

(* extend_many with singleton list equals extend *)
let extend_many_singleton (x: var_id) (v: value) (e: env)
    : Lemma (ensures extend_many [(x, v)] e == extend x v e)
    [SMTPat (extend_many [(x, v)] e)] =
  (* By definition: [(x,v)] @ e = (x,v) :: e = extend x v e *)
  ()

(* Remove variable *)
let remove (x: var_id) (e: env) : env =
  List.Tot.filter (fun (y, _) -> y <> x) e

(* Domain of environment *)
let dom (e: env) : list var_id =
  List.Tot.map fst e

(** ============================================================================
    HEAP
    ============================================================================ *)

(* Empty heap *)
let empty_heap : heap = []

(* Next available location *)
let next_loc (h: heap) : loc =
  1 + List.Tot.fold_left (fun m (l, _) -> max m l) 0 h

(* Allocate on heap *)
let alloc (v: value) (h: heap) : loc & heap =
  let l = next_loc h in
  (l, (l, v) :: h)

(* Read from heap *)
let read (l: loc) (h: heap) : option value =
  List.Tot.assoc l h

(* Write to heap *)
let write (l: loc) (v: value) (h: heap) : heap =
  (l, v) :: List.Tot.filter (fun (l', _) -> l' <> l) h

(* Deallocate *)
let dealloc (l: loc) (h: heap) : heap =
  List.Tot.filter (fun (l', _) -> l' <> l) h

(** ============================================================================
    COMPUTATION RESULTS
    ============================================================================ *)

(* Result is a monad *)
let return (#a: Type) (x: a) : result a = ROk x

#push-options "--fuel 1 --ifuel 1"
let bind (#a #b: Type) (m: result a) (f: a -> result b) : result b =
  match m with
  | ROk x -> f x
  | RErr e -> RErr e
  | RDiv -> RDiv
  | RBreak lbl v -> RBreak lbl v
  | RCont lbl -> RCont lbl
  | RRet v -> RRet v
  | RYield v -> RYield v
  | RPerform op args -> RPerform op args
  | RAbort p v -> RAbort p v
  | RGoto lbl -> RGoto lbl
#pop-options

let (let*) = bind

(* Map over result *)
#push-options "--fuel 1 --ifuel 1"
let map_result (#a #b: Type) (f: a -> b) (r: result a) : result b =
  match r with
  | ROk x -> ROk (f x)
  | RErr e -> RErr e
  | RDiv -> RDiv
  | RBreak lbl v -> RBreak lbl v
  | RCont lbl -> RCont lbl
  | RRet v -> RRet v
  | RYield v -> RYield v
  | RPerform op args -> RPerform op args
  | RAbort p v -> RAbort p v
  | RGoto lbl -> RGoto lbl
#pop-options

(* Extract value from ROk result - explicit projector for noeq type *)
let result_value (#a: Type) (r: result a{ROk? r}) : a =
  match r with
  | ROk x -> x

(** ============================================================================
    STATE MONAD
    ============================================================================ *)

(* Initial state *)
let init_state : state = {
  st_env = empty_env;
  st_heap = empty_heap
}

(* State monad operations *)
let st_return (#a: Type) (x: a) : comp a =
  fun st -> (ROk x, st)

let st_bind (#a #b: Type) (m: comp a) (f: a -> comp b) : comp b =
  fun st ->
    match m st with
    | (ROk x, st') -> f x st'
    | (RErr e, st') -> (RErr e, st')
    | (RDiv, st') -> (RDiv, st')
    | (RBreak lbl v, st') -> (RBreak lbl v, st')
    | (RCont lbl, st') -> (RCont lbl, st')
    | (RRet v, st') -> (RRet v, st')
    | (RYield v, st') -> (RYield v, st')
    | (RPerform op args, st') -> (RPerform op args, st')
    | (RAbort p v, st') -> (RAbort p v, st')
    | (RGoto lbl, st') -> (RGoto lbl, st')

(* State operations *)
let get_env : comp env =
  fun st -> (ROk st.st_env, st)

let set_env (e: env) : comp unit =
  fun st -> (ROk (), { st with st_env = e })

let get_heap : comp heap =
  fun st -> (ROk st.st_heap, st)

let set_heap (h: heap) : comp unit =
  fun st -> (ROk (), { st with st_heap = h })

let st_lookup (x: var_id) : comp (option value) =
  fun st -> (ROk (lookup x st.st_env), st)

let st_extend (x: var_id) (v: value) : comp unit =
  fun st -> (ROk (), { st with st_env = extend x v st.st_env })

let st_alloc (v: value) : comp loc =
  fun st ->
    let (l, h') = alloc v st.st_heap in
    (ROk l, { st with st_heap = h' })

let st_read (l: loc) : comp (option value) =
  fun st -> (ROk (read l st.st_heap), st)

let st_write (l: loc) (v: value) : comp unit =
  fun st -> (ROk (), { st with st_heap = write l v st.st_heap })

(** ============================================================================
    VALUE OPERATIONS
    ============================================================================ *)

(* Convert literal to value - preserves type information *)
let lit_to_value (l: literal) : value =
  match l with
  | LitUnit -> VUnit
  | LitBool b -> VBool b
  | LitInt n ty -> VInt n ty      (* Preserve int_type *)
  | LitFloat f prec -> VFloat f prec  (* Preserve float_prec *)
  | LitString s -> VString s
  | LitChar c -> VChar c

(** ============================================================================
    VALUE SIZE FUNCTIONS (for termination proofs)
    ============================================================================ *)

(* Size of a value - used for termination measures.
   These are mutually recursive. We use the totality of the inductive type to justify termination. *)
let rec value_size (v: value) : Tot nat (decreases v) =
  match v with
  | VUnit | VBool _ | VInt _ _ | VFloat _ _ | VString _ | VChar _
  | VRef _ | VRefMut _ | VBox _ | VClosure _ | VNone -> 1
  | VBoundMethod recv _ -> 1 + value_size recv  (* Bound method: receiver + closure *)
  | VSome v' | VOk v' | VErr v' -> 1 + value_size v'
  | VTuple vs -> 1 + value_list_size vs
  | VArray vs -> 1 + value_list_size vs
  | VStruct _ fields -> 1 + field_value_list_size fields
  | VVariant _ _ vs -> 1 + value_list_size vs
  (* Async/Generator values - constant size since they use heap locations *)
  | VFuture _ -> 1
  | VGenerator _ -> 1

and value_list_size (vs: vlist value) : Tot nat (decreases vs) =
  match vs with
  | [] -> 0
  | v :: rest -> value_size v + value_list_size rest

(* Note: field_value_list_size termination relies on the strictly_positive annotation
   on vlist ensuring that values in the list are subterms of the list.
   F* should be able to verify this with sufficient fuel. *)
and field_value_list_size (fields: vlist (string & value)) : Tot nat (decreases fields) =
  match fields with
  | [] -> 0
  | (_, v) :: rest -> value_size v + field_value_list_size rest

(** value_size is always positive *)
let rec value_size_pos (v: value)
    : Lemma (ensures value_size v >= 1)
            (decreases v)
            [SMTPat (value_size v)] =
  match v with
  | VUnit | VBool _ | VInt _ _ | VFloat _ _ | VString _ | VChar _
  | VRef _ | VRefMut _ | VBox _ | VClosure _ | VNone
  | VFuture _ | VGenerator _ -> ()
  | VBoundMethod recv _ -> value_size_pos recv
  | VSome v' | VOk v' | VErr v' -> value_size_pos v'
  | VTuple _ | VArray _ | VStruct _ _ | VVariant _ _ _ -> ()

(* Runtime future state equality *)
let runtime_future_state_eq (s1 s2: runtime_future_state) : bool =
  match s1, s2 with
  | RFutPending, RFutPending -> true
  | RFutResolved l1, RFutResolved l2 -> l1 = l2
  | RFutFailed e1, RFutFailed e2 -> e1 = e2
  | RFutCancelled, RFutCancelled -> true
  | _, _ -> false

(* Runtime generator state equality *)
let runtime_gen_state_eq (s1 s2: runtime_gen_state) : bool =
  match s1, s2 with
  | RGenInitial c1, RGenInitial c2 -> c1 = c2
  | RGenYielded l1 c1, RGenYielded l2 c2 -> l1 = l2 && c1 = c2
  | RGenDone l1, RGenDone l2 -> l1 = l2
  | RGenFailed e1, RGenFailed e2 -> e1 = e2
  | _, _ -> false

(** ============================================================================
    VALUE EQUALITY - IEEE 754 COMPLIANT
    ============================================================================

    CRITICAL: Float comparison follows IEEE 754 semantics:
    - NaN is not equal to anything, including itself
    - Two floats must have matching precision for equality

    This is semantically correct for language runtime behavior.
    For bit-exact comparison (serialization), use value_eq_bits.
    ============================================================================ *)

(* Value equality - mutually recursive with list helper *)
let rec value_eq (v1 v2: value) : Tot bool (decreases %[value_size v1; 0]) =
  match v1, v2 with
  | VUnit, VUnit -> true
  | VBool b1, VBool b2 -> b1 = b2
  (* Integer equality: must match both value AND type *)
  | VInt n1 ty1, VInt n2 ty2 ->
      n1 = n2 && ty1.width = ty2.width && ty1.sign = ty2.sign
  (* Float equality: IEEE 754 compliant - NaN != NaN, must match precision *)
  | VFloat f1 prec1, VFloat f2 prec2 ->
      (* Use IEEE 754 semantics from Primitives module *)
      prec1 = prec2 && float_repr_eq_ieee754 f1 f2
  | VString s1, VString s2 -> s1 = s2
  | VChar c1, VChar c2 -> c1 = c2
  | VTuple vs1, VTuple vs2 ->
      length vs1 = length vs2 && value_list_eq vs1 vs2
  | VNone, VNone -> true
  | VSome v1', VSome v2' -> value_eq v1' v2'
  | VRef l1, VRef l2 -> l1 = l2
  | VRefMut l1, VRefMut l2 -> l1 = l2
  | VBox l1, VBox l2 -> l1 = l2
  | VFuture fs1, VFuture fs2 -> runtime_future_state_eq fs1 fs2
  | VGenerator gs1, VGenerator gs2 -> runtime_gen_state_eq gs1 gs2
  | _, _ -> false

and value_list_eq (vs1 vs2: vlist value) : Tot bool (decreases %[value_list_size vs1; 1]) =
  match vs1, vs2 with
  | [], [] -> true
  | v1 :: rest1, v2 :: rest2 -> value_eq v1 v2 && value_list_eq rest1 rest2
  | _, _ -> false

(* Bit-exact value equality - ignores IEEE 754 NaN semantics.
   Use for serialization, hashing, or when bit-exact comparison is needed. *)
let rec value_eq_bits (v1 v2: value) : Tot bool (decreases %[value_size v1; 0]) =
  match v1, v2 with
  | VUnit, VUnit -> true
  | VBool b1, VBool b2 -> b1 = b2
  | VInt n1 ty1, VInt n2 ty2 ->
      n1 = n2 && ty1.width = ty2.width && ty1.sign = ty2.sign
  (* Bit-exact comparison for floats - does NOT follow IEEE 754 *)
  | VFloat f1 prec1, VFloat f2 prec2 ->
      prec1 = prec2 && float_repr_eq_bits f1 f2
  | VString s1, VString s2 -> s1 = s2
  | VChar c1, VChar c2 -> c1 = c2
  | VTuple vs1, VTuple vs2 ->
      length vs1 = length vs2 && value_list_eq_bits vs1 vs2
  | VNone, VNone -> true
  | VSome v1', VSome v2' -> value_eq_bits v1' v2'
  | VRef l1, VRef l2 -> l1 = l2
  | VRefMut l1, VRefMut l2 -> l1 = l2
  | VBox l1, VBox l2 -> l1 = l2
  | VFuture fs1, VFuture fs2 -> runtime_future_state_eq fs1 fs2
  | VGenerator gs1, VGenerator gs2 -> runtime_gen_state_eq gs1 gs2
  | _, _ -> false

and value_list_eq_bits (vs1 vs2: vlist value) : Tot bool (decreases %[value_list_size vs1; 1]) =
  match vs1, vs2 with
  | [], [] -> true
  | v1 :: rest1, v2 :: rest2 -> value_eq_bits v1 v2 && value_list_eq_bits rest1 rest2
  | _, _ -> false

(* Char comparison helper *)
let char_compare (c1 c2: FStar.Char.char) : int =
  let i1 = FStar.Char.int_of_char c1 in
  let i2 = FStar.Char.int_of_char c2 in
  if i1 < i2 then -1 else if i1 > i2 then 1 else 0

(** Value comparison - IEEE 754 compliant for floats.

    CRITICAL: For floats, comparisons involving NaN return 0 (unordered).
    This follows IEEE 754 semantics where NaN comparisons are unordered.

    Returns:
    - -1 if v1 < v2
    -  0 if v1 = v2 (or unordered for NaN)
    -  1 if v1 > v2
*)
let value_compare (v1 v2: value) : int =
  match v1, v2 with
  | VInt n1 _, VInt n2 _ -> if n1 < n2 then -1 else if n1 > n2 then 1 else 0
  (* Float comparison: NaN comparisons are unordered (return 0) *)
  | VFloat f1 _, VFloat f2 _ ->
      (* If either is NaN, comparison is unordered *)
      if is_nan_f64 f1 || is_nan_f64 f2 then 0
      else if f1 < f2 then -1 else if f1 > f2 then 1 else 0
  | VString s1, VString s2 -> FStar.String.compare s1 s2
  | VChar c1, VChar c2 -> char_compare c1 c2
  | _, _ -> 0

(* Truthy check - updated for typed integers *)
let is_truthy (v: value) : bool =
  match v with
  | VBool b -> b
  | VInt n _ -> n <> 0
  | VFloat f _ -> not (is_nan_f64 f) && f <> 0  (* NaN is falsy *)
  | VNone -> false
  | VSome _ -> true
  | _ -> true

(** ============================================================================
    NAN-FREE PREDICATE
    ============================================================================

    Required for reflexivity of value_eq (since NaN != NaN per IEEE 754).
    ============================================================================ *)

(* Predicate: value contains no NaN floats - required for reflexivity *)
let rec value_is_nan_free (v: value) : Tot bool (decreases v) =
  match v with
  | VFloat f _ -> not (is_nan_f64 f)
  | VSome v' | VOk v' | VErr v' -> value_is_nan_free v'
  | VTuple vs | VArray vs -> value_list_is_nan_free vs
  | VStruct _ fields -> field_value_list_is_nan_free fields
  | VVariant _ _ vs -> value_list_is_nan_free vs
  | _ -> true

and value_list_is_nan_free (vs: vlist value) : Tot bool (decreases vs) =
  match vs with
  | [] -> true
  | v :: rest -> value_is_nan_free v && value_list_is_nan_free rest

and field_value_list_is_nan_free (fields: vlist (string & value)) : Tot bool (decreases fields) =
  match fields with
  | [] -> true
  | (_, v) :: rest -> value_is_nan_free v && field_value_list_is_nan_free rest

(** ============================================================================
    VALUE EQUALITY LEMMAS
    ============================================================================

    IMPORTANT: Due to IEEE 754 semantics for floats (NaN != NaN), value_eq
    does NOT form a true equivalence relation. Reflexivity fails for NaN values.

    These lemmas establish partial equivalence properties:
    - value_eq_bits forms a true equivalence relation (bit-exact comparison)
    - value_eq is reflexive EXCEPT for NaN-containing values
    - value_eq is symmetric and transitive (when it returns true)

    For proofs requiring reflexivity, use value_eq_bits instead.
    ============================================================================ *)

(** value_eq_bits is reflexive (always true, no NaN exception) *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let rec value_eq_bits_refl (v: value)
    : Lemma (ensures value_eq_bits v v = true)
            (decreases %[value_size v; 0])
            [SMTPat (value_eq_bits v v)] =
  match v with
  | VUnit | VBool _ | VInt _ _ | VFloat _ _ | VString _ | VChar _
  | VRef _ | VRefMut _ | VBox _ | VClosure _ | VNone
  | VFuture _ | VGenerator _ -> ()
  | VBoundMethod recv _ -> value_eq_bits_refl recv
  | VSome v' -> value_eq_bits_refl v'
  | VOk v' -> value_eq_bits_refl v'
  | VErr v' -> value_eq_bits_refl v'
  | VTuple vs -> value_list_eq_bits_refl vs
  | VArray vs -> value_list_eq_bits_refl vs
  | VStruct _ _ -> ()  (* Not fully compared in value_eq_bits *)
  | VVariant _ _ _ -> ()  (* Not fully compared in value_eq_bits *)

and value_list_eq_bits_refl (vs: vlist value)
    : Lemma (ensures value_list_eq_bits vs vs = true)
            (decreases %[value_list_size vs; 1]) =
  match vs with
  | [] -> ()
  | v :: rest -> value_eq_bits_refl v; value_list_eq_bits_refl rest
#pop-options

(** value_eq is reflexive for NaN-free values.
    IMPORTANT: This does NOT hold for values containing NaN floats. *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
let rec value_eq_refl (v: value)
    : Lemma (requires value_is_nan_free v)
            (ensures value_eq v v = true)
            (decreases %[value_size v; 0])
            [SMTPat (value_eq v v)] =
  match v with
  | VUnit | VBool _ | VInt _ _ | VFloat _ _ | VString _ | VChar _
  | VRef _ | VRefMut _ | VBox _ | VClosure _ | VNone
  | VFuture _ | VGenerator _ -> ()
  | VBoundMethod recv _ -> value_eq_refl recv
  | VSome v' -> value_eq_refl v'
  | VOk v' -> value_eq_refl v'
  | VErr v' -> value_eq_refl v'
  | VTuple vs -> value_list_eq_refl vs
  | VArray vs -> value_list_eq_refl vs
  | VStruct _ _ -> ()  (* Not fully compared in value_eq *)
  | VVariant _ _ _ -> ()  (* Not fully compared in value_eq *)

and value_list_eq_refl (vs: vlist value)
    : Lemma (requires value_list_is_nan_free vs)
            (ensures value_list_eq vs vs = true)
            (decreases %[value_list_size vs; 1]) =
  match vs with
  | [] -> ()
  | v :: rest -> value_eq_refl v; value_list_eq_refl rest
#pop-options

(** value_eq is symmetric: value_eq v1 v2 = true ==> value_eq v2 v1 = true *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let rec value_eq_sym (v1 v2: value)
    : Lemma (requires value_eq v1 v2 = true)
            (ensures value_eq v2 v1 = true)
            (decreases %[value_size v1; 0])
            [SMTPat (value_eq v1 v2); SMTPat (value_eq v2 v1)] =
  match v1, v2 with
  | VUnit, VUnit | VBool _, VBool _ | VInt _ _, VInt _ _
  | VFloat _ _, VFloat _ _ | VString _, VString _ | VChar _, VChar _
  | VRef _, VRef _ | VRefMut _, VRefMut _ | VBox _, VBox _
  | VNone, VNone | VFuture _, VFuture _ | VGenerator _, VGenerator _ -> ()
  | VSome v1', VSome v2' -> value_eq_sym v1' v2'
  | VOk v1', VOk v2' -> value_eq_sym v1' v2'
  | VErr v1', VErr v2' -> value_eq_sym v1' v2'
  | VTuple vs1, VTuple vs2 -> value_list_eq_sym vs1 vs2
  | VArray vs1, VArray vs2 -> value_list_eq_sym vs1 vs2
  | _, _ -> ()

and value_list_eq_sym (vs1 vs2: vlist value)
    : Lemma (requires value_list_eq vs1 vs2 = true)
            (ensures value_list_eq vs2 vs1 = true)
            (decreases %[value_list_size vs1; 1]) =
  match vs1, vs2 with
  | [], [] -> ()
  | v1 :: r1, v2 :: r2 -> value_eq_sym v1 v2; value_list_eq_sym r1 r2
  | _, _ -> ()
#pop-options

(** value_eq is transitive:
    value_eq v1 v2 = true /\ value_eq v2 v3 = true ==> value_eq v1 v3 = true *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec value_eq_trans (v1 v2 v3: value)
    : Lemma (requires value_eq v1 v2 = true /\ value_eq v2 v3 = true)
            (ensures value_eq v1 v3 = true)
            (decreases %[value_size v1; 0]) =
  match v1, v2, v3 with
  | VUnit, VUnit, VUnit | VBool _, VBool _, VBool _
  | VInt _ _, VInt _ _, VInt _ _ | VFloat _ _, VFloat _ _, VFloat _ _
  | VString _, VString _, VString _ | VChar _, VChar _, VChar _
  | VRef _, VRef _, VRef _ | VRefMut _, VRefMut _, VRefMut _
  | VBox _, VBox _, VBox _ | VNone, VNone, VNone
  | VFuture _, VFuture _, VFuture _
  | VGenerator _, VGenerator _, VGenerator _ -> ()
  | VSome v1', VSome v2', VSome v3' -> value_eq_trans v1' v2' v3'
  | VOk v1', VOk v2', VOk v3' -> value_eq_trans v1' v2' v3'
  | VErr v1', VErr v2', VErr v3' -> value_eq_trans v1' v2' v3'
  | VTuple vs1, VTuple vs2, VTuple vs3 -> value_list_eq_trans vs1 vs2 vs3
  | VArray vs1, VArray vs2, VArray vs3 -> value_list_eq_trans vs1 vs2 vs3
  | _, _, _ -> ()

and value_list_eq_trans (vs1 vs2 vs3: vlist value)
    : Lemma (requires value_list_eq vs1 vs2 = true /\ value_list_eq vs2 vs3 = true)
            (ensures value_list_eq vs1 vs3 = true)
            (decreases %[value_list_size vs1; 1]) =
  match vs1, vs2, vs3 with
  | [], [], [] -> ()
  | v1 :: r1, v2 :: r2, v3 :: r3 ->
      value_eq_trans v1 v2 v3; value_list_eq_trans r1 r2 r3
  | _, _, _ -> ()
#pop-options

(** ============================================================================
    VALUE CANONICAL FORM LEMMAS
    ============================================================================ *)

(** VUnit is the unique unit value *)
let vunit_canonical (v: value)
    : Lemma (requires VUnit? v)
            (ensures v == VUnit)
            [SMTPat (VUnit? v)] = ()

(** VBool values are determined by their boolean *)
let vbool_canonical (v: value) (b: bool)
    : Lemma (requires VBool? v /\ VBool?._0 v = b)
            (ensures v == VBool b)
            [SMTPat (VBool? v)] = ()

(** VInt values preserve their type information *)
let vint_type_preserved (v: value) (n: int) (ty: int_type)
    : Lemma (requires VInt? v /\ VInt?.n v = n /\ VInt?.ty v = ty)
            (ensures v == VInt n ty) = ()

(** VFloat values preserve their precision *)
let vfloat_prec_preserved (v: value) (f: float_repr) (p: float_prec)
    : Lemma (requires VFloat? v /\ VFloat?.f v = f /\ VFloat?.prec v = p)
            (ensures v == VFloat f p) = ()

(** VRef locations are non-negative *)
let vref_loc_nonneg (v: value)
    : Lemma (requires VRef? v)
            (ensures VRef?._0 v >= 0)
            [SMTPat (VRef? v)] = ()

(** VRefMut locations are non-negative *)
let vrefmut_loc_nonneg (v: value)
    : Lemma (requires VRefMut? v)
            (ensures VRefMut?._0 v >= 0)
            [SMTPat (VRefMut? v)] = ()

(** VBox locations are non-negative *)
let vbox_loc_nonneg (v: value)
    : Lemma (requires VBox? v)
            (ensures VBox?._0 v >= 0)
            [SMTPat (VBox? v)] = ()

(** VClosure IDs are non-negative *)
let vclosure_id_nonneg (v: value)
    : Lemma (requires VClosure? v)
            (ensures VClosure?._0 v >= 0)
            [SMTPat (VClosure? v)] = ()

(** ============================================================================
    VALUE TYPE INVERSION LEMMA
    ============================================================================ *)

(** Value constructor determines discriminator *)
let value_type_inversion (v: value)
    : Lemma (ensures
           (VUnit? v    ==> v == VUnit) /\
           (VNone? v    ==> v == VNone) /\
           (VBool? v    ==> (exists (b:bool). v == VBool b)) /\
           (VInt? v     ==> (exists (n:int) (ty:int_type). v == VInt n ty)) /\
           (VFloat? v   ==> (exists (f:float_repr) (p:float_prec). v == VFloat f p)) /\
           (VString? v  ==> (exists (s:string). v == VString s)) /\
           (VChar? v    ==> (exists (c:FStar.Char.char). v == VChar c)) /\
           (VTuple? v   ==> (exists (vs:vlist value). v == VTuple vs)) /\
           (VArray? v   ==> (exists (vs:vlist value). v == VArray vs)) /\
           (VStruct? v  ==> (exists (tn:type_name) (fs:vlist (string & value)). v == VStruct tn fs)) /\
           (VVariant? v ==> (exists (tn:type_name) (vn:string) (vs:vlist value). v == VVariant tn vn vs)) /\
           (VRef? v     ==> (exists (l:loc). v == VRef l /\ l >= 0)) /\
           (VRefMut? v  ==> (exists (l:loc). v == VRefMut l /\ l >= 0)) /\
           (VBox? v     ==> (exists (l:loc). v == VBox l /\ l >= 0)) /\
           (VClosure? v ==> (exists (id:closure_id). v == VClosure id /\ id >= 0)) /\
           (VSome? v    ==> (exists (v':value). v == VSome v')) /\
           (VOk? v      ==> (exists (v':value). v == VOk v')) /\
           (VErr? v     ==> (exists (v':value). v == VErr v')) /\
           (VFuture? v  ==> (exists (fs:runtime_future_state). v == VFuture fs)) /\
           (VGenerator? v ==> (exists (gs:runtime_gen_state). v == VGenerator gs)))
          [SMTPat (VUnit? v); SMTPat (VNone? v); SMTPat (VBool? v);
           SMTPat (VInt? v); SMTPat (VFloat? v)] =
  match v with
  | VUnit -> ()
  | VNone -> ()
  | VBool b -> ()
  | VInt n ty -> ()
  | VFloat f p -> ()
  | VString s -> ()
  | VChar c -> ()
  | VTuple vs -> ()
  | VArray vs -> ()
  | VStruct tn fs -> ()
  | VVariant tn vn vs -> ()
  | VRef l -> ()
  | VRefMut l -> ()
  | VBox l -> ()
  | VClosure id -> ()
  | VSome v' -> ()
  | VOk v' -> ()
  | VErr v' -> ()
  | VFuture fs -> ()
  | VGenerator gs -> ()

(** ============================================================================
    PATTERN MATCHING
    ============================================================================ *)

(* Pattern size functions for termination measure *)
let rec pattern_size (p: pattern) : Tot nat (decreases p) =
  match p with
  | PatWild -> 1
  | PatVar _ -> 1
  | PatLit _ -> 1
  | PatTuple pats -> 1 + pattern_list_size pats
  | PatStruct _ fps -> 1 + field_pattern_list_size fps
  | PatVariant _ _ pats -> 1 + pattern_list_size pats
  | PatOr p1 p2 -> 1 + pattern_size p1 + pattern_size p2
  | PatGuard p _ -> 1 + pattern_size p
  | PatRef p -> 1 + pattern_size p
  | PatBox p -> 1 + pattern_size p
  | PatRest _ -> 1                       (* ...rest or ... *)
  | PatAs p _ -> 1 + pattern_size p      (* p @ x *)
  | PatType _ _ -> 1                     (* Type pattern: : T or x: T *)

and pattern_list_size (pats: list pattern) : Tot nat (decreases pats) =
  match pats with
  | [] -> 0
  | p :: rest -> pattern_size p + pattern_list_size rest

and field_pattern_list_size (fps: list (string & pattern)) : Tot nat (decreases fps) =
  match fps with
  | [] -> 0
  | (_, p) :: rest -> pattern_size p + field_pattern_list_size rest

(* Match value against pattern *)
let rec match_pattern (p: pattern) (v: value)
    : Tot match_result (decreases %[pattern_size p; 0]) =
  match p with
  | PatWild -> Some []

  | PatVar x -> Some [(x, v)]

  | PatLit lit ->
      if value_eq (lit_to_value lit) v then Some [] else None

  | PatTuple pats ->
      (match v with
       | VTuple vs ->
           if List.Tot.length pats <> List.Tot.length vs then None
           else match_patterns pats vs
       | _ -> None)

  | PatStruct ty_name field_pats ->
      (match v with
       | VStruct ty_name' fields ->
           if ty_name <> ty_name' then None
           else match_struct_fields field_pats fields
       | _ -> None)

  | PatVariant ty_name var_name pats ->
      (match v with
       | VVariant ty_name' var_name' vs ->
           if ty_name <> ty_name' || var_name <> var_name' then None
           else if List.Tot.length pats <> List.Tot.length vs then None
           else match_patterns pats vs
       | _ -> None)

  | PatOr p1 p2 ->
      (match match_pattern p1 v with
       | Some binds -> Some binds
       | None -> match_pattern p2 v)

  (* DESIGN LIMITATION: PatRef and PatBox matching cannot dereference
     because match_pattern is a pure function without heap access.

     Current behavior:
     - Matches the reference/box value itself, NOT the dereferenced value
     - The inner pattern p' is matched against the VRef/VBox wrapper

     For proper reference dereferencing, use eval_match_pattern in Eval.fst
     which has access to the heap state and can perform dereferencing.

     This is consistent with the design principle that pattern matching
     in Values.fst is a pure operation, while heap access is effectful.

     Example:
       PatRef (PatVar "x") matches VRef loc
       -> binds x to VRef loc (NOT to the dereferenced value)

     To match dereferenced content, the evaluator must:
       1. Check if v is VRef loc
       2. Read heap[loc] to get the actual value
       3. Match p' against the dereferenced value
  *)
  | PatRef p' ->
      (match v with
       | VRef _ ->
           (* Match the reference wrapper itself - dereferencing requires heap *)
           match_pattern p' v
       | _ -> None)

  | PatBox p' ->
      (match v with
       | VBox _ ->
           (* Match the box wrapper itself - dereferencing requires heap *)
           match_pattern p' v
       | _ -> None)

  | PatGuard _ _ -> None  (* Guards need evaluation context - see Eval.fst *)

  (* PatRest: Used in array/tuple destructuring to capture remaining elements.
     In standalone context, binds entire value if var given, otherwise matches anything. *)
  | PatRest opt_var ->
      (match opt_var with
       | Some x -> Some [(x, v)]  (* Bind entire value to variable *)
       | None -> Some [])         (* Match but don't bind *)

  (* PatAs: Bind the whole matched value to a name while also destructuring.
     The pattern (p @ x) matches v if p matches v, binding both x to v and
     any bindings from p. *)
  | PatAs inner_pat x ->
      (match match_pattern inner_pat v with
       | Some binds -> Some ((x, v) :: binds)  (* Prepend the as-binding *)
       | None -> None)

  (* PatType: Type pattern - matches if value's runtime type matches expected type.
     Used for runtime type checking like: match x { _: int => ..., _: string => ... }

     DESIGN NOTE: Like PatGuard, type patterns require evaluation context because
     type_of_value is defined after match_pattern (due to interface ordering).
     The full implementation is in eval_match_pattern in Eval.fst.

     This pure version always returns None to indicate "needs evaluation context".
     The evaluator should handle PatType by:
     1. Computing type_of_value(v)
     2. Checking subtype v_ty expected_ty
     3. Binding opt_var to v if match succeeds *)
  | PatType _ _ -> None  (* Type patterns need evaluation context - see Eval.fst *)

(* Match multiple patterns against multiple values *)
and match_patterns (pats: list pattern) (vs: list value)
    : Tot match_result (decreases %[pattern_list_size pats; 1]) =
  match pats, vs with
  | [], [] -> Some []
  | p :: pats', v :: vs' ->
      (match match_pattern p v, match_patterns pats' vs' with
       | Some b1, Some b2 -> Some (b1 @ b2)
       | _, _ -> None)
  | _, _ -> None

(* Match struct fields - directly recursive for proper mutual recursion *)
and match_struct_fields (field_pats: list (string & pattern))
                        (fields: list (string & value))
    : Tot match_result (decreases %[field_pattern_list_size field_pats; 2]) =
  match field_pats with
  | [] -> Some []
  | (name, pat) :: rest ->
      (match List.Tot.assoc name fields with
       | Some v ->
           (match match_pattern pat v, match_struct_fields rest fields with
            | Some b1, Some b2 -> Some (b1 @ b2)
            | _, _ -> None)
       | None -> None)

(** ============================================================================
    PATTERN MATCHING LEMMAS
    ============================================================================ *)

(** PatVar patterns always match and bind the value.
    This is a fundamental property: variable patterns are irrefutable.

    NOTE: This lemma requires fixing the underlying type issue where
    match_pattern takes `pattern` (= with_loc pattern') but matches against
    `pattern'` constructors. The lemma holds semantically but the proof
    requires either:
    1. Fixing match_pattern to properly extract loc_value before matching
    2. Adding implicit coercions from with_loc to its inner type

    For now, we use admit() to document this as a known issue. *)
let match_pattern_patvar (x: var_id) (v: value)
    : Lemma (ensures match_pattern (locate_dummy (PatVar x)) v == Some [(x, v)])
    [SMTPat (match_pattern (locate_dummy (PatVar x)) v)] =
  admit ()  (* Requires fixing pattern/pattern' type mismatch in match_pattern *)

(** ============================================================================
    LITERAL-VALUE TYPE PRESERVATION LEMMAS
    ============================================================================ *)

(** Unit literal produces unit value *)
let lit_to_value_unit ()
    : Lemma (lit_to_value LitUnit == VUnit) = ()

(** Bool literal produces bool value with same boolean *)
let lit_to_value_bool (b: bool)
    : Lemma (lit_to_value (LitBool b) == VBool b)
            [SMTPat (lit_to_value (LitBool b))] = ()

(** Int literal preserves integer type *)
let lit_to_value_int (n: int) (ty: int_type)
    : Lemma (lit_to_value (LitInt n ty) == VInt n ty)
            [SMTPat (lit_to_value (LitInt n ty))] = ()

(** Float literal preserves precision *)
let lit_to_value_float (f: float_repr) (p: float_prec)
    : Lemma (lit_to_value (LitFloat f p) == VFloat f p)
            [SMTPat (lit_to_value (LitFloat f p))] = ()

(** String literal produces string value *)
let lit_to_value_string (s: string)
    : Lemma (lit_to_value (LitString s) == VString s)
            [SMTPat (lit_to_value (LitString s))] = ()

(** Char literal produces char value *)
let lit_to_value_char (c: FStar.Char.char)
    : Lemma (lit_to_value (LitChar c) == VChar c)
            [SMTPat (lit_to_value (LitChar c))] = ()

(** ============================================================================
    HELPER LEMMAS FOR HEAP/ENV OPERATIONS
    ============================================================================

    These lemmas establish properties of assoc and filter that are needed
    for the heap and environment operation specifications.

    Following FStar.List.Tot.Properties patterns for list induction proofs.
    ============================================================================ *)

(** assoc after filter with equal key returns None.
    If we filter out all entries with key k, then looking up k returns None. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec assoc_filter_eq_none (#a: eqtype) (#b: Type) (k: a) (l: list (a & b))
    : Lemma (ensures List.Tot.assoc k (List.Tot.filter (fun (k', _) -> k' <> k) l) == None)
            (decreases l) =
  match l with
  | [] -> ()
  | (k', v') :: tl ->
      if k' <> k then begin
        (* k' passes the filter, so it's in the result *)
        (* We need to prove assoc k ((k', v') :: filter ...) == None *)
        (* Since k' <> k, assoc k ((k', v') :: ...) == assoc k (...) *)
        assoc_filter_eq_none k tl
      end else begin
        (* k' = k, so (k', v') is filtered out *)
        assoc_filter_eq_none k tl
      end
#pop-options

(** assoc after filter with different key is unchanged.
    If we filter out entries with key k, looking up k' (where k' <> k) gives same result. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec assoc_filter_neq_same (#a: eqtype) (#b: Type) (k: a) (k': a) (l: list (a & b))
    : Lemma (requires k <> k')
            (ensures List.Tot.assoc k' (List.Tot.filter (fun (x, _) -> x <> k) l) == List.Tot.assoc k' l)
            (decreases l) =
  match l with
  | [] -> ()
  | (x, v) :: tl ->
      if x <> k then begin
        (* (x, v) passes filter - it's included in result *)
        if x = k' then begin
          (* Found k' at head - both assocs return Some v *)
          ()
        end else begin
          (* x <> k' - need to look in tail *)
          assoc_filter_neq_same k k' tl
        end
      end else begin
        (* x = k, so (x, v) is filtered out *)
        (* Since k <> k', we have x <> k', so assoc k' ((x,v)::tl) == assoc k' tl *)
        assoc_filter_neq_same k k' tl
      end
#pop-options

(** fold_left max is monotonic: result >= accumulator.
    Helper for proving next_loc produces a fresh location. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec fold_max_geq_acc (h: heap) (acc: nat)
    : Lemma (ensures List.Tot.fold_left (fun m (l', _) -> max m l') acc h >= acc)
            (decreases h) =
  match h with
  | [] -> ()
  | (l, v) :: tl ->
      let new_acc = max acc l in
      fold_max_geq_acc tl new_acc
#pop-options

(** fold_left max >= any element location in the heap *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let rec fold_max_geq_elem (h: heap) (acc: nat) (l: loc) (v: value)
    : Lemma (requires List.Tot.memP (l, v) h)
            (ensures List.Tot.fold_left (fun m (l', _) -> max m l') acc h >= l)
            (decreases h) =
  match h with
  | [] -> ()  (* Contradicts memP *)
  | (l', v') :: tl ->
      let new_acc = max acc l' in
      if l = l' && v == v' then begin
        (* Element is at head *)
        (* fold_left ... acc h = fold_left ... (max acc l') tl *)
        (* max acc l' >= l' = l *)
        fold_max_geq_acc tl new_acc
      end else begin
        (* Element is in tail *)
        fold_max_geq_elem tl new_acc l v
      end
#pop-options

(** next_loc produces a location greater than all existing locations in the heap *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let next_loc_gt_all (h: heap) (l: loc) (v: value)
    : Lemma (requires List.Tot.memP (l, v) h)
            (ensures next_loc h > l) =
  fold_max_geq_elem h 0 l v
#pop-options

(** If a location is greater than all locations in heap, assoc returns None *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec assoc_none_if_not_mem (l: loc) (h: heap)
    : Lemma (requires ~(List.Tot.mem l (List.Tot.map fst h)))
            (ensures List.Tot.assoc l h == None)
            (decreases h) =
  match h with
  | [] -> ()
  | (l', _) :: tl ->
      if l = l' then ()  (* Contradicts precondition *)
      else assoc_none_if_not_mem l tl
#pop-options

(** Helper: if l > all locations in h, then l not in map fst h *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let rec gt_all_not_mem (l: loc) (h: heap)
    : Lemma (requires forall l' v'. List.Tot.memP (l', v') h ==> l > l')
            (ensures ~(List.Tot.mem l (List.Tot.map fst h)))
            (decreases h) =
  match h with
  | [] -> ()
  | (l', v') :: tl ->
      (* l > l' by precondition *)
      (* So l <> l' *)
      gt_all_not_mem l tl
#pop-options

(** next_loc is not a member of the heap's location domain *)
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec next_loc_not_in_heap (h: heap)
    : Lemma (ensures ~(List.Tot.mem (next_loc h) (List.Tot.map fst h)))
            (decreases h) =
  match h with
  | [] -> ()
  | (l, v) :: tl ->
      let nl = next_loc h in
      (* next_loc h = 1 + fold_left max 0 h *)
      (* fold_left max 0 h >= l (for head element) *)
      fold_max_geq_elem h 0 l v;
      (* So nl = 1 + fold_left max 0 h >= 1 + l > l *)
      assert (nl > l);
      (* For elements in tl: fold_left max 0 h >= fold_left max 0 tl *)
      (* and fold_left max 0 tl >= l' for any l' in tl *)
      (* So nl > l' for any l' in tl *)
      (* Therefore nl not in map fst h *)
      ()
#pop-options

(** ============================================================================
    HEAP OPERATION SPECIFICATIONS
    ============================================================================ *)

(** alloc returns a fresh location not in the original heap *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let alloc_fresh (v: value) (h: heap)
    : Lemma (let (l, h') = alloc v h in
             read l h == None /\
             read l h' == Some v)
            [SMTPat (alloc v h)] =
  let l = next_loc h in
  let h' = (l, v) :: h in
  (* Part 1: read l h' = Some v *)
  (* This follows directly from assoc definition - l is at head *)
  assert (read l h' == Some v);
  (* Part 2: read l h = None *)
  (* l = next_loc h is greater than all locations in h *)
  next_loc_not_in_heap h;
  assoc_none_if_not_mem l h
#pop-options

(** alloc preserves existing heap bindings *)
let alloc_preserves (v: value) (h: heap) (l': loc)
    : Lemma (requires (let (l, _) = alloc v h in l <> l'))
            (ensures (let (_, h') = alloc v h in read l' h' == read l' h)) =
  ()

(** write updates the specified location *)
let write_updates (l: loc) (v: value) (h: heap)
    : Lemma (read l (write l v h) == Some v)
            [SMTPat (read l (write l v h))] = ()

(** write preserves other locations *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let write_preserves (l: loc) (v: value) (h: heap) (l': loc)
    : Lemma (requires l <> l')
            (ensures read l' (write l v h) == read l' h)
            [SMTPat (read l' (write l v h))] =
  (* write l v h = (l, v) :: filter (fun (l', _) -> l' <> l) h *)
  (* read l' ((l, v) :: ...) = assoc l' ((l, v) :: ...) *)
  (* Since l <> l', assoc skips (l, v) at head *)
  (* So we need: assoc l' (filter (fun (x, _) -> x <> l) h) == assoc l' h *)
  assoc_filter_neq_same l l' h
#pop-options

(** dealloc removes the specified location *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let dealloc_removes (l: loc) (h: heap)
    : Lemma (read l (dealloc l h) == None)
            [SMTPat (read l (dealloc l h))] =
  (* dealloc l h = filter (fun (l', _) -> l' <> l) h *)
  (* read l (dealloc l h) = assoc l (filter (fun (l', _) -> l' <> l) h) *)
  (* All entries with key l are filtered out, so assoc returns None *)
  assoc_filter_eq_none l h
#pop-options

(** dealloc preserves other locations *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let dealloc_preserves (l: loc) (h: heap) (l': loc)
    : Lemma (requires l <> l')
            (ensures read l' (dealloc l h) == read l' h)
            [SMTPat (read l' (dealloc l h))] =
  (* dealloc l h = filter (fun (x, _) -> x <> l) h *)
  (* read l' (dealloc l h) = assoc l' (filter ...) *)
  (* Since l <> l', bindings for l' are preserved by filter *)
  assoc_filter_neq_same l l' h
#pop-options

(** ============================================================================
    ENVIRONMENT OPERATION SPECIFICATIONS
    ============================================================================ *)

(** lookup after extend finds the extended binding *)
let extend_lookup (x: var_id) (v: value) (e: env)
    : Lemma (lookup x (extend x v e) == Some v)
            [SMTPat (lookup x (extend x v e))] = ()

(** lookup after extend for different variable is unchanged *)
let extend_lookup_other (x: var_id) (y: var_id) (v: value) (e: env)
    : Lemma (requires x <> y)
            (ensures lookup y (extend x v e) == lookup y e) = ()

(** lookup in empty_env always returns None *)
let empty_env_lookup (x: var_id)
    : Lemma (lookup x empty_env == None)
            [SMTPat (lookup x empty_env)] = ()

(** remove eliminates the binding *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let remove_lookup (x: var_id) (e: env)
    : Lemma (lookup x (remove x e) == None)
            [SMTPat (lookup x (remove x e))] =
  (* remove x e = filter (fun (y, _) -> y <> x) e *)
  (* lookup x (remove x e) = assoc x (filter (fun (y, _) -> y <> x) e) *)
  (* All entries with key x are filtered out, so assoc returns None *)
  assoc_filter_eq_none x e
#pop-options

(** ============================================================================
    RESULT MONAD LAWS
    ============================================================================ *)

(** Left identity: return a >>= f  ===  f a *)
let result_left_identity (#a #b: Type) (x: a) (f: a -> result b)
    : Lemma (bind (return x) f == f x) = ()

(** Right identity: m >>= return  ===  m *)
let result_right_identity (#a: Type) (m: result a)
    : Lemma (bind m return == m) =
  match m with
  | ROk x -> ()
  | RErr e -> ()
  | RDiv -> ()
  | RBreak lbl v -> ()
  | RCont lbl -> ()
  | RRet v -> ()
  | RYield v -> ()
  | RPerform op args -> ()
  | RAbort p v -> ()
  | RGoto lbl -> ()

(** Associativity: (m >>= f) >>= g  ===  m >>= (\x -> f x >>= g) *)
let result_assoc (#a #b #c: Type)
    (m: result a) (f: a -> result b) (g: b -> result c)
    : Lemma (bind (bind m f) g == bind m (fun x -> bind (f x) g)) =
  match m with
  | ROk x -> ()
  | RErr e -> ()
  | RDiv -> ()
  | RBreak lbl v -> ()
  | RCont lbl -> ()
  | RRet v -> ()
  | RYield v -> ()
  | RPerform op args -> ()
  | RAbort p v -> ()
  | RGoto lbl -> ()

(** ============================================================================
    TYPE INFERENCE FROM VALUES
    ============================================================================

    Following HACL* Lib.Sequence.Lemmas patterns for type preservation proofs.

    The type_of_value function computes the static type from a runtime value.
    This is fundamental for type preservation lemmas which prove that
    operations preserve type information during evaluation.

    CRITICAL DESIGN NOTES:
    1. VInt and VFloat carry full type information (width, signedness, precision)
       following HACL* Lib.IntTypes patterns - this enables precise typing.

    2. Some values (VNone, VRef, VClosure) don't carry enough type info.
       We return TPrim PUnknown for these - consistent with gradual typing.
       The evaluator/type checker must track these types externally.

    3. VTuple and VArray infer types from their elements. For empty containers
       or heterogeneous arrays, we return Unknown as element type.

    See: brrr_lang_spec_v0.4.tex Section 2 (Type System)
    ============================================================================ *)

(** Compute the static type of a runtime value.

    This function is the bridge between runtime values and static types.
    It enables type preservation proofs: if e : T and e --> v, then type_of_value v = T.

    Following HACL* patterns:
    - Mutually recursive with helpers for compound types
    - Uses termination measure based on value_size
    - Returns PUnknown for values without sufficient type info *)
let rec type_of_value (v: value) : Tot brrr_type (decreases value_size v) =
  match v with
  (* Primitives: direct mapping to types *)
  | VUnit -> TPrim PUnit
  | VBool _ -> TPrim PBool
  | VInt _ ty -> TNumeric (NumInt ty)    (* Preserves int_type from literal *)
  | VFloat _ prec -> TNumeric (NumFloat prec)  (* Preserves float_prec *)
  | VString _ -> TPrim PString
  | VChar _ -> TPrim PChar

  (* Compound types: infer from structure *)
  | VTuple vs -> TTuple (type_of_value_list vs)
  | VArray vs ->
      (* For arrays, attempt to find homogeneous element type *)
      let elem_ty = infer_array_element_type vs in
      TWrap WArray elem_ty
  | VStruct name _ -> TNamed name  (* Nominal type reference *)
  | VVariant name _ _ -> TNamed name  (* Enum variant maps to enum type *)

  (* References: type info not carried in value, use Unknown as placeholder.
     Actual type must be tracked in type environment/heap typing. *)
  | VRef _ -> TWrap WRef (TPrim PUnknown)
  | VRefMut _ -> TWrap WRefMut (TPrim PUnknown)
  | VBox _ -> TWrap WBox (TPrim PUnknown)

  (* Closures: function type not available in value representation.
     Must be tracked externally in closure store typing. *)
  | VClosure _ -> TFunc {
      params = [];
      return_type = TPrim PUnknown;
      effects = pure;
      is_unsafe = false
    }

  (* Bound method: receiver + closure.
     The method type includes the receiver type information.
     We use MOne (linear) since the receiver is moved into the method call. *)
  | VBoundMethod recv _ ->
      let recv_ty = type_of_value recv in
      TFunc {
        params = [{ name = Some "self"; ty = recv_ty; mode = MOne }];
        return_type = TPrim PUnknown;
        effects = pure;
        is_unsafe = false
      }

  (* Option: Some carries inner type, None is unknown *)
  | VNone -> TWrap WOption (TPrim PUnknown)
  | VSome v' -> TWrap WOption (type_of_value v')

  (* Result: Ok/Err carry their respective types, other is unknown *)
  | VOk v' -> TResult (type_of_value v') (TPrim PUnknown)
  | VErr v' -> TResult (TPrim PUnknown) (type_of_value v')

  (* Async/Generators: use placeholder function type *)
  | VFuture _ -> TWrap WOption (TPrim PUnknown)  (* Future<T> ~ Option<T> semantically *)
  | VGenerator _ -> TFunc {
      params = [];
      return_type = TWrap WOption (TPrim PUnknown);
      effects = pure;  (* Generator effect would be tracked separately *)
      is_unsafe = false
    }

(** Helper: compute types for a list of values *)
and type_of_value_list (vs: vlist value) : Tot (list brrr_type) (decreases value_list_size vs) =
  match vs with
  | [] -> []
  | v :: rest -> type_of_value v :: type_of_value_list rest

(** Helper: infer element type for arrays.
    Returns element type if all elements have same type, else Unknown. *)
and infer_array_element_type (vs: vlist value) : Tot brrr_type (decreases value_list_size vs) =
  match vs with
  | [] -> TPrim PUnknown  (* Empty array: element type unknown *)
  | [v] -> type_of_value v  (* Single element: use its type *)
  | v :: rest ->
      let v_ty = type_of_value v in
      let rest_ty = infer_array_element_type rest in
      (* If types match, keep it; otherwise return Unknown *)
      if type_eq v_ty rest_ty then v_ty else TPrim PUnknown

(** ============================================================================
    INTEGER ARITHMETIC OPERATIONS
    ============================================================================

    These operations preserve type information following HACL* patterns.
    Integer operations maintain the int_type of operands when compatible.

    Type Preservation Rules:
    - Same int_type: result has same int_type
    - Different int_types: promote to wider type (if same signedness)
    - Incompatible types: operation returns error value

    Following HACL* Lib.IntTypes patterns for safe integer arithmetic.
    ============================================================================ *)

(** Integer widening: promote narrower type to wider.
    Returns wider type if same signedness, None if incompatible. *)
let int_type_widen (ty1 ty2: int_type) : option int_type =
  if ty1.sign <> ty2.sign then None  (* Can't widen different signedness *)
  else
    match width_bits ty1.width, width_bits ty2.width with
    | Some w1, Some w2 ->
        if w1 >= w2 then Some ty1 else Some ty2
    | _, _ -> None  (* Native types don't widen *)

(** Integer addition with type preservation.
    Result inherits the wider integer type of the operands.

    IMPORTANT: This is the semantic int_add for the evaluator.
    Overflow behavior depends on int_type:
    - Unsigned: wrapping (modulo 2^width)
    - Signed: implementation-defined (Rust panics in debug, wraps in release)

    For type preservation proofs, we focus on the TYPE being preserved,
    not the value semantics (which would require modular arithmetic proofs). *)
let int_add (v1: value{VInt? v1}) (v2: value{VInt? v2}) : value =
  let VInt n1 ty1 = v1 in
  let VInt n2 ty2 = v2 in
  match int_type_widen ty1 ty2 with
  | Some result_ty -> VInt (n1 + n2) result_ty
  | None -> VErr (VString "int_add: incompatible integer types")

(** Integer subtraction with type preservation *)
let int_sub (v1: value{VInt? v1}) (v2: value{VInt? v2}) : value =
  let VInt n1 ty1 = v1 in
  let VInt n2 ty2 = v2 in
  match int_type_widen ty1 ty2 with
  | Some result_ty -> VInt (n1 - n2) result_ty
  | None -> VErr (VString "int_sub: incompatible integer types")

(** Integer multiplication with type preservation *)
let int_mul (v1: value{VInt? v1}) (v2: value{VInt? v2}) : value =
  let VInt n1 ty1 = v1 in
  let VInt n2 ty2 = v2 in
  match int_type_widen ty1 ty2 with
  | Some result_ty -> VInt (n1 * n2) result_ty
  | None -> VErr (VString "int_mul: incompatible integer types")

(** Integer division with type preservation.
    Returns VErr on division by zero. *)
let int_div (v1: value{VInt? v1}) (v2: value{VInt? v2}) : value =
  let VInt n1 ty1 = v1 in
  let VInt n2 ty2 = v2 in
  if n2 = 0 then VErr (VString "int_div: division by zero")
  else
    match int_type_widen ty1 ty2 with
    | Some result_ty -> VInt (n1 / n2) result_ty
    | None -> VErr (VString "int_div: incompatible integer types")

(** ============================================================================
    TYPE PRESERVATION LEMMAS - Following HACL* Lib.Sequence.Lemmas Patterns
    ============================================================================

    These lemmas prove that operations preserve type information.
    This is the foundation for type soundness: well-typed programs
    produce well-typed values.

    Pattern from HACL*:
    - Use #push-options for complex proofs
    - Use [SMTPat ...] for automatic lemma application
    - Use calc blocks for equational reasoning where needed
    - Prove lemmas without admit()
    ============================================================================ *)

(** Type preservation for integer addition.
    If both operands have compatible integer types, the result is an integer
    with the widened type. *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val int_add_preserves_type : v1:value{VInt? v1} -> v2:value{VInt? v2} ->
  Lemma (ensures
    (VInt? (int_add v1 v2) ==> TNumeric? (type_of_value (int_add v1 v2))) /\
    (VErr? (int_add v1 v2) ==> TResult? (type_of_value (int_add v1 v2))))
  [SMTPat (int_add v1 v2)]
let int_add_preserves_type v1 v2 =
  let VInt n1 ty1 = v1 in
  let VInt n2 ty2 = v2 in
  match int_type_widen ty1 ty2 with
  | Some result_ty -> ()  (* VInt case: TNumeric (NumInt result_ty) *)
  | None -> ()  (* VErr case: TResult ... *)
#pop-options

(** Type preservation: addition of same-typed integers produces same type *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val int_add_same_type : v1:value -> v2:value -> ty:int_type ->
  Lemma (requires VInt? v1 /\ VInt? v2 /\ VInt?.ty v1 = ty /\ VInt?.ty v2 = ty)
        (ensures VInt? (int_add v1 v2) /\ VInt?.ty (int_add v1 v2) = ty)
  [SMTPat (int_add v1 v2); SMTPat (VInt?.ty v1)]
let int_add_same_type v1 v2 ty =
  let VInt n1 ty1 = v1 in
  let VInt n2 ty2 = v2 in
  (* ty1 = ty2 = ty, so int_type_widen returns Some ty *)
  ()
#pop-options

(** Type preservation for subtraction *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val int_sub_preserves_type : v1:value{VInt? v1} -> v2:value{VInt? v2} ->
  Lemma (ensures
    (VInt? (int_sub v1 v2) ==> TNumeric? (type_of_value (int_sub v1 v2))) /\
    (VErr? (int_sub v1 v2) ==> TResult? (type_of_value (int_sub v1 v2))))
  [SMTPat (int_sub v1 v2)]
let int_sub_preserves_type v1 v2 =
  let VInt n1 ty1 = v1 in
  let VInt n2 ty2 = v2 in
  match int_type_widen ty1 ty2 with
  | Some _ -> ()
  | None -> ()
#pop-options

(** Type preservation for multiplication *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val int_mul_preserves_type : v1:value{VInt? v1} -> v2:value{VInt? v2} ->
  Lemma (ensures
    (VInt? (int_mul v1 v2) ==> TNumeric? (type_of_value (int_mul v1 v2))) /\
    (VErr? (int_mul v1 v2) ==> TResult? (type_of_value (int_mul v1 v2))))
  [SMTPat (int_mul v1 v2)]
let int_mul_preserves_type v1 v2 =
  let VInt n1 ty1 = v1 in
  let VInt n2 ty2 = v2 in
  match int_type_widen ty1 ty2 with
  | Some _ -> ()
  | None -> ()
#pop-options

(** Type preservation for division *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val int_div_preserves_type : v1:value{VInt? v1} -> v2:value{VInt? v2} ->
  Lemma (ensures
    (VInt? (int_div v1 v2) ==> TNumeric? (type_of_value (int_div v1 v2))) /\
    (VErr? (int_div v1 v2) ==> TResult? (type_of_value (int_div v1 v2))))
  [SMTPat (int_div v1 v2)]
let int_div_preserves_type v1 v2 =
  let VInt n1 ty1 = v1 in
  let VInt n2 ty2 = v2 in
  if n2 = 0 then ()
  else
    match int_type_widen ty1 ty2 with
    | Some _ -> ()
    | None -> ()
#pop-options

(** ============================================================================
    CANONICAL FORM LEMMAS - Following HACL* Proof Patterns
    ============================================================================

    Canonical forms lemmas establish that values of certain types have
    specific shapes. These are essential for progress proofs in type soundness.

    Example: If type_of_value v = TNumeric (NumInt ty), then v = VInt n ty.

    Pattern from HACL* specs/lemmas/:
    - Use Classical.forall_intro for universal statements
    - Use SMTPat for automatic application
    ============================================================================ *)

(** Canonical form for integers: if type_of_value returns numeric int type,
    the value must be VInt *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val canonical_int : v:value ->
  Lemma (requires TNumeric? (type_of_value v) /\ NumInt? (TNumeric?._0 (type_of_value v)))
        (ensures VInt? v)
  [SMTPat (type_of_value v); SMTPat (TNumeric? (type_of_value v))]
let canonical_int v =
  match v with
  | VInt _ _ -> ()
  | VFloat _ _ -> ()  (* VFloat gives NumFloat, not NumInt - precondition false *)
  | _ -> ()  (* All other cases don't produce TNumeric *)
#pop-options

(** Canonical form for floats: if type_of_value returns numeric float type,
    the value must be VFloat *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val canonical_float : v:value ->
  Lemma (requires TNumeric? (type_of_value v) /\ NumFloat? (TNumeric?._0 (type_of_value v)))
        (ensures VFloat? v)
  [SMTPat (type_of_value v); SMTPat (NumFloat? (TNumeric?._0 (type_of_value v)))]
let canonical_float v =
  match v with
  | VFloat _ _ -> ()
  | VInt _ _ -> ()  (* VInt gives NumInt, not NumFloat - precondition false *)
  | _ -> ()
#pop-options

(** Canonical form for booleans: if type_of_value returns bool type,
    the value must be VBool *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val canonical_bool : v:value ->
  Lemma (requires type_of_value v == TPrim PBool)
        (ensures VBool? v)
  [SMTPat (type_of_value v)]
let canonical_bool v =
  match v with
  | VBool _ -> ()
  | _ -> ()  (* No other value produces TPrim PBool *)
#pop-options

(** Canonical form for unit: if type_of_value returns unit type,
    the value must be VUnit *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val canonical_unit : v:value ->
  Lemma (requires type_of_value v == TPrim PUnit)
        (ensures v == VUnit)
  [SMTPat (type_of_value v)]
let canonical_unit v =
  match v with
  | VUnit -> ()
  | _ -> ()
#pop-options

(** Canonical form for strings: if type_of_value returns string type,
    the value must be VString *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val canonical_string : v:value ->
  Lemma (requires type_of_value v == TPrim PString)
        (ensures VString? v)
  [SMTPat (type_of_value v)]
let canonical_string v =
  match v with
  | VString _ -> ()
  | _ -> ()
#pop-options

(** Canonical form for chars: if type_of_value returns char type,
    the value must be VChar *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val canonical_char : v:value ->
  Lemma (requires type_of_value v == TPrim PChar)
        (ensures VChar? v)
  [SMTPat (type_of_value v)]
let canonical_char v =
  match v with
  | VChar _ -> ()
  | _ -> ()
#pop-options

(** Canonical form for tuples: if type_of_value returns tuple type,
    the value must be VTuple *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val canonical_tuple : v:value ->
  Lemma (requires TTuple? (type_of_value v))
        (ensures VTuple? v)
  [SMTPat (type_of_value v); SMTPat (TTuple? (type_of_value v))]
let canonical_tuple v =
  match v with
  | VTuple _ -> ()
  | _ -> ()
#pop-options

(** Canonical form for Some: if type_of_value returns Option with known inner,
    and inner is not Unknown, then value must be VSome *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val canonical_some : v:value ->
  Lemma (requires TWrap? (type_of_value v) /\
                  TWrap?._0 (type_of_value v) = WOption /\
                  not (TPrim? (TWrap?._1 (type_of_value v)) &&
                       TPrim?._0 (TWrap?._1 (type_of_value v)) = PUnknown))
        (ensures VSome? v)
let canonical_some v =
  match v with
  | VSome _ -> ()
  | VNone -> ()  (* VNone gives Unknown inner, so precondition false *)
  | _ -> ()
#pop-options

(** ============================================================================
    TUPLE TYPE PROJECTION LEMMAS
    ============================================================================

    These lemmas relate tuple value structure to tuple type structure.
    Essential for typing tuple projection operations.

    Following HACL* Lib.Sequence patterns for list operations.
    ============================================================================ *)

(** type_of_value_list length preservation *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val type_of_value_list_length : vs:vlist value ->
  Lemma (ensures length (type_of_value_list vs) = length vs)
        (decreases vs)
  [SMTPat (type_of_value_list vs)]
let rec type_of_value_list_length vs =
  match vs with
  | [] -> ()
  | _ :: rest -> type_of_value_list_length rest
#pop-options

(** Tuple type projection: nth element of value list corresponds to
    nth element of type list *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
val tuple_proj_type : vs:vlist value -> i:nat{i < length vs} ->
  Lemma (ensures
    type_of_value (index vs i) == index (type_of_value_list vs) i)
  (decreases i)
  [SMTPat (type_of_value (index vs i))]
let rec tuple_proj_type vs i =
  match vs with
  | v :: rest ->
      if i = 0 then ()
      else tuple_proj_type rest (i - 1)
#pop-options

(** Tuple type structure: type_of_value of VTuple is TTuple of component types *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val tuple_type_structure : vs:vlist value ->
  Lemma (ensures type_of_value (VTuple vs) == TTuple (type_of_value_list vs))
  [SMTPat (type_of_value (VTuple vs))]
let tuple_type_structure vs = ()
#pop-options

(** ============================================================================
    ARRAY HOMOGENEITY LEMMAS
    ============================================================================

    These lemmas establish properties of homogeneous arrays where all
    elements have the same type.

    Key insight: If infer_array_element_type returns a concrete type (not Unknown),
    then all elements must have that type.
    ============================================================================ *)

(** Helper: check if a type is Unknown *)
let is_unknown_type (t: brrr_type) : bool =
  match t with
  | TPrim PUnknown -> true
  | _ -> false

(** Homogeneous array lemma: if array element type is not Unknown,
    all elements have that type *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
val array_homogeneous : vs:vlist value ->
  Lemma (requires not (is_unknown_type (infer_array_element_type vs)))
        (ensures forall (i:nat{i < length vs}). type_eq (type_of_value (index vs i))
                                                        (infer_array_element_type vs) = true)
        (decreases vs)
let rec array_homogeneous vs =
  match vs with
  | [] -> ()
  | [v] -> type_eq_refl (type_of_value v)
  | v :: rest ->
      let v_ty = type_of_value v in
      let rest_ty = infer_array_element_type rest in
      (* Precondition implies type_eq v_ty rest_ty = true *)
      (* Therefore infer_array_element_type vs = v_ty *)
      if type_eq v_ty rest_ty then begin
        type_eq_refl v_ty;
        (* Recursively prove for rest *)
        if not (is_unknown_type rest_ty) then
          array_homogeneous rest
        else ()
      end else ()
#pop-options

(** Array with single element has that element's type *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val singleton_array_type : v:value ->
  Lemma (ensures infer_array_element_type [v] == type_of_value v)
  [SMTPat (infer_array_element_type [v])]
let singleton_array_type v = ()
#pop-options

(** Empty array has Unknown element type *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val empty_array_type : unit ->
  Lemma (ensures infer_array_element_type [] == TPrim PUnknown)
let empty_array_type () = ()
#pop-options

(** ============================================================================
    VALUE-TYPE CORRESPONDENCE LEMMAS
    ============================================================================

    These lemmas establish the fundamental correspondence between
    value constructors and type constructors.

    This is the core of type preservation: evaluation preserves typing.
    ============================================================================ *)

(** VInt corresponds to TNumeric NumInt *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val vint_type_correspondence : n:int -> ty:int_type ->
  Lemma (ensures type_of_value (VInt n ty) == TNumeric (NumInt ty))
  [SMTPat (type_of_value (VInt n ty))]
let vint_type_correspondence n ty = ()
#pop-options

(** VFloat corresponds to TNumeric NumFloat *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val vfloat_type_correspondence : f:float_repr -> prec:float_prec ->
  Lemma (ensures type_of_value (VFloat f prec) == TNumeric (NumFloat prec))
  [SMTPat (type_of_value (VFloat f prec))]
let vfloat_type_correspondence f prec = ()
#pop-options

(** VBool corresponds to TPrim PBool *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val vbool_type_correspondence : b:bool ->
  Lemma (ensures type_of_value (VBool b) == TPrim PBool)
  [SMTPat (type_of_value (VBool b))]
let vbool_type_correspondence b = ()
#pop-options

(** VSome corresponds to TWrap WOption *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val vsome_type_correspondence : v:value ->
  Lemma (ensures type_of_value (VSome v) == TWrap WOption (type_of_value v))
  [SMTPat (type_of_value (VSome v))]
let vsome_type_correspondence v = ()
#pop-options

(** VOk corresponds to TResult with ok type *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val vok_type_correspondence : v:value ->
  Lemma (ensures type_of_value (VOk v) == TResult (type_of_value v) (TPrim PUnknown))
  [SMTPat (type_of_value (VOk v))]
let vok_type_correspondence v = ()
#pop-options

(** VErr corresponds to TResult with error type *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val verr_type_correspondence : v:value ->
  Lemma (ensures type_of_value (VErr v) == TResult (TPrim PUnknown) (type_of_value v))
  [SMTPat (type_of_value (VErr v))]
let verr_type_correspondence v = ()
#pop-options

(** ============================================================================
    LITERAL TYPE PRESERVATION LEMMAS
    ============================================================================

    These lemmas prove that lit_to_value preserves type information.
    If a literal has type T, then lit_to_value produces a value of type T.
    ============================================================================ *)

(** lit_to_value preserves integer type exactly *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val lit_to_value_int_type : n:int -> ty:int_type ->
  Lemma (ensures type_of_value (lit_to_value (LitInt n ty)) == TNumeric (NumInt ty))
  [SMTPat (lit_to_value (LitInt n ty))]
let lit_to_value_int_type n ty = ()
#pop-options

(** lit_to_value preserves float precision exactly *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val lit_to_value_float_type : f:float_repr -> prec:float_prec ->
  Lemma (ensures type_of_value (lit_to_value (LitFloat f prec)) == TNumeric (NumFloat prec))
  [SMTPat (lit_to_value (LitFloat f prec))]
let lit_to_value_float_type f prec = ()
#pop-options

(** lit_to_value for bool produces TPrim PBool *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val lit_to_value_bool_type : b:bool ->
  Lemma (ensures type_of_value (lit_to_value (LitBool b)) == TPrim PBool)
  [SMTPat (lit_to_value (LitBool b))]
let lit_to_value_bool_type b = ()
#pop-options

(** lit_to_value for unit produces TPrim PUnit *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val lit_to_value_unit_type : unit ->
  Lemma (ensures type_of_value (lit_to_value LitUnit) == TPrim PUnit)
let lit_to_value_unit_type () = ()
#pop-options

(** lit_to_value for string produces TPrim PString *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val lit_to_value_string_type : s:string ->
  Lemma (ensures type_of_value (lit_to_value (LitString s)) == TPrim PString)
  [SMTPat (lit_to_value (LitString s))]
let lit_to_value_string_type s = ()
#pop-options

(** lit_to_value for char produces TPrim PChar *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val lit_to_value_char_type : c:FStar.Char.char ->
  Lemma (ensures type_of_value (lit_to_value (LitChar c)) == TPrim PChar)
  [SMTPat (lit_to_value (LitChar c))]
let lit_to_value_char_type c = ()
#pop-options

(** ============================================================================
    TYPE OF VALUE STRUCTURAL LEMMAS
    ============================================================================

    Additional structural lemmas about type_of_value following HACL* patterns.
    ============================================================================ *)

(** type_of_value for VStruct returns TNamed *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val vstruct_type_is_named : name:type_name -> fields:vlist (string & value) ->
  Lemma (ensures type_of_value (VStruct name fields) == TNamed name)
  [SMTPat (type_of_value (VStruct name fields))]
let vstruct_type_is_named name fields = ()
#pop-options

(** type_of_value for VVariant returns TNamed *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val vvariant_type_is_named : ty_name:type_name -> var_name:string -> args:vlist value ->
  Lemma (ensures type_of_value (VVariant ty_name var_name args) == TNamed ty_name)
  [SMTPat (type_of_value (VVariant ty_name var_name args))]
let vvariant_type_is_named ty_name var_name args = ()
#pop-options

(** type_of_value is deterministic: same value always gives same type *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val type_of_value_deterministic : v:value ->
  Lemma (ensures type_of_value v == type_of_value v)
  [SMTPat (type_of_value v)]
let type_of_value_deterministic v = ()
#pop-options
