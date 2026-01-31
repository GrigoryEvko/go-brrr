(** ============================================================================
    BrrrTypeJoin.fsti - Type Join/Meet (Lattice Operations) Interface
    ============================================================================

    This module provides type lattice operations for:
    - Conditional expression typing (if-then-else)
    - Pattern matching arm type unification
    - Gradual typing consistent subtyping

    ============================================================================ *)

module BrrrTypeJoin

open FStar.List.Tot
open BrrrPrimitives
open BrrrTypes
open BrrrModes
open BrrrEffects

(** --------------------------------------------------------------------------
    RESULT TYPES
    -------------------------------------------------------------------------- *)

(** Result of type join (least upper bound) computation *)
noeq type type_lub_result =
  | LUBOk   : result:brrr_type -> type_lub_result
  | LUBFail : t1:brrr_type -> t2:brrr_type -> type_lub_result

(** Result of type meet (greatest lower bound) computation *)
noeq type type_glb_result =
  | GLBOk   : result:brrr_type -> type_glb_result
  | GLBFail : t1:brrr_type -> t2:brrr_type -> type_glb_result

(** Monadic bind for LUB results *)
val lub_bind : r:type_lub_result -> f:(brrr_type -> type_lub_result) -> type_lub_result

(** Monadic bind for GLB results *)
val glb_bind : r:type_glb_result -> f:(brrr_type -> type_glb_result) -> type_glb_result

(** --------------------------------------------------------------------------
    NUMERIC TYPE HELPERS (must precede type_join since they are used by it)
    -------------------------------------------------------------------------- *)

(** Join two int_width values: take the maximum width *)
val width_join : w1:int_width -> w2:int_width -> int_width

(** Meet two int_width values: take the minimum width *)
val width_meet : w1:int_width -> w2:int_width -> int_width

(** Join two signedness values *)
val signedness_join : s1:signedness -> s2:signedness -> signedness

(** Meet two signedness values *)
val signedness_meet : s1:signedness -> s2:signedness -> option signedness

(** Join two integer types *)
val int_type_join : i1:int_type -> i2:int_type -> int_type

(** Join two float precisions *)
val float_prec_join : f1:float_prec -> f2:float_prec -> float_prec

(** Join two numeric types *)
val numeric_type_join : n1:numeric_type -> n2:numeric_type -> option numeric_type

(** Row intersection for effect meet *)
val row_intersect : r1:effect_row -> r2:effect_row -> effect_row

(** --------------------------------------------------------------------------
    CORE LATTICE OPERATIONS
    -------------------------------------------------------------------------- *)

(** Compute the least upper bound (join) of two types.
    Returns LUBOk t if a join exists, LUBFail if incompatible.

    Key properties:
    - t1 <: type_join t1 t2
    - t2 <: type_join t1 t2
    - For any T: t1 <: T and t2 <: T implies type_join t1 t2 <: T *)
val type_join : t1:brrr_type -> t2:brrr_type -> Tot type_lub_result (decreases t1)

(** Compute the greatest lower bound (meet) of two types.
    Returns GLBOk t if a meet exists, GLBFail if incompatible.

    Key properties:
    - type_meet t1 t2 <: t1
    - type_meet t1 t2 <: t2
    - For any T: T <: t1 and T <: t2 implies T <: type_meet t1 t2 *)
val type_meet : t1:brrr_type -> t2:brrr_type -> Tot type_glb_result (decreases t1)

(** --------------------------------------------------------------------------
    HELPER OPERATIONS
    -------------------------------------------------------------------------- *)

(** Join a list of types element-wise *)
val type_join_list : ts1:list brrr_type -> ts2:list brrr_type ->
  Tot (option (list brrr_type)) (decreases ts1)

(** Meet a list of types element-wise *)
val type_meet_list : ts1:list brrr_type -> ts2:list brrr_type ->
  Tot (option (list brrr_type)) (decreases ts1)

(** Meet parameter types *)
val type_meet_params : ps1:list param_type -> ps2:list param_type ->
  Tot (option (list param_type)) (decreases ps1)

(** Join parameter types *)
val type_join_params : ps1:list param_type -> ps2:list param_type ->
  Tot (option (list param_type)) (decreases ps1)

(** --------------------------------------------------------------------------
    CONVENIENCE FUNCTIONS
    -------------------------------------------------------------------------- *)

(** Type for conditional branches: join of then and else types *)
val type_conditional_branches : then_ty:brrr_type -> else_ty:brrr_type -> type_lub_result

(** Type for match arms: fold join over all arm types *)
val type_match_arms_lub : tys:list brrr_type -> type_lub_result

(** Unwrap LUB result, returning Dynamic if no join exists *)
val type_join_or_dynamic : t1:brrr_type -> t2:brrr_type -> brrr_type

(** Check if two types have a valid join *)
val types_have_join : t1:brrr_type -> t2:brrr_type -> bool

(** --------------------------------------------------------------------------
    LATTICE LAW LEMMAS
    -------------------------------------------------------------------------- *)

(** Join is commutative *)
val type_join_comm : t1:brrr_type -> t2:brrr_type ->
  Lemma (type_join t1 t2 == type_join t2 t1)
        [SMTPat (type_join t1 t2)]

(** Meet is commutative *)
val type_meet_comm : t1:brrr_type -> t2:brrr_type ->
  Lemma (type_meet t1 t2 == type_meet t2 t1)
        [SMTPat (type_meet t1 t2)]

(** Never is bottom for join *)
val type_join_never_left : t:brrr_type ->
  Lemma (type_join (TPrim PNever) t == LUBOk t)

(** Dynamic is top for join *)
val type_join_dynamic_right : t:brrr_type ->
  Lemma (type_join t (TPrim PDynamic) == LUBOk (TPrim PDynamic))

(** Same types have trivial join *)
val type_join_refl : t:brrr_type ->
  Lemma (type_join t t == LUBOk t)
