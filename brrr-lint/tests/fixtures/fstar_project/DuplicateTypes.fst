module DuplicateTypes

(** This type is duplicated in both .fst and .fsti - FST001 should flag it *)
type sec_level =
  | Public       : sec_level
  | Confidential : sec_level
  | Secret       : sec_level

(** This noeq record is also duplicated *)
noeq type labeled_value = {
  value : int;
  label : sec_level;
}

(** Private types should NOT be flagged even if they appear in .fsti *)
private type internal_state = nat

(** This type differs from .fsti - should NOT offer autofix *)
type mismatched_type =
  | VariantA : mismatched_type
  | VariantB : mismatched_type

let classify (x: int) : sec_level =
  if x > 100 then Secret
  else if x > 10 then Confidential
  else Public

let create_labeled (v: int) (l: sec_level) : labeled_value =
  { value = v; label = l }
