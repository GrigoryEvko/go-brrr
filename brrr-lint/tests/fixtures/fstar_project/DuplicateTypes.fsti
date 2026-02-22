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

(** This type differs from .fst - should NOT offer autofix *)
type mismatched_type =
  | VariantA : mismatched_type
  | VariantB : mismatched_type
  | VariantC : mismatched_type

val classify : int -> sec_level

val create_labeled : int -> sec_level -> labeled_value
