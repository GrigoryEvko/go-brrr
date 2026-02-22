module MissingDocs

(* FST013: Documentation checker *)

(* This val is missing documentation *)
val undocumented_function : int -> int

(** This val has proper documentation *)
val documented_function : int -> int

(* This type is missing documentation *)
type config = {
  debug: bool;
  level: nat;
}

(** Documented type *)
type documented_config = {
  name: string;
  value: int;
}

let undocumented_function x = x + 1

let documented_function x = x * 2

(* Private items don't need docs *)
private let internal_helper x = x
