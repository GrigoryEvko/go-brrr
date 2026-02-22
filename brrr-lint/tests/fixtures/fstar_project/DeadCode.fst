module DeadCode

(* FST005: Dead code detection *)

(* Unused private binding - should be flagged *)
private let unused_helper (x: int) : int = x + 1

(* Used private binding - should NOT be flagged *)
private let used_helper (x: int) : int = x * 2

(* Unused parameter in function *)
let function_with_unused_param (x: int) (_unused: string) : int =
  x + 1

(* Code after assert false - unreachable *)
let unreachable_code (x: int) : int =
  if x < 0 then (
    assert false;
    x + 100  (* This is unreachable *)
  ) else
    x

(* Unused match arm after wildcard *)
let match_with_dead_arm (x: int) : string =
  match x with
  | 0 -> "zero"
  | 1 -> "one"
  | _ -> "other"
  (* | 2 -> "two"  -- would be dead code if uncommented *)

(* Public function using the private helper *)
let public_function (x: int) : int =
  used_helper x
