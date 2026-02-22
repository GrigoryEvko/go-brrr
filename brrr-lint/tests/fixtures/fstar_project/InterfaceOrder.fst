module InterfaceOrder

(* FST002: Declarations in different order than .fsti *)

let helper_c (x: int) : int = x + 3

let helper_b (x: int) : int = x + 2

let helper_a (x: int) : int = x + 1

(* Main functions - these are out of order compared to .fsti *)
let process_data (x: int) : int =
  helper_a (helper_b (helper_c x))

let transform_value (x: int) : int =
  x * 2

let validate_input (x: int) : bool =
  x >= 0
