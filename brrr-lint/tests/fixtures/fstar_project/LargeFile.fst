module LargeFile

(* Large file for stress testing - 1000+ lines equivalent content *)

open FStar.List.Tot
open FStar.Seq
open FStar.Set
open FStar.Map

(* Multiple types for testing *)
type status =
  | Pending
  | Active
  | Complete
  | Failed

noeq type record_001 = { field001: int; status001: status }
noeq type record_002 = { field002: int; status002: status }
noeq type record_003 = { field003: int; status003: status }
noeq type record_004 = { field004: int; status004: status }
noeq type record_005 = { field005: int; status005: status }
noeq type record_006 = { field006: int; status006: status }
noeq type record_007 = { field007: int; status007: status }
noeq type record_008 = { field008: int; status008: status }
noeq type record_009 = { field009: int; status009: status }
noeq type record_010 = { field010: int; status010: status }

(* Multiple functions for testing *)
let func_001 (x: int) : int = x + 1
let func_002 (x: int) : int = x + 2
let func_003 (x: int) : int = x + 3
let func_004 (x: int) : int = x + 4
let func_005 (x: int) : int = x + 5
let func_006 (x: int) : int = x + 6
let func_007 (x: int) : int = x + 7
let func_008 (x: int) : int = x + 8
let func_009 (x: int) : int = x + 9
let func_010 (x: int) : int = x + 10
let func_011 (x: int) : int = x + 11
let func_012 (x: int) : int = x + 12
let func_013 (x: int) : int = x + 13
let func_014 (x: int) : int = x + 14
let func_015 (x: int) : int = x + 15
let func_016 (x: int) : int = x + 16
let func_017 (x: int) : int = x + 17
let func_018 (x: int) : int = x + 18
let func_019 (x: int) : int = x + 19
let func_020 (x: int) : int = x + 20

(* Private unused functions for dead code detection *)
private let unused_001 (x: int) : int = x * 1
private let unused_002 (x: int) : int = x * 2
private let unused_003 (x: int) : int = x * 3
private let unused_004 (x: int) : int = x * 4
private let unused_005 (x: int) : int = x * 5
private let unused_006 (x: int) : int = x * 6
private let unused_007 (x: int) : int = x * 7
private let unused_008 (x: int) : int = x * 8
private let unused_009 (x: int) : int = x * 9
private let unused_010 (x: int) : int = x * 10

(* Functions with unused parameters *)
let with_unused_param_001 (x: int) (_y: int) : int = x
let with_unused_param_002 (x: int) (_y: int) : int = x
let with_unused_param_003 (x: int) (_y: int) : int = x
let with_unused_param_004 (x: int) (_y: int) : int = x
let with_unused_param_005 (x: int) (_y: int) : int = x

(* Redundant refinements *)
let redundant_001 (x: nat{x >= 0}) : nat = x
let redundant_002 (x: nat{x >= 0}) : nat = x
let redundant_003 (x: nat{x >= 0}) : nat = x
let redundant_004 (x: nat{x >= 0}) : nat = x
let redundant_005 (x: nat{x >= 0}) : nat = x

(* Public entry points *)
let main_001 () : int = func_001 0
let main_002 () : int = func_002 0
let main_003 () : int = func_003 0

(* Continue with more content to make this a large file... *)
let compose_001 (x: int) : int = func_001 (func_002 x)
let compose_002 (x: int) : int = func_003 (func_004 x)
let compose_003 (x: int) : int = func_005 (func_006 x)
let compose_004 (x: int) : int = func_007 (func_008 x)
let compose_005 (x: int) : int = func_009 (func_010 x)

(* Nested structures *)
let nested_001 (x: int) : int =
  let a = x + 1 in
  let b = a + 2 in
  let c = b + 3 in
  c

let nested_002 (x: int) : int =
  let a = x * 2 in
  let b = a * 3 in
  let c = b * 4 in
  c

let nested_003 (x: int) : int =
  if x > 0 then
    if x > 10 then
      if x > 100 then x * 1000
      else x * 100
    else x * 10
  else x

(* End of large file *)
let final_function (x: int) : int =
  nested_001 (nested_002 (nested_003 x))
