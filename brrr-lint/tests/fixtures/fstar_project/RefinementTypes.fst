module RefinementTypes

(* FST012: Refinement type simplifier *)

(* Redundant refinement: nat already implies x >= 0 *)
let redundant_nat (x: nat{x >= 0}) : nat = x

(* Promotable: int with x >= 0 could be nat *)
let promotable_to_nat (x: int{x >= 0}) : int = x + 1

(* Useless refinement: True is always true *)
let useless_refinement (x: int{True}) : int = x

(* Valid refinement - should NOT be flagged *)
let valid_refinement (x: nat{x > 0 /\ x < 100}) : nat = x

(* Another redundant: pos already implies x > 0 *)
let redundant_pos (x: pos{x > 0}) : pos = x

(* Complex but valid refinement *)
let bounded_add (x: nat{x < 1000}) (y: nat{y < 1000}) : nat{result:nat{result < 2000}} =
  x + y
