module UnusedOpens

(* FST004: These opens are unused and should be flagged *)
open FStar.List.Tot
open FStar.Seq
open FStar.Set

(* This open is actually used *)
open FStar.Math.Lemmas

let square (x: nat) : nat =
  x * x

(* Using FStar.Math.Lemmas makes it "used" *)
let lemma_square_positive (x: nat) : Lemma (square x >= 0) =
  ()

(* Simple function not using any imported modules *)
let add (x y: int) : int = x + y

let mul (x y: int) : int = x * y
