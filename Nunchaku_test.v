(* tests for the tactic Nunchaku *)

Require Import Nunchaku.
Require Import Nunchaku.Nunchaku.

Variable A B : Prop.

Goal A -> B.
Proof.
  nunchaku.
  Abort.
Qed.

