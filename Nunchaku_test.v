(* tests for the tactic Nunchaku *)

Load Nunchaku.

Variable A B : Prop.

Goal A -> B.
Proof.
  nunchaku.
  Abort.
Qed.

