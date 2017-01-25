(* tests for the tactic Nunchaku *)

Require Import Nunchaku.

Module pure_logic.

  Goal (False -> False) -> False.
  Proof.
    nunchaku warn.
  Abort.

End pure_logic.

Module simple_types.

  Definition A := unit.

  Goal (fun x:A => x) = (fun x:A => x).
  Proof.
    nunchaku_warn.
  Qed.

End simple_types.

Section sec1.

Inductive mynat := Z | S : mynat -> mynat.

Variable A B : Prop.

Fixpoint p (n:mynat): Prop :=
  match n with
  | Z => True
  | S Z => False
  | S (S n) => p n
  end.

Definition n_4 : mynat := S (S (S (S Z))).

(* make A true, so that we can still have a counterex
  to A->B *)
Axiom def_a : A = p n_4.

Goal p n_4 /\ A -> B.
Proof.
  nunchaku.
  Abort.
Qed.

End Section.

Goal (forall (a:Type) p (x:a), p x \/ ~ (p x)).
Proof.
  nunchaku_warn.
Abort.