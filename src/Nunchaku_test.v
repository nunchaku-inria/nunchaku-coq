(* tests for the tactic Nunchaku *)

Require Import Nunchaku.

Set Info Level 10.

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
    nunchaku warn.
  Abort.

End simple_types.


Module inductive.

  Inductive mynat := Z | S : mynat -> mynat.

  Goal Z = S Z.
  Proof.
    nunchaku warn.
  Abort.

  Inductive Tree := L | N : Tree -> Tree -> Tree.

  Goal L = N L (N L L).
  Proof.
    nunchaku warn.
  Abort.

  Inductive Even := EZ | ES : Odd -> Even
  with Odd := OS : Even -> Odd.

  Goal EZ = ES (OS EZ).
  Proof.
   nunchaku warn.

End inductive.

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
  nunchaku warn.
Abort.

End Section.

Goal (forall (a:Type) p (x:a), p x \/ ~ (p x)).
Proof.
  nunchaku warn.
Abort.