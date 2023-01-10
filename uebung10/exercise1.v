Require Import Classical.

Parameter S: Set.
Parameter c d: S.

(*Praedikate*)
Parameter D P Q: S -> Prop.
Parameter L: S -> S -> Prop.

Axiom A1: forall x, D x -> exists y, P y /\ L y x.
Axiom A2: forall x, P x -> forall y, Q y -> ~L x y.

Theorem T: forall x, D x -> ~Q x.
Proof.
  intro c.
  intro.
  intro.

  pose proof A1 as A1.
  pose proof A2 as A2.

  assert (exists y, P y /\ L y c).
  apply A1.
  assumption.

  destruct H1 as [d H1].
  destruct H1 as [H1 H2].

  assert (~L d c).
  apply A2.
  assumption.
  assumption.
  
  contradiction.
Qed.