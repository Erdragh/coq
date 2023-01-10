Require Import Classical.

Parameter D: Set.
Parameter c d: D.

Parameter P Q: D -> Prop.

(*Beispiel 1*)
Theorem T1: (forall x, P x) /\ (forall x, P x -> Q x) -> (forall x, Q x).
Proof.
  intro.
  destruct H as [H0 H1].
  intro c.
    (*Unterbeweis*)
    apply H1.
    apply H0.
Qed.

(*Beispiel 2*)
Theorem T2: (exists x, P x) /\ (forall x, P x -> Q x) -> (exists x, Q x).
Proof.
  intro.
  destruct H as [H0 H1].
  (*Unterbeweis durch Elimination des Existenzquantors*)
    destruct H0 as [d H0].
    (*Existenzquantor im Ziel fuer d beweisen*)
    exists d.
      apply H1.
  assumption.
Qed.