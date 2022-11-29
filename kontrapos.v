Require Import Classical_Prop.

Parameters A B C: Prop.

Theorem Kontrapos: (A -> B) -> (~B -> ~A).
Proof.
    intro H.
    intro H1.
    intro H2.
    assert (B).
    apply H.
    exact H2.
    contradiction.
Qed.
