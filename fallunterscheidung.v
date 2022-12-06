Require Import Classical_Prop.

Section Fallunterscheidung.
Variables x y: Prop. (* x = psi; y = phi*)
Lemma FU: ((x -> y) /\ (~x -> y)) -> y.
Proof.
    intro A.
    destruct A as [A B].
    (*Widerspruchsbeweis*)
    apply NNPP.
    intro C.
    assert (~x) as D.
    intro E.
        assert (y).
        apply A.
        exact E.
    contradiction. (*y and ~y*)
        assert (y).
        apply B.
        exact D.
    contradiction. (*y and ~y*)
Qed.
End Fallunterscheidung.

Parameters A B: Prop.

Theorem GD: (A -> B) \/ (B -> A).
Proof.
    apply FU with (x := A).
    split.
    intro.
    right.
    intro.
    assumption.

    intro.
    left.
    intro.
    contradiction.
Qed.

Theorem PL: ((A -> B) -> A) -> A.
Proof.
    apply FU with (x := A).
    split.
        intro C.
        intro D.
        exact C.
        intro C.
        intro D.
        assert (A -> B).
            intro E.
            contradiction.
        apply D.
        exact H.
Qed.


    