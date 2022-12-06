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