Require Import Classical_Prop.

Section Fallunterscheidung.
Variables x y: Prop. (* x = psi; y = phi *)
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
        apply D.
        intro E.
        contradiction.
Qed.

Theorem TDN: A \/ ~A.
Proof.
    apply FU with (x := A).
    split.
    intro.
    left.
    assumption.
    intro.
    right.
    assumption.
Qed.

(*
I could probably have used assumption a lot in here,
but I think using names is more readable.

In the future I probably will use it, because it means
less work to write things down, but also less readibility,
which I think is important when first learning about programming
concepts, as I want to go back and take a look at the code
and understand what it's doing.
*)

Theorem FirstExercise: ((A \/ B) -> (A /\ B)) -> ((~A \/ B) /\ (A \/ ~B)).
Proof.
    intro Implication.
    apply FU with (x := (A \/ B)).
    split.
        intro A_or_B.
        (*Proof for the left side.*)
        split.
        assert (A /\ B) as A_and_B.
            apply Implication.
            exact A_or_B.
            destruct A_and_B as [_ yesB].
        right.
        exact yesB.
        assert (A /\ B) as A_and_B.
            apply Implication.
            exact A_or_B.
            destruct A_and_B as [yesA _].
        left.
        exact yesA.

        (*Proof for the right side.*)
        intro not_A_or_B.
        assert (~A /\ ~B) as notA_and_notB.
        split.
        intro yesA.
            assert (A \/ B) as A_or_B.
            left.
            exact yesA.
        contradiction.
        intro yesB.
            assert (A \/ B) as A_or_B.
            right.
            exact yesB.
        contradiction.
        destruct notA_and_notB as [notA notB].

        split.
        left.
        exact notA.
        right.
        exact notB.
Qed.

Theorem SecondExercise: ((A -> (~B \/ ~A)) -> ((A -> ~B) \/ ~B)).
Proof.
    intro Implication.
    left.
    intro yesA.
    assert (~B \/ ~A) as notB_or_notA.
        apply Implication.
        exact yesA.
    destruct notB_or_notA.
    exact H.
    contradiction.
Qed.

Parameters C: Prop.

Theorem ThirdExercise: ((A /\ (B \/ C)) -> ((A /\ B) \/ (A /\C))).
Proof.
    intro A_and__B_or_C.
    destruct A_and__B_or_C as [yesA B_or_C].
    destruct B_or_C.
        (*Proof for B being given*)
        left.
        split.
        exact yesA.
        exact H.
        (*Proof for C being given*)
        right.
        split.
        exact yesA.
        exact H.
Qed.