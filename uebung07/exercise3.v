Require Import Classical_Prop.

Parameters isElephant forgets wonMastermind hasTrunk didMastermind: Prop.

Theorem Exercise3: ((
    (isElephant -> ~forgets) /\ 
    (wonMastermind -> ~hasTrunk) /\
    ((~forgets /\ didMastermind) -> wonMastermind) /\
    (~hasTrunk -> ~isElephant) /\
    (isElephant /\ didMastermind)) -> False).
Proof.
    intro Conjunction.
    destruct Conjunction as [A1 A2].
    destruct A2 as [A2 A3].
    destruct A3 as [A3 A4].
    destruct A4 as [A4 A5].
    destruct A5 as [Elephant Participated].
    assert (~forgets) as DoesntForget.
        apply A1.
        exact Elephant.
    assert (~forgets /\ didMastermind) as ShouldWinMastermind.
        split.
        exact DoesntForget.
        exact Participated.
    assert (wonMastermind) as IsWinner.
        apply A3.
        exact ShouldWinMastermind.
    assert (~hasTrunk) as DoesntHaveTrunk.
        apply A2.
        exact IsWinner.
    assert (~isElephant) as NotElephant.
        apply A4.
        exact DoesntHaveTrunk.
    contradiction.
Qed.