Require Import Classical_Prop.

(*Copied from exercise 1,2 from uebung07*)
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


Section drinker.

  Variable T : Set.             (* "Datentyp" fÃ¼r die Personen in der Kneipe. *)
  Variable x : T.               (* Sicherstellung, dass Ã¼berhaupt jemand in der Kneipe ist. *)
  Variable drinks : T -> Prop.  (* PrÃ¤dikat, dass jemand in der Kneipe trinkt. *)

  Theorem Paradox: exists x, drinks x -> forall y, drinks y.
  Proof.
    apply FU with (x := exists z, ~ drinks z).
    split.
      intro ExistsNonDrinker.
      destruct ExistsNonDrinker as [z ZDoesntDrink].
      exists z.
      intro ZDoesDrink.
      contradiction.
      
      intro DoesntExistNonDrinker.
      exists x.
      assert (forall y, ~~drinks y) as EverybodyDoesntNotDrink.
        intro y.
        intro YDoesntDrink.
        unfold not at 1 in DoesntExistNonDrinker.
        apply DoesntExistNonDrinker.
        exists y.
        apply YDoesntDrink.
      intro xDrinks.
      intro y.
      apply NNPP.
      apply EverybodyDoesntNotDrink.
  Qed.
  

End drinker.

Section zoll.

  Variable T : Set.

  Variable E : T -> Prop.       (* reist ein *)
  Variable I : T -> Prop.       (* genieÃŸt ImmunitÃ¤t *)
  Variable S : T -> T -> Prop.  (* S x y meint "x durchsucht y" *)
  Variable Z : T -> Prop.       (* Ist Zollbeamter/-in *)
  Variable D : T -> Prop.       (* Betreibt Drogenschmuggel *)

  Theorem Drogenschmuggel: ((forall x, ~I x -> exists y, Z y /\ S y x) /\ (exists x, E x /\ D x /\ (forall y, S y x -> D y)) /\ (forall x, I x -> ~ D x) -> (exists x, Z x /\ D x)).
  Proof.
    intro Conjunction.
    destruct Conjunction as [Phi1 [Phi2 Phi3]].
    destruct Phi2 as [x [xEntered [xSmuggles onlySmugglersSearchedX]]].
    assert (~ I x) as xNotImmune.
      intro xImmune.
      assert (~ D x) as xDoesntSmuggle.
        apply Phi3.
        exact xImmune.
      contradiction.
    assert (exists y, Z y /\ S y x) as [y [yZoll ySearchedx]].
      apply Phi1.
      exact xNotImmune.
    assert (D y) as ySmuggles.
      apply onlySmugglersSearchedX.
      exact ySearchedx.
    exists y.
    split.
    exact yZoll.
    exact ySmuggles.
  Qed.

End zoll.

Section eq.

  Variable f : Set -> Set -> Set.
  Variables x y : Set.

  Hypothesis A1 : forall x y, f y (f x y) = x.

  Theorem T2 : f (f x y) x = y.
  Proof.
    (*TODO: Hier Beweis ergÃ¤nzen.*)
  Admitted. (*TODO: Nach erfolgreichem Beweis diese Zeile durch "Qed."  ersetzen. *)

End eq.