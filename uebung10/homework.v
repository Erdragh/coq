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

  (* TODO: Formalisierung und Beweis des Paradoxons. *)
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

  (*TODO: Hier Formalisierung und Beweis einfÃ¼gen. *)

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