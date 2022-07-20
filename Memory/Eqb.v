Require Import Bool Arith.
  
  Module Type EQB.
    Parameter t : Type.
    Parameter eqb: t -> t -> bool.
    Axiom eqb_eq: forall x y, eqb x y = true <-> x = y.
  End EQB.

  Module Full(Eqb: EQB).
    
    Include Eqb.
    
    Lemma eqb_refl:
      forall κ, eqb κ κ = true.
    Proof.
      intros κ. now apply eqb_eq.
    Qed.
    
    Lemma eqb_neq:
      forall κ κ', eqb κ κ' = false <-> κ <> κ'.
    Proof.
      intros κ κ'; split; intro H.
      - intro H'; subst; rewrite eqb_refl in H; discriminate.
      - apply Bool.not_true_iff_false.
        contradict H.
        now apply eqb_eq.
    Qed.
    
    
    Lemma eqb_sym:
      forall κ κ', eqb κ κ' = eqb κ' κ.
    Proof.
      intros κ κ'.
      case_eq(eqb κ κ'); intro H.
      - apply eqb_eq in H; subst.
        now rewrite eqb_refl.
      - apply eqb_neq in H.
        symmetry.
        apply Bool.not_true_iff_false.
        contradict H.
        now apply eqb_eq in H.
    Qed.
    
  End Full.
  
