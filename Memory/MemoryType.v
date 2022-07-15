Require Import Arith ZArith Vrac.Tactics.

Inductive mtyp := i8 | i16 | i32 | i64.

Definition mtyp_eqb κ κ' :=
  match (κ, κ') with
  | (i8, i8) => true
  | (i16, i16) => true
  | (i32, i32) => true
  | (i64, i64) => true
  | _ => false
  end.

Lemma eq_iff_mtyp_eqb_true :
  forall κ κ', κ = κ' <-> mtyp_eqb κ κ' = true.
Proof.
  intros κ κ'; split; intro H;
    destruct κ; destruct κ'; subst; now compute.
Qed.

Lemma mtyp_eqb_refl :
  forall κ, mtyp_eqb κ κ = true.
Proof.
  intros; now apply eq_iff_mtyp_eqb_true.
Qed.

Lemma mtyp_eqb_sym :
  forall κ κ', mtyp_eqb κ κ' = mtyp_eqb κ' κ.
Proof.
  intros; destruct κ; destruct κ'; trivial.
Qed.

Lemma mtyp_eqb_neq:
  forall κ κ', mtyp_eqb κ κ' = false <-> κ <> κ'.
Proof.
  intros κ κ'; split; intro H.
  - contradict H; apply eq_iff_mtyp_eqb_true in H; rewrite H; now intro H'.
  - apply Bool.not_true_is_false. contradict H.
    now apply eq_iff_mtyp_eqb_true.
Qed.

Definition sizeof: mtyp -> Z :=
  fun type => match type with
           | i8 => 1%Z
           | i16 => 2%Z
           | i32 => 4%Z
           | i64 => 8%Z
           end.

Lemma sizeof_pos:
  forall κ, (0 <= sizeof κ)%Z.
Proof.
  now destruct κ.
Qed.

Ltac simpl_mtyp :=
  try simpl_eqb;
  match goal with 
  | [ |- context [mtyp_eqb ?x ?x ] ] =>
      rewrite mtyp_eqb_refl; simpl
  | [ H: context [ mtyp_eqb ?x ?x ] |- _ ] =>
      rewrite mtyp_eqb_refl in H; simpl in H
  | [ H: mtyp_eqb ?x ?y = true |- _ ] =>
      apply eq_iff_mtyp_eqb_true in H; subst
  | [ Hn: ?x <> ?y |- context [mtyp_eqb ?x ?y ] ] =>
      apply mtyp_eqb_neq in Hn; rewrite Hn; simpl
  | [ Hn: ?x <> ?y, H: context [ mtyp_eqb ?x ?y ] |- _ ] =>
      apply mtyp_eqb_neq in Hn; rewrite Hn in H; simpl in H
  | [ Hn: ?y <> ?x |- context [mtyp_eqb ?x ?y ] ] =>
      apply mtyp_eqb_neq in Hn; rewrite mtyp_eqb_sym in Hn; rewrite Hn;
      apply mtyp_eqb_neq in Hn; simpl
  | [ Hn: ?y <> ?x, H: context [ mtyp_eqb ?x ?y ] |- _ ] =>
      apply mtyp_eqb_neq in Hn; rewrite mtyp_eqb_sym in Hn; rewrite Hn in H;
      apply mtyp_eqb_neq in Hn; simpl in H
  end.

