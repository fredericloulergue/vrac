Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import RAC.Semantics.
Require Import ZArith.ZArith.
Require Import String.
From Coq Require Import Lists.List.
Open Scope string_scope.
Open Scope fsl_scope.
Open Scope Z_scope.
Open Scope list_scope.



Theorem absence_of_dangling_pointers :
    forall n (z:=VMpz n) (mem_state:M) (var_env:Ωᵥ), 
        mem_state n <> ⊥ <-> 
        exists x, var_env x = Some z /\
        ~(exists x', x <> x' -> var_env x <> Some z)
.
Admitted.


Lemma iff_env_partial_order :
    forall env env' v, env_partial_orderb env env' v = true <-> env_partial_order env env' v.
Proof.
    intros. destruct env eqn:Senv. destruct env' eqn:Senv'. split.
    - intro H. unfold env_partial_orderb in H. simpl in H. destruct (ω v) eqn:Ev.
        * destruct v0 eqn:Ev0 ; destruct (ω1 v) eqn:Ev' ; subst ; try discriminate ; destruct v1 eqn:Ev1 ; subst ;simpl in H ; try discriminate.
            ** apply Int.mi_eq_iff in H.  apply sameInt with n ; simpl.
                *** assumption.
                *** rewrite H. assumption. 
            ** simpl in H. subst ; try discriminate. apply Nat.eqb_eq in H. subst. 
                apply sameMpz with n0 ; simpl ; assumption.
            ** apply undefInt with n ; simpl.
                *** assumption.
                *** right. assumption.
            ** apply undefInt with (Int.of_z 0 zeroinRange) ; simpl.
                *** assumption.
                *** left. assumption.
            ** apply undefMpz with n ; simpl.
                *** assumption.
                *** right. assumption.
            ** apply undefMpz with 0%nat ; simpl.
                *** assumption.
                *** left. assumption.
        * apply none. assumption.
    - intro H. inversion H ; unfold env_partial_orderb ; rewrite H0 ; simpl in *.
     * rewrite H1. apply Int.mi_eq_iff. reflexivity.
     * rewrite H1. apply Nat.eqb_refl.
     * destruct H1 ; rewrite H1 ; reflexivity. 
     * destruct H1 ; rewrite H1 ; reflexivity. 
     * reflexivity.
Qed.

Corollary refl_env_partial_order : forall e, e ⊑ e.
Proof.
    intros . apply iff_env_partial_order. unfold env_partial_orderb. 
    destruct e.
    simpl. destruct (ω v). destruct v0 ; try reflexivity.
    unfold same_values. apply Int.mi_eq_iff.
    * reflexivity.
    * unfold same_values. apply Nat.eqb_refl.
    * reflexivity.
Qed.

Lemma eq_env_partial_order : 
    forall e e' v z, e ⊑ e' ->  z <> UInt /\ z <> UMpz -> (fst e) v = Some z -> (fst e') v = Some z.
Proof.
    intros. destruct H with v ; rewrite H2 in H1 ; try injection H1 as Eq ; subst ; try assumption.
    - destruct H0 as [uint _]. destruct uint. reflexivity.
    - destruct H0 as [_ umpz]. destruct umpz. reflexivity.
    - discriminate.
Qed.   


Lemma weakening_of_expression_semantics : 
forall env e x,
    env ⊨ e => x <-> (forall env', env ⊑ env' ->  env' ⊨ e => x)
.
Proof.
    split.
    - generalize dependent x. induction e.
        * intros v H env' Inc. inversion H. subst. apply E_Int.
        * intros v H env' Inc. inversion H. subst. apply E_Var.
            apply eq_env_partial_order with (v:=var) (z:=z) in Inc.
            ** assumption.
            ** split ; intro contra ; inversion contra.
            ** assumption.
        * intros v H env' Inc. inversion H ;  subst. 
            apply E_BinOpInt with z_ir z'_ir.
             + apply IHe1 ; assumption.
             + apply IHe2 ; assumption.
        * intros. inversion H ; subst.
            + apply E_BinOpTrue with z z' z_ir z'_ir.
                ++ apply IHe1 ; assumption.
                ++ apply IHe2 ; assumption.
                ++ assumption.
            + apply E_BinOpFalse with z z' z_ir z'_ir.
                ++ apply IHe1 ; assumption.
                ++ apply IHe2 ; assumption.
                ++ assumption.
    - intro. apply H. apply refl_env_partial_order.
Qed.