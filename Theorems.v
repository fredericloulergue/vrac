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



Lemma weakening_of_expression_semantics : 
forall env e x,
    env ⊨ e => x <-> (forall env', env ⊑ env' ->  env' ⊨ e => x)
.
Proof.
    assert (
        eq_env_partial_order : forall e e' v z, e ⊑ e' ->  z <> UInt /\ z <> UMpz -> (fst e) v = Some z -> (fst e') v = Some z
    ). 
    {
        intros. destruct H with v ; try assumption ; try rewrite H2 in H1 ; try injection H1 as Eq ; subst ; try assumption.
        - destruct H0 as [uint _]. destruct uint. reflexivity.
        - destruct H0 as [_ umpz]. destruct umpz. reflexivity.
        - discriminate.
    }

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
    - intro. apply H. constructor.
Qed.