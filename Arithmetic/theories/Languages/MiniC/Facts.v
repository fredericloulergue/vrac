From Coq Require Import FinFun.
From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax MiniC.Semantics.

Import FunctionalEnv Domain Facts.

Fact untouched_var_same_eval_exp {T : Set} : forall exp_sem, 
    _untouched_var_same_eval_exp exp_sem ->
    _untouched_var_same_eval_exp (@generic_exp_sem T exp_sem).
Proof with eauto with rac_hint.
    intros exp_sem Hext ev e v x Hnotin Hderiv. induction Hderiv ; simpl in Hnotin...
    - split... constructor. simpl. apply p_map_not_same_eq... StringSet.D.fsetdec.
    - split ; 
        intro x';  econstructor...
        + apply IHHderiv1. StringSet.D.fsetdec. 
        + apply IHHderiv2. StringSet.D.fsetdec.
        + apply IHHderiv1... StringSet.D.fsetdec. 
        + apply IHHderiv2... StringSet.D.fsetdec. 
    - split;
        intro x';  econstructor...
        + apply IHHderiv1... StringSet.D.fsetdec. 
        + apply IHHderiv2... StringSet.D.fsetdec. 
        + apply IHHderiv1... StringSet.D.fsetdec. 
        + apply IHHderiv2... StringSet.D.fsetdec. 
    - split ; 
        intro x';  econstructor...
        + apply IHHderiv1... StringSet.D.fsetdec. 
        + apply IHHderiv2... StringSet.D.fsetdec.  
        + apply IHHderiv1... StringSet.D.fsetdec. 
        + apply IHHderiv2... StringSet.D.fsetdec.  
Qed.

Fact untouched_var_same_eval_stmt {S T : Set} : 
    forall exp_sem stmt_sem ext_stmt_vars, 
    _untouched_var_same_eval_stmt exp_sem stmt_sem ext_stmt_vars ->
    _untouched_var_same_eval_stmt exp_sem (@generic_stmt_sem S T exp_sem stmt_sem ext_stmt_vars) ext_stmt_vars.
Proof with auto with rac_hint.
    intros exp_sem stmt_sem ext_stmt_vars Hext f ev ev' s x Hderiv [Hnotin Huservar]. induction Hderiv ; simpl in Hnotin; trivial.
    - simpl. autounfold with rac_hint. rewrite p_map_not_same... StringSet.D.fsetdec.
    -  apply IHHderiv. StringSet.D.fsetdec.
    - apply IHHderiv. StringSet.D.fsetdec. 
    - apply IHHderiv.  simpl. StringSet.D.fsetdec.
    - destruct IHHderiv.
        + StringSet.D.fsetdec.
        + apply IHHderiv0. StringSet.D.fsetdec. 
    - simpl. symmetry. apply p_map_not_same_eq... StringSet.D.fsetdec.
    (* return *)
    - simpl. destruct (eq_dec res_f x). subst. 
        * discriminate.
        * autounfold with rac_hint. symmetry...
    - eapply Hext in H...
Qed.

Fact determinist_exp_eval {T : Set}: 
forall ext_exp_sem, _determinist_exp_eval ext_exp_sem -> _determinist_exp_eval (@generic_exp_sem T ext_exp_sem).
Proof.
    intros ext_exp_sem ext_inj. unfold _determinist_exp_eval. intros e. induction e ; intros ; inversion H ; inversion H0 ; subst ; try easy.
    4,5:
        apply IHe1 with (v:=VInt (z ⁱⁿᵗ z_ir)) (v':=VInt (z0 ⁱⁿᵗ z_ir0)) in H11 ; [|assumption] ; injection H11 as eqz ;
        apply IHe2 with (v:=VInt (z' ⁱⁿᵗ z'_ir)) (v':= VInt (z'0 ⁱⁿᵗ z'_ir0)) in H13; [|assumption] ;  injection H13 as eqz' ; subst ; now rewrite H14 in H7.
    - f_equal. f_equal. now apply Int.mi_eq. 
    - congruence.
    - f_equal. f_equal. apply Int.mi_eq. simpl. f_equal.
        + apply IHe1 with (v:=VInt (z ⁱⁿᵗ z_ir)) (v':= VInt (z0 ⁱⁿᵗ z_ir0)) in H13; [|assumption]. now injection H13. 
        + apply IHe2 with (v:=VInt (z' ⁱⁿᵗ z'_ir)) (v':=VInt (z'0 ⁱⁿᵗ z'_ir0)) in H14; [|assumption]. now injection H14.
Qed.


Fact _determinist_c_exp_eval {T} : _determinist_exp_eval (@Empty_exp_sem T).
Proof. easy. Qed.

Definition determinist_c_exp_eval {T}:= determinist_exp_eval (@Empty_exp_sem T) _determinist_c_exp_eval.

Fact Forall2_same_zargs { T : Set} : forall ev eargs zargs zargs0  exp_sem, 
    _determinist_exp_eval exp_sem
    -> List.Forall2 (@generic_exp_sem T exp_sem ev) eargs zargs 
    -> List.Forall2 (@generic_exp_sem T exp_sem ev) eargs zargs0 -> zargs = zargs0.
Proof.
    intros ev eargs zargs zargs0 exp H  Hderiv. generalize dependent zargs0. induction Hderiv ; intros zargs0 H1.
    - now inversion H1.
    - destruct zargs0. inversion H1. apply List.Forall2_cons_iff in H1 as [H1 Hderiv2].
        apply determinist_exp_eval in H0 ; [|assumption]. apply H0 in H1. subst. f_equal. clear H0.
        now apply IHHderiv in Hderiv2.
Qed.

Fact determinist_stmt_eval {S T : Set}: 
    forall ext_exp_sem ext_stmt_sem ext_stmt_vars, 
    @_determinist_stmt_eval S T ext_exp_sem ext_stmt_sem -> 
    _determinist_stmt_eval ext_exp_sem (@generic_stmt_sem S T ext_exp_sem ext_stmt_sem ext_stmt_vars).
Proof with auto. 
    intros ext_exp_sem ext_stmt_sem ext_stmt_vars Hds Hde f s ev ev' Hderiv. induction Hderiv ; intros.
    - inversion H... 
    - inversion H2 ; subst... repeat f_equal.  apply determinist_exp_eval in H8... specialize (H8 z). apply H8 in H1. now inversion H1.
    - inversion H1 ; subst...  apply determinist_exp_eval in H6... destruct H as [H []]. apply H6 in H. now inversion H.
    - inversion H1 ; subst... apply determinist_exp_eval in H... destruct H6 as [H2 []]. apply H in H2. now inversion H2.
    - inversion H0... 
    - inversion H1 ; subst... apply IHHderiv in H4. subst. apply IHHderiv0 in H6. now subst. 
    - inversion H5 ; subst. 
       (* same args, same body *) 
            rewrite H10 in H0. injection H0 as H0. subst.
            (* same args eval *) 
            assert (zargs = zargs0). {
                pose proof (@Forall2_same_zargs T ev eargs vargs vargs0 ext_exp_sem Hde H1 H11) as H0. unfold vargs,vargs0 in H0.
                apply list_map_id_eq in H0. assumption. unfold Injective. intros x y H7. now inversion H7. 
            }
            subst. apply IHHderiv in H12. subst. rewrite H4 in H15. injection H15 as H15. now subst.
    - inversion H3.  subst.  rewrite H7 in H0. injection H0 as Eq1. subst. 
             assert (zargs = zargs0). {
                pose proof (@Forall2_same_zargs T ev eargs vargs vargs0 ext_exp_sem Hde H1 H8) as H0. unfold vargs,vargs0 in H0.
                apply list_map_id_eq in H0. assumption. unfold Injective. intros x y Heq. now inversion Heq. 
             }
             subst.
            apply IHHderiv in H10. now subst.
    - inversion H0 ; subst... apply determinist_exp_eval in H... apply H in H2. injection H2 as H2. now subst.
    - inversion H1...
    - inversion H0. subst. unfold _determinist_stmt_eval in Hds. eapply Hds... apply H. apply H2.
Qed.

Fact _determinist_c_stmt_eval {S T} : @_determinist_stmt_eval S T Empty_exp_sem Empty_stmt_sem. easy. Qed.
Definition determinist_c_stmt_eval {S T} := determinist_stmt_eval Empty_exp_sem Empty_stmt_sem Empty_ext_stmt_vars (@_determinist_c_stmt_eval S T).

