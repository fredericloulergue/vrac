From Coq Require Import Logic.FinFun.
From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax MiniC.Semantics.

Import FunctionalEnv Domain Facts.


Section GenericFacts.
    Context {S T : Set} {fe : @fenv S T}.
    Context {ext_used_stmt_vars : S -> StringSet.t} {ext_ty_val: 𝕍 -> @c_type T}.

    Variable (stmt_sem : forall f e, @generic_stmt_sem_sig S T f e).

    Notation generic_exp_sem := (fun e => @generic_exp_sem T e).
    Notation generic_stmt_sem := (fun f e => @generic_stmt_sem _ _ stmt_sem ext_used_stmt_vars ext_ty_val f e).


    Fact untouched_var_same_eval_exp : 
        @_untouched_var_same_eval_exp T generic_exp_sem.
    Proof with eauto with rac_hint.
        clear stmt_sem fe.
        intros ev e v x Hnotin Hderiv.  induction Hderiv ; simpl in Hnotin...
        - split ; constructor...  intros. simpl. apply p_map_not_same_eq... StringSet.D.fsetdec.
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

    Fact untouched_var_same_eval_stmt : 
        @_untouched_var_same_eval_stmt _ _ stmt_sem ext_used_stmt_vars fe ->
        @_untouched_var_same_eval_stmt _ _ generic_stmt_sem ext_used_stmt_vars fe.
    Proof with auto with rac_hint.
        intros Hext ev ev' s x Hderiv [Hnotin Huservar]. induction Hderiv ; simpl in Hnotin; trivial.
        - simpl. autounfold with rac_hint. rewrite p_map_not_same... StringSet.D.fsetdec.
        -  apply IHHderiv. StringSet.D.fsetdec.
        - apply IHHderiv. StringSet.D.fsetdec. 
        - apply IHHderiv.  simpl. StringSet.D.fsetdec.
        - destruct IHHderiv1.
            + StringSet.D.fsetdec.
            + apply IHHderiv2. StringSet.D.fsetdec. 
        - simpl. symmetry. apply p_map_not_same_eq... StringSet.D.fsetdec.
        (* return *)
        - simpl. destruct (eq_dec res_f x).
            + subst. discriminate.
            + autounfold with rac_hint. symmetry...
        - eapply Hext in H...
    Qed.

    Fact determinist_exp_eval : 
        _determinist_exp_eval generic_exp_sem.
    Proof.
        intros e. induction e ; intros ; inversion H ; inversion H0 ; subst ; try easy.
        4,5:
            apply IHe1 with (v:=VInt (z ⁱⁿᵗ z_ir)) (v':=VInt (z0 ⁱⁿᵗ z_ir0)) in H11 ; [|assumption] ; injection H11 as eqz ;
            apply IHe2 with (v:=VInt (z' ⁱⁿᵗ z'_ir)) (v':= VInt (z'0 ⁱⁿᵗ z'_ir0)) in H13; [|assumption] ;  injection H13 as eqz' ; subst ; now rewrite H14 in H7.
        - f_equal. f_equal. now apply MI.mi_eq. 
        - congruence.
        - f_equal. f_equal. apply MI.mi_eq. simpl. f_equal.
            + apply IHe1 with (v:=VInt (z ⁱⁿᵗ z_ir)) (v':= VInt (z0 ⁱⁿᵗ z_ir0)) in H13; [|assumption]. now injection H13. 
            + apply IHe2 with (v:=VInt (z' ⁱⁿᵗ z'_ir)) (v':=VInt (z'0 ⁱⁿᵗ z'_ir0)) in H14; [|assumption]. now injection H14.
    Qed.


    (* Definition determinist_c_exp_eval := @determinist_exp_eval Empty_exp_sem _determinist_c_exp_eval. *)

    Fact Forall2_same_zargs : 
        forall ev eargs zargs zargs0, 
        List.Forall2 (generic_exp_sem ev) eargs zargs 
        -> List.Forall2 (generic_exp_sem ev) eargs zargs0 
        -> zargs = zargs0.
    Proof.
        intros ev eargs zargs zargs0 Hderiv. generalize dependent zargs0. induction Hderiv ; intros zargs0 H1.
        - now inversion H1.
        - destruct zargs0; [inversion H1|].
            apply List.Forall2_cons_iff in H1 as [H1 Hderiv2].
            apply determinist_exp_eval in H1.  apply H1 in H. subst. f_equal. clear H1.
            now apply IHHderiv in Hderiv2.
    Qed.

    Fact determinist_stmt_eval : 
        _determinist_stmt_eval generic_exp_sem stmt_sem (fe:=fe) -> 
        _determinist_stmt_eval generic_exp_sem generic_stmt_sem (fe:=fe).
    Proof with auto.
        intros  Hds Hde s ev ev' Hderiv. induction Hderiv using @generic_stmt_sem_full_ind; intros.

        - inversion H...    
        - inversion_clear H2... repeat f_equal.  apply determinist_exp_eval in H5... specialize (H5 z). apply H5 in H1. now inversion H1. 
        - inversion_clear H0...  apply determinist_exp_eval in H1... destruct H as [H []]. apply H1 in H. now inversion H.
        - inversion_clear H0... exfalso.  apply determinist_exp_eval in H... destruct H1 as [H1 Hnotz]. apply H in H1. inversion H1. now apply Hnotz.
        - inversion H... 
        - inversion_clear H... apply IHHderiv1 in H0. subst. apply IHHderiv2 in H1. now subst. 
        - inversion_clear H4. destruct H5 as (params0 & Hl & Hf & Hargs & Hsem).
            (* same args, same body *) 
            assert (Heq: params = params0 /\ b = b0) by (rewrite Hf in H0; now inversion_clear H0). inversion_clear Heq. subst.
            (* same args eval *) 
            assert (zargs = zargs0). {
                pose proof (Forall2_same_zargs _ _ _ _  H1 Hargs) as Hsame.
                apply list_map_id_eq in Hsame; [assumption|]. unfold Injective. intros x y Heq. now inversion Heq. 
            }
            subst. apply IHHderiv in Hsem. subst. rewrite H7 in H3. injection H3 as H3. now subst.

                
        - inversion_clear H2. destruct H3 as (params0 & Hl & Hf & Hargs & Hsem). 
            assert (Heq: params = params0 /\ b = b0) by (rewrite Hf in H0; now inversion_clear H0). inversion_clear Heq. subst.
            assert (zargs = zargs0). {
                pose proof (@Forall2_same_zargs  _ _ _ _ H1 Hargs) as Hsame. 
                apply list_map_id_eq in Hsame ; [assumption|]. unfold Injective. intros x y Heq. now inversion Heq. 
            }
            subst. apply IHHderiv in Hsem. now subst.
        - inversion H0 ; subst... apply determinist_exp_eval in H... apply H in H2. injection H2 as H2. now subst.
        - inversion H1...

        - inversion H0. subst. enough (ev_s0 = ev_s).
            + subst. apply IHHderiv in H5. now subst.
            + admit.
        - inversion H0. subst. unfold _determinist_stmt_eval in Hds. eapply Hds...
            + apply H.
            + apply H2. 
    Admitted.

End GenericFacts.


Fact _determinist_c_exp_eval {T : Set} : @_determinist_exp_eval T Empty_exp_sem.
Proof. easy. Qed.

Fact _determinist_c_stmt_eval {S T : Set} {ext_used_stmt_vars} : 
    @_determinist_stmt_eval S T Empty_exp_sem Empty_stmt_sem ext_used_stmt_vars.
Proof. easy. Qed.


(* Definition determinist_c_stmt_eval {S T } fe := @determinist_stmt_eval S T Empty_ext_used_stmt_vars fe Empty_stmt_sem  _determinist_c_stmt_eval. *)