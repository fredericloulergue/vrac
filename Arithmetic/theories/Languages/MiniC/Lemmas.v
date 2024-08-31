From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax MiniC.Semantics.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import Strings.String.

Fact untouched_var_same_eval_exp {T : Set} : forall exp_sem, 
    _untouched_var_same_eval_exp exp_sem ->
    _untouched_var_same_eval_exp (@generic_exp_sem T exp_sem).
Proof with eauto with rac_hint.
    intros exp_sem Hext ev e v x Hnotin Hderiv. induction Hderiv ; simpl in Hnotin...
    - split... constructor. simpl. apply p_map_not_same_eq...
    - rewrite List.in_app_iff in Hnotin ; apply Decidable.not_or_iff in Hnotin as [Hxnotine Hxnotine'].  split ; 
        intro x';  econstructor...
        + apply IHHderiv1...
        + apply IHHderiv2...
        + apply IHHderiv1...
        + apply IHHderiv2...
    - rewrite List.in_app_iff in Hnotin ; apply Decidable.not_or_iff in Hnotin as [Hxnotine Hxnotine'].  split ; 
        intro x';  econstructor...
        + apply IHHderiv1...
        + apply IHHderiv2...
        + apply IHHderiv1...
        + apply IHHderiv2...
    - rewrite List.in_app_iff in Hnotin ; apply Decidable.not_or_iff in Hnotin as [Hxnotine Hxnotine'].  split ; 
        intro x';  econstructor...
        + apply IHHderiv1...
        + apply IHHderiv2...
        + apply IHHderiv1...
        + apply IHHderiv2... 
Qed.

Fact untouched_var_same_eval_stmt {S T : Set} : 
    forall exp_sem stmt_sem, 
    _untouched_var_same_eval_stmt exp_sem stmt_sem ->
    _untouched_var_same_eval_stmt exp_sem (@generic_stmt_sem S T exp_sem stmt_sem).
Proof.
    intros exp_sem stmt_sem Hext f ev ev' s x Hderiv [Hnotin Huservar]. induction Hderiv ; simpl in Hnotin; trivial.
    - subst. apply Decidable.not_or_iff in Hnotin as [Hdiffxresf]. simpl. autounfold with rac_hint. rewrite p_map_not_same.
        * easy.
        * congruence.
    -  apply IHHderiv. 
        intro Hcontra. apply Hnotin. apply List.in_app_iff. right. 
        apply List.in_app_iff. now left.
    - apply IHHderiv. intro Hcontra. apply Hnotin. apply List.in_app_iff. right. 
        apply List.in_app_iff. now right.
    - apply IHHderiv. simpl. intro contra. rewrite List.app_nil_r in contra. apply Hnotin. apply List.in_app_iff in contra as [Hine | Hinses].
        * apply List.in_app_iff. now left.
        * apply List.in_app_iff in Hinses as [Hins | Hins].
            + apply List.in_app_iff. now right.
            + assumption.
    - destruct IHHderiv.
        + intro Hcontra. apply Hnotin. apply  List.in_app_iff. now left.
        + apply IHHderiv0. intro Hcontra. apply Hnotin. apply List.in_app_iff. now right.
    - simpl. symmetry. apply p_map_not_same_eq ; auto.
    (* return *)
    - simpl. destruct (eq_dec res_f x). subst. 
        * discriminate.
        * autounfold with rac_hint. symmetry. rewrite p_map_not_same_eq. auto. congruence.  
    - eapply Hext in H ; eauto.
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
    forall ext_exp_sem ext_stmt_sem, 
    @_determinist_stmt_eval S T ext_exp_sem ext_stmt_sem -> 
    _determinist_stmt_eval ext_exp_sem (@generic_stmt_sem S T ext_exp_sem ext_stmt_sem).
Proof with auto. 
    intros ext_exp_sem ext_stmt_sem Hds Hde f s ev ev' Hderiv. induction Hderiv ; intros.
    - inversion H... 
    - inversion H3 ; subst... repeat f_equal.  apply determinist_exp_eval in H2... apply H2 in H10. now subst.
    - inversion H1 ; subst...  apply determinist_exp_eval in H6... destruct H. apply H6 in H. now symmetry in H.
    - inversion H1 ; subst... apply determinist_exp_eval in H... destruct H6. apply H in H2. now symmetry in H2. 
    - inversion H0... 
    - inversion H1 ; subst... apply IHHderiv in H4. subst. apply IHHderiv0 in H6. now subst. 
    - inversion H5 ; subst. 
       (* same args, same body *) 
            rewrite H10 in H0. injection H0 as H0. subst.
            (* same args eval *) 
            assert (zargs = zargs0) by auto using (@Forall2_same_zargs T ev eargs zargs zargs0 ext_exp_sem). 
            subst. apply IHHderiv in H12. subst. rewrite H4 in H15. injection H15 as H15. now subst.
    - inversion H3.  subst.  rewrite H7 in H0. injection H0 as Eq1. subst. 
            assert (zargs = zargs0) by eauto using (@Forall2_same_zargs T _ eargs zargs zargs0 ext_exp_sem). subst. 
            apply IHHderiv in H10. now subst.
    - inversion H0 ; subst... apply determinist_exp_eval in H... apply H in H2. injection H2 as H2. now subst.
    - inversion H1...
    - inversion H0. subst. unfold _determinist_stmt_eval in Hds. eapply Hds... apply H. apply H2.
Qed.

Fact _determinist_c_stmt_eval {S T} : @_determinist_stmt_eval S T Empty_exp_sem Empty_stmt_sem. easy. Qed.
Definition determinist_c_stmt_eval {S T} := determinist_stmt_eval Empty_exp_sem Empty_stmt_sem (@_determinist_c_stmt_eval S T).

Lemma weakening_of_expression_semantics {T} : 
    forall exp_sem, 
    (_weakening_of_expression_semantics exp_sem )
    ->
    _weakening_of_expression_semantics (@generic_exp_sem T exp_sem)
.
Proof with (eauto using refl_env_mem_partial_order with rac_hint).
    split...  intro Hderiv. induction Hderiv; intros...
        constructor. eapply eq_env_partial_order... easy.
Qed.

Fact _weakening_of_c_expression_semantics {T} : _weakening_of_expression_semantics (@Empty_exp_sem T). 
Proof.
    unfold _weakening_of_expression_semantics. intros. split ; unfold Empty_exp_sem.
    - intros [].
    - intro H. apply H with ev... apply refl_env_mem_partial_order.
Qed.

Definition weakening_of_c_expression_semantics  {T} := 
weakening_of_expression_semantics (@Empty_exp_sem T) _weakening_of_c_expression_semantics.

Lemma weakening_of_statement_semantics_1 {S T : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_statement_semantics_1 exp_sem stmt_sem 
    -> _weakening_of_statement_semantics_1 exp_sem (@generic_stmt_sem S T exp_sem stmt_sem)
.
Proof with eauto using refl_env_mem_partial_order,env_partial_order_add with rac_hint.
    intros exp_sem stmt_sem Hext_stmt Hext_exp f ev₀ s ev₁. 
    pose proof (weakening_of_expression_semantics exp_sem Hext_exp) as exp_weak.
    intro Hderiv. induction Hderiv ; intros ev₀' [Henv Hmem].
        (* skip *)
        * exists ev₀'... 
        
        (* assign *) 
        * exists (ev₀' <| env ; vars ::= {{x \ z}} |>). split. 
            + split... simpl. apply env_partial_order_add... 
            + apply S_Assign...
                *** now apply env_same_ty with ev. 
                *** rewrite (exp_weak e) in H2. specialize (H2 ev₀'). apply H2...


        (* if true *)
        * destruct H. destruct (IHHderiv ev₀') as [ev_s [[Henv2 Hmem2] Hderiv2]]... exists ev_s. intros . split...
            apply S_IfTrue with z. split...
            rewrite  (exp_weak e) in H... apply Hderiv2...
        (* if false *)
        * destruct (IHHderiv ev₀') as [ev_s [[Henv2 Hmem2] Hderiv2]]... exists ev_s. split...
            apply S_IfFalse...
            rewrite  (exp_weak e) in H... 


         (* while *)
        * destruct (IHHderiv ev₀') as [ev_s [[Henv2 Hmem2] Hderiv2]]... 


        (* c seq *)
        * destruct IHHderiv with ev₀' as [I1ev [I1Hrel I1Hderiv]]...
            destruct IHHderiv0 with I1ev as [I2ev [I2Hrel I2Hderiv]]... 

        (* f call *)
         * edestruct IHHderiv as [e_s [Hrel Hderiv2]].
            + now split.
            + eexists (ev₀' <| env; vars ::= {{c \Def z}} |> <| mstate := ev' |>). split.
                ++ split... apply env_partial_order_add... easy. 
                ++ eapply S_FCall... 
                    +++ epose proof (List.Forall2_impl (R1:=generic_exp_sem ev) (generic_exp_sem ev₀')) as Hforall. destruct Hforall with eargs zargs...
                        intros...
                    apply exp_weak with ev...
        (* p call *)
        *  edestruct IHHderiv as [ev_s [Hrel Hderiv2]].
            + now split... 
            + eexists (_ <| mstate := _ |>)... simpl. split.
                ++ destruct Hrel. split...
                ++ eapply S_PCall ...
                    +++ epose proof (List.Forall2_impl (R1:=generic_exp_sem ev) (generic_exp_sem ev₀')) as Hforall. destruct Hforall with eargs zargs...
                        intros. apply exp_weak with ev...

        (* return *)
        * exists (ev₀' <| env ; vars ::= {{res_f \Def z}} |>). split.
            + split... apply env_partial_order_add...
            + apply S_Return... apply (exp_weak e ev z)...

        (* assert *)
        * exists ev₀'. split... apply S_PAssert with z...
            apply (exp_weak e ev z)...

        (* other cases *)
        * specialize (Hext_stmt Hext_exp f ev (S_Ext s) ev').
            apply Hext_stmt with ev₀' in H. destruct H as [ev'' [Hrel2 Hderiv]]... easy.                 
Qed.

Fact _weakening_of_c_statements_semantics_1 {S T} : _weakening_of_statement_semantics_1 (@Empty_exp_sem T) (@Empty_stmt_sem S T). 
Proof. easy. Qed.

Lemma weakening_of_statement_semantics_2 {S T : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_statement_semantics_2 exp_sem stmt_sem 
    -> _weakening_of_statement_semantics_2 exp_sem (@generic_stmt_sem S T exp_sem stmt_sem)
.
Proof with auto with rac_hint.
    intros exp_sem stmt_sem ext_stmt_weak f ev₀ ev₀' s ev₁ ext_exp_deter ext_exp_weak  [Hderiv1 Hrel].
    pose proof (weakening_of_expression_semantics exp_sem ext_exp_weak) as exp_weak.
    unfold _weakening_of_expression_semantics in exp_weak.
    unfold _weakening_of_statement_semantics_2 in ext_stmt_weak.
    
    induction Hderiv1 ; intros ev₁' Hderiv2 ; inversion Hderiv2 ; subst ; try easy...
    
    (* assign *)
    - split... simpl. intros v [Hnotin Hnotcompvar].  assert (HH: type_of_value (ev x) <> None) by congruence. apply type_of_value_env in HH.
        apply not_in_diff with (x:=v)  in HH... autounfold with rac_hint. eapply p_map_not_same_eq...  intro neq...

    (* if false *)
    - apply IHHderiv1... destruct H. specialize (exp_weak e ev z). rewrite exp_weak in H. specialize (H ev₀' Hrel). 
            apply determinist_exp_eval in H. apply H in H5. now subst. assumption.

    (* if true *)
    -  destruct H5. specialize (exp_weak e ev (VInt zero)). rewrite exp_weak in H. specialize (H ev₀' Hrel).
            apply determinist_exp_eval in H. apply H in H1. now subst. assumption.

    (* seq *)
    - admit.
    
    (* fcall *)
    - rewrite H9 in H0. inversion H0. subst. clear H0 H9 H8 H14. split ; admit.

    (* pcall *)
    - rewrite H6 in H0. injection H0 as H0. subst. edestruct IHHderiv1... admit. admit.
        epose proof (List.Forall2_impl (R1:=generic_exp_sem ev) (generic_exp_sem ev)) as Hforall. admit.

    (* return *)
    -  split ; intros v... intros [Hnotin Hnotcomp]. destruct (string_dec res_f v).
        + subst. discriminate. (* v is the function return value*)
        +  symmetry. apply p_map_not_same...
            
    (* assert *)
    - eapply ext_stmt_weak with (ev₀:=ev) (ev₁:=ev')  in H1...
Admitted.

Fact weakening_of_expression_semantics_3 {S T : Set} : forall exp_sem, 
    _weakening_of_expression_semantics exp_sem
    -> _weakening_of_expression_semantics_3 (@generic_exp_sem T exp_sem)
.
Proof with auto.
    intros exp Hweak ev e v ev1 Hderiv ev2 Hrel [Henv Hmem]. induction Hderiv.
    - constructor.
    - constructor. destruct Henv with x. simpl in H1. destruct H1. now left.
    - econstructor.
        + apply IHHderiv1.
            * intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                intros Hine. apply He2. apply List.in_app_iff...
            * intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                intro Hin. apply Hm2. apply List.in_app_iff... 
        + apply IHHderiv2.
            * intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                intros Hine. apply He2. apply List.in_app_iff. now right.
            * intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                intro Hin. apply Hm2. apply List.in_app_iff... 
    - apply C_E_BinOpTrue with z z' z_ir z'_ir...
        + apply IHHderiv1.
            * intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                intros Hine. apply He2. apply List.in_app_iff...
            * intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                intro Hin. apply Hm2. apply List.in_app_iff...
        + apply IHHderiv2.
            * intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                intros Hine. apply He2. apply List.in_app_iff...
            * intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                intro Hin. apply Hm2. apply List.in_app_iff...

    - apply C_E_BinOpFalse with z z' z_ir z'_ir...
        + apply IHHderiv1.
            * intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                intros Hine. apply He2. apply List.in_app_iff...
            * intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                intro Hin. apply Hm2. apply List.in_app_iff...
        + apply IHHderiv2.
            * intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                intros Hine. apply He2. apply List.in_app_iff...
            * intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                intro Hin. apply Hm2. apply List.in_app_iff...
Qed.


Lemma weakening_of_statement_semantics_3 {S T : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_expression_semantics exp_sem
    -> _weakening_of_statement_semantics_3 stmt_sem 
    -> _weakening_of_statement_semantics_3 (@generic_stmt_sem S T exp_sem stmt_sem)
.

Proof with auto with rac_hint.
    intros exp_sem stmt_sem ext_exp_weak ext_stmt_weak f ev₀ s ev₁ Hderiv ev₀' Hrel [Henv Hmem].
    induction Hderiv.
    (* skip *)
    - exists ev₀'. constructor.
    (* assign *)
    - destruct Henv with x. simpl in H4. destruct H4...  
    (* if true *)
    - destruct IHHderiv as [ev'' Hx]...
        + intro v. destruct Henv with v. split... intros Hin. apply H2.
            apply List.in_app_iff. right. apply List.in_app_iff...
        + intros l v Hdom. destruct Hmem with l v... split... intros Hin. apply H2.  
            apply List.in_app_iff. right. apply List.in_app_iff...
        + exists ev''. apply S_IfTrue with z... destruct H as [He Hzero]. split...
            eapply weakening_of_expression_semantics_3 in He... specialize He with ev₀'. apply He.
            * apply Hrel.
            * split ; simpl in Henv,Hmem.
                ** intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                    intros Hine. apply He2. apply List.in_app_iff...
                ** intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                    intro Hin. apply Hm2. apply List.in_app_iff...

    (* if false *)
    - destruct IHHderiv as [ev'' Hx]...
        + intro v. destruct Henv with v. split... intros Hin. apply H2.
            apply List.in_app_iff. right. apply List.in_app_iff...
        + intros l v Hdom. destruct Hmem with l v... split... intros Hin. apply H2.  
            apply List.in_app_iff. right. apply List.in_app_iff...
        + exists ev''. apply S_IfFalse... 
            eapply weakening_of_expression_semantics_3 in H... specialize H with ev₀'. apply H.
            * apply Hrel.
            * split ; simpl in Henv,Hmem.
                ** intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                    intros Hine. apply He2. apply List.in_app_iff...
                ** intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                    intro Hin. apply Hm2. apply List.in_app_iff...
    (* while *)
    - destruct IHHderiv as [ev'' Hx]...
        + intro v. destruct Henv with v. split... intros Hin. simpl in H1,Hin. apply H1. rewrite List.app_nil_r in Hin.
            apply List.in_app_iff in Hin. destruct Hin.
            * apply List.in_app_iff...
            * apply List.in_app_iff in H2. destruct H2... apply List.in_app_iff...
        + intros l v Hdom. destruct Hmem with l v... split... intros Hin. apply H1. simpl in Hin. rewrite List.app_nil_r in Hin.
            apply List.in_app_iff in Hin. destruct Hin.
            * apply List.in_app_iff...
            * apply List.in_app_iff in H2. destruct H2... apply List.in_app_iff...
        +  exists ev''. constructor... 

    (* seq *)
    - destruct IHHderiv as [ev0 Hx]...
        + intro v. destruct Henv with v. split... intros Hin. simpl in H2,Hin. apply H2. 
            apply List.in_app_iff...
        + intros l v Hdom. destruct Hmem with l v... split... intros Hin. apply H2. simpl in Hin.
            apply List.in_app_iff...
        + eexists.  apply S_Seq with ev0... admit. 

    (* fcall *)
    - eexists. apply S_FCall with b xargs zargs...
        * admit.
        * admit.
        * apply H4.

    (* pcall *)
    - repeat eexists. apply S_PCall with b xargs zargs...
        * admit.
        *  admit.

    (* return *)
    - exists (ev₀' <| env ; vars ::= {{res_f\Def z}} |>). apply S_Return.
        eapply weakening_of_expression_semantics_3 in H... specialize H with ev₀'. apply H... apply Hrel.
        
    (* assert *)
    - exists ev₀'. apply S_PAssert with z... 
        eapply weakening_of_expression_semantics_3 in H... specialize H with ev₀'. apply H... apply Hrel.
        

    (* other cases *)
    - unfold _weakening_of_statement_semantics_3 in ext_stmt_weak.
        specialize (ext_stmt_weak f  ev (S_Ext s) _ H ev₀' Hrel).
        destruct ext_stmt_weak as [ev'' Hd]... exists ev''...
Admitted.
