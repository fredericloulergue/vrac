From Coq Require Import Strings.String Logic.FinFun. 
From RecordUpdate Require Import RecordUpdate.
From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax MiniC.Semantics.

Import FunctionalEnv Domain.

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
    forall exp_sem stmt_sem ext_stmt_vars, 
    _untouched_var_same_eval_stmt exp_sem stmt_sem ext_stmt_vars ->
    _untouched_var_same_eval_stmt exp_sem (@generic_stmt_sem S T exp_sem stmt_sem ext_stmt_vars) ext_stmt_vars.
Proof.
    intros exp_sem stmt_sem ext_stmt_vars Hext f ev ev' s x Hderiv [Hnotin Huservar]. induction Hderiv ; simpl in Hnotin; trivial.
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


Lemma weakening_of_expression_semantics {T} : 
    forall exp_sem, 
    (_weakening_of_expression_semantics exp_sem exist_env_mem_partial_order)
    ->
    _weakening_of_expression_semantics (@generic_exp_sem T exp_sem) exist_env_mem_partial_order
.
Proof with (eauto using refl_env_mem_partial_order with rac_hint).
    split...  intro Hderiv. induction Hderiv; intros...
        constructor. eapply eq_int_env_mem_partial_order...
Qed.


Definition weakening_of_c_expression_semantics {T} := weakening_of_expression_semantics (@Empty_exp_sem T) weakening_of_empty_expression_semantics. 



Lemma weakening_of_statement_semantics_1 {S T : Set} : 
    forall exp_sem stmt_sem ext_stmt_vars, 
    _weakening_of_statement_semantics_1 exp_sem stmt_sem env_mem_partial_order
    -> _weakening_of_statement_semantics_1 exp_sem (@generic_stmt_sem S T exp_sem stmt_sem ext_stmt_vars) env_mem_partial_order
.
Proof with eauto using refl_env_mem_partial_order, env_partial_order_add with rac_hint.
    intros exp_sem stmt_sem ext_stmt_vars Hext_stmt Hext_exp f ev₀ s ev₁. 
    pose proof (weakening_of_expression_semantics exp_sem Hext_exp) as exp_weak.
    intro Hderiv. induction Hderiv ; intros ev₀' sub Henvmem.
        (* skip *)
        * exists ev₀'. split...
        
        (* assign *) 
        * exists (ev₀' <| env ; vars ::= {{x \induced (proj1_sig sub) z}} |>). split. 
            + simpl. pose proof (env_partial_order_add ev ev₀' sub) as H3. simpl in *. now  destruct H3 with x z.
            + apply S_Assign...
                ** apply env_same_ty with ev...
                    *** right. now exists sub.
                     *** congruence.
                ** rewrite (exp_weak e) in H1. specialize (H1 ev₀'). destruct H1... now exists sub.

        (* if true *)
        * destruct H. destruct (IHHderiv ev₀' sub) as [ev_s [Henvmem2 Hderiv2]]...
            exists ev_s. split...
            apply S_IfTrue with z... split... 
            rewrite  (exp_weak e) in H. apply H. now exists sub.

        (* if false *)
        * destruct (IHHderiv ev₀' sub) as [ev_s [Henvmem2 Hderiv2]]... exists ev_s. split...
            apply S_IfFalse...
            rewrite  (exp_weak e) in H. apply H. now exists sub. 


         (* while *)
        * destruct (IHHderiv ev₀' sub) as [ev_s [Henvmem2 Hderiv2]]...


        (* c seq *)
        * destruct (IHHderiv ev₀' sub) as [I1ev [I1Hrel I1Hderiv]]... 
            destruct (IHHderiv0 I1ev sub) as [I2ev [I2Hrel I2Hderiv]]... 

        (* f call *)
         * destruct (IHHderiv (empty_env <| env; vars ::= p_map_addall_back xargs vargs |>) sub) as [b_ev' [H5 Hsem]]; subst vargs.
            +  apply same_int_any_sub. 
                ++ apply List.Forall2_length in H1. pose proof (List.map_length  (fun x : Int.MI => Def (VInt x)) zargs) as H5.
                    rewrite H5 in H1. congruence. 
                ++ apply empty_env_mem_refl_any_sub. 
            + eexists (ev₀' <| env; vars ::= {{c \Def z}} |> <| mstate := b_ev' |>). split.
                ++ apply env_mem_partial_order_add_mem... now pose proof (env_partial_order_add ev ev₀' _ Henvmem c z).
                ++  apply S_FCall with b xargs zargs...
                    +++ epose proof (List.Forall2_impl (R1:=generic_exp_sem ev) (generic_exp_sem ev₀')) as Hforall.
                            apply Hforall... intros. apply exp_weak with ev... now exists sub.
                    +++ apply eq_int_env_mem_partial_order with b_ev... now exists sub. 
   
        (* p call *)
         * destruct (IHHderiv (empty_env <| env; vars ::= p_map_addall_back xargs vargs |>) sub) as [b_ev' [H5 Hsem]]; subst vargs.
            +  apply same_int_any_sub. 
                ++ apply List.Forall2_length in H1. pose proof (List.map_length  (fun x : Int.MI => Def (VInt x)) zargs) as H5.
                    rewrite H5 in H1. congruence. 
                ++ apply empty_env_mem_refl_any_sub. 
            + exists (ev₀' <| mstate := b_ev' |>). split.
                ++ apply env_mem_partial_order_add_mem...
                ++  apply S_PCall with b xargs zargs...
                    +++ epose proof (List.Forall2_impl (R1:=generic_exp_sem ev) (generic_exp_sem ev₀')) as Hforall.
                            apply Hforall... intros. apply exp_weak with ev... now exists sub.

        (* return *)
        * exists (ev₀' <| env ; vars ::= {{res_f \Def z}} |>). split.
            + now pose proof (env_partial_order_add ev ev₀' sub Henvmem).
            + apply S_Return... apply (exp_weak e ev z)... now exists sub.

        (* assert *)
        * exists ev₀'. split... apply S_PAssert with z...
            apply (exp_weak e ev z)... now exists sub.

        (* other cases *)
        * specialize (Hext_stmt Hext_exp f ev (S_Ext s) ev').
            eapply Hext_stmt in H... destruct H as [ev'' [Hrel2 Hderiv]]...                  
Qed.

Definition weakening_of_c_statements_semantics_1 {S T} := 
    weakening_of_statement_semantics_1 (@Empty_exp_sem T) (@Empty_stmt_sem S T) Empty_ext_stmt_vars (weakening_of_empty_statement_semantics_1 env_mem_partial_order).  

Lemma weakening_of_statement_semantics_2 {S T : Set} : 
    forall exp_sem stmt_sem ext_stmt_vars, 
    _weakening_of_statement_semantics_2 exp_sem stmt_sem env_mem_partial_order
    -> _weakening_of_statement_semantics_2 exp_sem (@generic_stmt_sem S T exp_sem stmt_sem ext_stmt_vars) env_mem_partial_order
.
Proof with auto with rac_hint.
    intros  exp_sem stmt_sem ext_stmt_vars Hext_stmt Hdeter Hext_exp  f ev₀ ev₀' s ev₁ sub [Hderiv1 Hrel]. 
    pose proof (weakening_of_expression_semantics exp_sem Hext_exp) as exp_weak.
    unfold _weakening_of_statement_semantics_2 in Hext_stmt. 
    unfold _weakening_of_expression_semantics in Hext_exp.    
    generalize dependent ev₀'.
    induction Hderiv1 ; intros ev₀' Hrel ev₁' Hderiv2 ; inversion Hderiv2 ; subst ; try easy...

    (* assign *)
    - split... simpl. intros v [Hnotin Hnotcompvar].  assert (HH: type_of_value (ev x) <> None) by congruence. apply type_of_value_env in HH.
        apply not_in_diff with (x:=v)  in HH... autounfold with rac_hint. eapply p_map_not_same_eq...  intro neq...

    (* if false *)
    - apply IHHderiv1... destruct H. specialize (exp_weak e ev z). rewrite exp_weak in H. specialize (H ev₀'). 
            apply determinist_exp_eval in H...
                + apply H in H5. inversion H5. now subst.
                + now exists sub.

    (* if true *)
    -  destruct H5. specialize (exp_weak e ev (VInt zero)). rewrite exp_weak in H. specialize (H ev₀').
            apply determinist_exp_eval in H...
            + apply H in H1. inversion H1. now subst.
            + now exists sub.

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
    - eapply Hext_stmt with (ev₀:=ev) (ev₁:=ev')  in H1...
Admitted.


Definition weakening_of_c_statements_semantics_2 {S T} := 
    weakening_of_statement_semantics_2 (@Empty_exp_sem T) (@Empty_stmt_sem S T) Empty_ext_stmt_vars 
    (weakening_of_empty_statement_semantics_2 env_mem_partial_order). 


Fact weakening_of_expression_semantics_3 {T : Set} : forall exp_sem, 
    _weakening_of_expression_semantics_3 exp_sem exist_strong_env_mem_partial_order
    -> _weakening_of_expression_semantics_3 (@generic_exp_sem T exp_sem) exist_strong_env_mem_partial_order
.
Proof with auto.
    intros exp Hextweak ev e v Hderiv.
    induction Hderiv; intros ev' [sub [Henv Hmem]] [HnotinEnv HnotinMem].
    - constructor.
    - assert (HxnotinEnv: ~ (dom ev - dom ev') x). {
        intros contra.  apply (HnotinEnv x contra); now left.
        }  
        apply not_in_sub_domain_prop in HxnotinEnv;[|apply in_domain_dec| apply in_domain_dec].
        constructor. destruct HxnotinEnv.
        * destruct H0 as [z' Hevx]. specialize (Henv x _ _ Hevx). rewrite H in Henv. inversion Henv. 
            destruct z' eqn:Z'Eqn.
            + destruct v eqn:VEqn.
                ++ simpl in H1. inversion H1. now subst.
                ++ destruct l; now subst.
            + simpl in H1. now subst.
        * exfalso. apply H0. now exists z. 
    - admit.
    - admit.
    - admit.
Admitted.

Definition weakening_of_c_expression_semantics_3 {T} := 
    weakening_of_expression_semantics_3 (@Empty_exp_sem T) (weakening_of_empty_expression_semantics_3 exist_strong_env_mem_partial_order). 


Lemma weakening_of_statement_semantics_3 {S T : Set} : 
    forall exp_sem stmt_sem ext_stmt_vars, 
    _weakening_of_expression_semantics_3 exp_sem exist_strong_env_mem_partial_order
    -> _weakening_of_statement_semantics_3 stmt_sem ext_stmt_vars  exist_strong_env_mem_partial_order
    -> _weakening_of_statement_semantics_3 (@generic_stmt_sem S T exp_sem stmt_sem ext_stmt_vars) ext_stmt_vars exist_strong_env_mem_partial_order
.

Proof with auto with rac_hint.
    intros exp_sem stmt_sem ext_stmt_vars ext_exp_weak ext_stmt_weak.
    epose proof (weakening_of_expression_semantics_3 exp_sem ext_exp_weak) as exp_weak.
    intros f ev₀ s ev₁ Hderiv ev₀' Hrel [Henv Hmem].

    induction Hderiv. 
    (* skip *)
    - exists ev₀'. constructor.

    (* assign *)
    -  exists (ev₀' <| env ; vars ::= {{x\Def z}} |>). apply S_Assign...
        +  apply env_same_ty with ev... left. pose proof strong_env_mem_stronger. destruct Hrel as [x0 Hrel]. exists x0. now apply H2. easy.
        + apply weakening_of_expression_semantics_3 with ev... split. 
            * intros v Hdom. apply Henv in Hdom. simpl in Hdom.  
                apply Decidable.not_or in Hdom. now destruct Hdom.
            * intros l Hdom. apply Hmem in Hdom as [l' Hdom]. simpl in Hdom.  exists l'. destruct Hdom. split... 

    (* if true *)
    -  admit.
    (* if false *)
    - admit.
    (* while *)
    - admit.

    (* seq *)
    - admit. 

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
        eapply weakening_of_expression_semantics_3 in H...
        
    (* assert *)
    - exists ev₀'. apply S_PAssert with z... 
        eapply weakening_of_expression_semantics_3 in H...
        

    (* other cases *)
    - unfold _weakening_of_statement_semantics_3 in ext_stmt_weak.
        specialize (ext_stmt_weak f  ev (S_Ext s) _ H ev₀' Hrel).
        destruct ext_stmt_weak as [ev'' Hd]... exists ev''...
Admitted.

Definition weakening_of_c_statements_semantics_3 {S T}  := 
    weakening_of_statement_semantics_3 
    (@Empty_exp_sem T) (@Empty_stmt_sem S T) Empty_ext_stmt_vars 
    (weakening_of_empty_expression_semantics_3 exist_strong_env_mem_partial_order) 
    (weakening_of_empty_statement_semantics_3 Empty_ext_stmt_vars exist_strong_env_mem_partial_order). 
