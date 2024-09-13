From Coq Require Import Strings.String Logic.FinFun. 
From RecordUpdate Require Import RecordUpdate.
From RAC Require Import Utils Environnement.Facts.
From RAC.Languages Require Import Syntax MiniC.Semantics MiniC.Facts.

Import FunctionalEnv Domain.

#[local] Open Scope utils_scope.


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
