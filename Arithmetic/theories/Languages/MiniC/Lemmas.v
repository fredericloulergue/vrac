From Coq Require Import Strings.String Logic.FinFun. 

From RAC Require Import Utils Environment.Facts.
From RAC.Languages Require Import Syntax MiniC.Semantics MiniC.Facts.

Import FunctionalEnv Domain.

#[local] Open Scope utils_scope.


Section GenericLemmas.
    Context {S T : Set} {fe : @fenv S T}.
    
    Context {ext_used_stmt_vars : S -> StringSet.t} {ext_ty_val: 𝕍 -> @c_type T}.
    
    Variable (exp_sem : forall e, @generic_exp_sem_sig T e).
    Variable (stmt_sem : forall f e, @generic_stmt_sem_sig S T f e).

    Variable (_determinist_stmt_eval :  _determinist_stmt_eval generic_exp_sem stmt_sem (fe := fe)).

    Notation generic_exp_sem := (fun e => @generic_exp_sem T e).
    Notation generic_stmt_sem := (fun f e => @generic_stmt_sem _ _ stmt_sem ext_used_stmt_vars ext_ty_val f e).



    Lemma LC1_weakening_of_expression_semantics : 
        _LC1_weakening_of_expression_semantics exp_sem exist_env_mem_partial_order ->
        _LC1_weakening_of_expression_semantics generic_exp_sem exist_env_mem_partial_order
    .
    Proof with (eauto using refl_env_mem_partial_order with rac_hint).
        split...  intro Hderiv. induction Hderiv; intros...
            constructor. eapply eq_int_env_mem_partial_order...
    Qed.


    Lemma LC21_weakening_of_statement_semantics : 
        _LC1_weakening_of_expression_semantics exp_sem exist_env_mem_partial_order ->
        _LC21_weakening_of_statement_semantics exp_sem stmt_sem exist_env_mem_partial_order env_mem_partial_order (fe:=fe) ->
        _LC21_weakening_of_statement_semantics  generic_exp_sem generic_stmt_sem exist_env_mem_partial_order env_mem_partial_order (fe:=fe)
    .
    Proof with eauto using refl_env_mem_partial_order, env_partial_order_add with rac_hint.
        intros  Hext_exp Hext_stmt exp_weak ev₀ s ev₁. red in exp_weak.

        intro Hderiv.  induction Hderiv using @generic_stmt_sem_full_ind ; intros ev₀' sub Henvmem.

        (* skip *)
        - exists ev₀'. split...
        
        (* assign *) 
        - exists (ev₀' <| env ; vars ::= {{x \induced (proj1_sig sub) z}} |>). split. 
            + simpl. pose proof (env_partial_order_add ev ev₀' sub) as H3. simpl in *. now  destruct H3 with x z.
            + apply S_Assign...
                -- apply env_same_ty with ev...
                    ++ right. now exists sub.
                    ++ congruence.
                -- rewrite exp_weak in H1. specialize (H1 ev₀'). destruct H1... now exists sub.

        (* if true *)
        - destruct H as [H1 H2]. destruct (IHHderiv ev₀' sub) as [ev_s [Henvmem2 Hderiv2]]...
            exists ev_s. split...
            apply S_IfTrue with z... split... 
            rewrite  exp_weak in H1. apply H1. now exists sub.

        (* if false *)
        - destruct (IHHderiv ev₀' sub) as [ev_s [Henvmem2 Hderiv2]]... exists ev_s. split...
            apply S_IfFalse...
            rewrite exp_weak in H. apply H. now exists sub. 


        (* while *)
        - destruct (IHHderiv ev₀' sub) as [ev_s [Henvmem2 Hderiv2]]...


        (* c seq *)
        - destruct (IHHderiv1 ev₀' sub) as [I1ev [I1Hrel I1Hderiv]]... 
            destruct (IHHderiv2 I1ev sub) as [I2ev [I2Hrel I2Hderiv]]... 

        (* f call *)
        
        - destruct (IHHderiv (empty_env <| env; vars ::= p_map_addall_back params vals |>) sub) as [b_ev' [Henvmem2 Hsem2]]; subst vals.
            +  apply same_int_any_sub. 
                * apply List.Forall2_length in H1. pose proof (List.length_map  (fun x : MI.t => Def (VInt x)) zargs) as Hlength.
                    rewrite Hlength in H1. congruence. 
                * apply empty_env_mem_refl_any_sub. 
            + eexists (ev₀' <| env; vars ::= {{c \Def z}} |> <| mstate := b_ev' |>). split.
                * apply env_mem_partial_order_add_mem... now pose proof (env_partial_order_add ev_args ev₀' _ Henvmem c z).
                *  apply S_FCall with b zargs...
                    -- epose proof (List.Forall2_impl (R1:=generic_exp_sem ev_args) (generic_exp_sem ev₀')) as Hforall. red.
                        exists params. repeat split...
                            apply Hforall... intros. apply exp_weak with ev_args... now exists sub.
                    -- apply eq_int_env_mem_partial_order with b_ev... now exists sub. 
        
        (* p call *)
        - destruct (IHHderiv (empty_env <| env; vars ::= p_map_addall_back params vals |>) sub) as [b_ev' [H5 Hsem2]]; subst vals.
            +  apply same_int_any_sub. 
                * apply List.Forall2_length in H1. pose proof (List.length_map  (fun x : MI.t => Def (VInt x)) zargs) as H5.
                    rewrite H5 in H1. congruence. 
                * apply empty_env_mem_refl_any_sub. 
            + exists (ev₀' <| mstate := b_ev' |>). split.
                * apply env_mem_partial_order_add_mem...
                *  apply S_PCall with b zargs...
                    epose proof (List.Forall2_impl (R1:=generic_exp_sem ev_args) (generic_exp_sem ev₀')) as Hforall. red. exists params. repeat split...
                    apply Hforall... intros. apply exp_weak with ev_args... now exists sub.
    
        (* return *)
        - exists (ev₀' <| env ; vars ::= {{res_f \Def z}} |>). split.
            + now pose proof (env_partial_order_add ev ev₀' sub Henvmem).
            + apply S_Return... apply (exp_weak e ev z)... now exists sub.

        (* assert *)
        - exists ev₀'. split... apply S_PAssert with z...
            apply (exp_weak e ev z)... now exists sub.

        (* scope *)
        - edestruct IHHderiv as [ev₁' [Henvmem' Hsem']].
            + admit.
            + exists (ev₀' <| mstate := ev₁'|>). split.
                * apply env_mem_partial_order_add_mem...
                * clear IHHderiv. inversion H; subst.
                    -- apply S_Scope with ev₀'... constructor.
                    -- eapply S_Scope; admit. (* need induction on H *)

        (* other cases *)
        - red in Hext_stmt. specialize (Hext_stmt Hext_exp ev (S_Ext s) ev').
            eapply Hext_stmt in H... destruct H as [ev'' [Hrel2 Hderiv2]]...                  
    Admitted.


    Lemma LC21_weakening_of_statement_semantics_strong : 
        _LC1_weakening_of_expression_semantics exp_sem exist_env_mem_partial_order ->
        _LC21_weakening_of_statement_semantics exp_sem stmt_sem exist_strong_env_mem_partial_order strong_env_mem_partial_order (fe:=fe) ->
        _LC21_weakening_of_statement_semantics  generic_exp_sem generic_stmt_sem exist_env_mem_partial_order env_mem_partial_order (fe:=fe).
    Admitted.



    Lemma LC22_weakening_of_statement_semantics : 
        _LC1_weakening_of_expression_semantics exp_sem exist_env_mem_partial_order ->
        _LC22_weakening_of_statement_semantics exp_sem stmt_sem exist_env_mem_partial_order env_mem_partial_order (fe:=fe) -> 
        _LC22_weakening_of_statement_semantics generic_exp_sem generic_stmt_sem exist_env_mem_partial_order env_mem_partial_order (fe:=fe)
    .
    Proof with auto with rac_hint.
        intros Hext_exp Hext_stmt exp_weak  ev₀ ev₀' s ev₁ sub [Hderiv1 Hrel]. 
        generalize dependent ev₀'. generalize dependent sub.
        induction Hderiv1 using @generic_stmt_sem_full_ind; intros sub ev₀' Hrel ev₁' Hderiv2 ; inversion Hderiv2 ; subst ; try easy...

        (* assign *)
        - split... simpl. intros v [Hnotin Hnotcompvar].  assert (HH: type_of_value (ev x) <> None) by congruence. apply type_of_value_env in HH.
            apply not_in_diff with (x:=v)  in HH...
            autounfold with rac_hint. eapply p_map_not_same_eq...  intro neq...

        (* if false && if true  *)
        - exfalso. destruct H as [H Hnotzero]. red in exp_weak. specialize (exp_weak e ev z). 
            apply exp_weak with ev₀' in H.
            + apply determinist_exp_eval in H4. apply H4 in H. inversion H. now apply Hnotzero.  
            + now exists sub.

        (* if true && if false  *)
        - exfalso. destruct H4 as [H8 Hnotzero]. red in exp_weak. specialize (exp_weak e ev zero). 
            eapply exp_weak in H.
            + apply determinist_exp_eval in H8. apply H8 in H. inversion H. now apply Hnotzero.  
            + now exists sub.
        
        (* seq *) 
        - admit.  
        
        (* fcall *)
        - destruct H7 as (params0 & Hl & Hf & Hforall & Hsem). rewrite Hf in H0. admit.
        
        (* pcall *)
        - destruct H5 as (params0 & Hl & Hf & Hforall & Hsem).  rewrite Hf in H0. injection H0 as H0. subst. 
            edestruct IHHderiv1...
            + admit.
            + admit.
            + epose proof (List.Forall2_impl (R1:=generic_exp_sem ev_args) (generic_exp_sem ev_args)) as Hforall2. admit.


        (* return *)
        -  split ; intros v... intros [Hnotin Hnotcomp]. destruct (string_dec res_f v).
            + subst. discriminate. (* v is the function return value*)
            +  symmetry. apply p_map_not_same...
                
        (* Scope *)
        - admit.

        (* ext *)
        - eapply Hext_stmt.
            +  apply Hext_exp.
            + split... apply H.
            + apply H1.
    Admitted.



    Fact LC1_weakening_of_expression_semantics_3  : 
        _LC1_weakening_of_expression_semantics_3 exp_sem strong_env_mem_partial_order ->
        _LC1_weakening_of_expression_semantics_3 generic_exp_sem strong_env_mem_partial_order
    .
    Proof with eauto with rac_hint.
        intros Hextweak ev e v sub Hderiv.
        induction Hderiv; intros ev' Henvmem [HnotinEnv HnotinMem].
        - constructor.
        - assert (HxnotinEnv: ~ (dom ev - dom ev')%dom_ x). {
            intros contra.  apply (HnotinEnv x contra); now left.
            }  
            apply not_in_sub_domain_prop in HxnotinEnv;[|apply in_domain_dec| apply in_domain_dec].
            constructor. destruct HxnotinEnv.
            * destruct H0 as [z' Hevx]. destruct Henvmem as [Henv _]. specialize (Henv x _ _ Hevx). rewrite H in Henv. inversion Henv. 
                destruct z' eqn:Z'Eqn.
                + destruct v eqn:VEqn.
                    ++ simpl in H1. inversion H1. now subst.
                    ++ destruct l; now subst.
                + simpl in H1. now subst.
            * exfalso. apply H0. now exists z. 
        
        - apply C_E_BinOpInt with z_ir z'_ir.
            + apply IHHderiv1...
                * split.
                    -- intros v Hdom. apply HnotinEnv in Hdom. simpl in Hdom |- *. StringSet.D.fsetdec. 
                    -- intros.  apply HnotinMem in H0. destruct H0 as [x0 [Hevx0 HnotInx0]].
                        exists x0. split... simpl in HnotInx0. StringSet.D.fsetdec.
            + apply IHHderiv2...
                * split.
                    -- intros v Hdom. apply HnotinEnv in Hdom. simpl in Hdom |- *. 
                        StringSet.D.fsetdec.
                    -- intros.  apply HnotinMem in H0. destruct H0 as [x0 [Hevx0 HnotInx0]].
                        exists x0. split... simpl in HnotInx0. StringSet.D.fsetdec.

        - eapply C_E_BinOpTrue...
            + apply IHHderiv1...
                * split.
                    -- intros v Hdom. apply HnotinEnv in Hdom. simpl in Hdom |- *. StringSet.D.fsetdec.
                    -- intros.  apply HnotinMem in H0. destruct H0 as [x0 [Hevx0 HnotInx0]].
                        exists x0. split... simpl in HnotInx0. StringSet.D.fsetdec.
            + apply IHHderiv2...
                * split.
                    -- intros v Hdom. apply HnotinEnv in Hdom. simpl in Hdom |- *. StringSet.D.fsetdec.
                    -- intros. apply HnotinMem in H0. destruct H0 as [x0 [Hevx0 HnotInx0]].
                        exists x0. split... simpl in HnotInx0. StringSet.D.fsetdec.

        - eapply C_E_BinOpFalse...
            + apply IHHderiv1...
                * split.
                    -- intros v Hdom. apply HnotinEnv in Hdom. simpl in Hdom |- *. StringSet.D.fsetdec.
                    -- intros.  apply HnotinMem in H0. destruct H0 as [x0 [Hevx0 HnotInx0]].
                        exists x0. split... simpl in HnotInx0. StringSet.D.fsetdec.
            + apply IHHderiv2...
                * split.
                    -- intros v Hdom. apply HnotinEnv in Hdom. simpl in Hdom |- *. StringSet.D.fsetdec.
                    -- intros.  apply HnotinMem in H0. destruct H0 as [x0 [Hevx0 HnotInx0]].
                        exists x0. split... simpl in HnotInx0. StringSet.D.fsetdec.
    Qed.



    Lemma LC23_weakening_of_statement_semantics : 
        _LC1_weakening_of_expression_semantics_3 exp_sem strong_env_mem_partial_order -> 
        _LC23_weakening_of_statement_semantics stmt_sem strong_env_mem_partial_order (ext_used_stmt_vars:=ext_used_stmt_vars) (fe:=fe) -> 
        _LC23_weakening_of_statement_semantics generic_stmt_sem strong_env_mem_partial_order  (ext_used_stmt_vars:=ext_used_stmt_vars) (fe:=fe)
    .
    Proof with eauto with rac_hint; try easy.
        intros ext_exp_weak ext_stmt_weak.
        epose proof (LC1_weakening_of_expression_semantics_3 ext_exp_weak) as exp_weak.
        epose proof (determinist_stmt_eval _ _determinist_stmt_eval) as stmt_deter.
        intros ev₀ s ev₁ sub Hderiv.
        induction Hderiv using @generic_stmt_sem_full_ind; intros ev₀' Hrel [Henv Hmem]. 
        
        (* skip *)
        - exists ev₀'. constructor.

        (* assign *)
        - exists (ev₀' <| env ; vars ::= {{x\Def z}} |>). apply S_Assign...
            + apply env_same_ty with ev... left. pose proof strong_env_mem_stronger. exists sub. now apply strong_env_mem_stronger. 
            + eapply LC1_weakening_of_expression_semantics_3... split. 
                * intros v Hdom. apply Henv in Hdom. simpl in Hdom |- *. StringSet.D.fsetdec.
                * intros l Hdom. apply Hmem in Hdom as [l' Hdom]. simpl in Hdom |- *. exists l'. destruct Hdom.  split...
                    StringSet.D.fsetdec. 

        (* if true *)
        - edestruct IHHderiv... 
            + split. 
                * intros v Hdom. specialize (Henv v Hdom). simpl in Henv. StringSet.D.fsetdec.
                * intros l Hdom. apply Hmem in Hdom as [l' Hdom]. simpl in Hdom |- *. exists l'. destruct Hdom.  split...
                    StringSet.D.fsetdec. 
            + exists x. apply S_IfTrue with z...
                split... eapply LC1_weakening_of_expression_semantics_3... split.
                * intros v Hdom. apply Henv in Hdom. simpl in Hdom |- *. StringSet.D.fsetdec.
                * intros l Hdom. apply Hmem in Hdom as [l' Hdom]. simpl in Hdom |- *. exists l'. destruct Hdom.  split...
                    StringSet.D.fsetdec. 


        (* if false *)
        - edestruct IHHderiv... 
            + split. 
                * intros v Hdom. apply Henv in Hdom. simpl in Hdom |- *. StringSet.D.fsetdec.
                * intros l Hdom. apply Hmem in Hdom as [l' Hdom]. simpl in Hdom |- *. exists l'. destruct Hdom.  split...
                    StringSet.D.fsetdec. 
            + exists x. apply S_IfFalse...
                eapply LC1_weakening_of_expression_semantics_3... split.
                * intros v Hdom. apply Henv in Hdom. simpl in Hdom |- *. StringSet.D.fsetdec.
                * intros l Hdom. apply Hmem in Hdom as [l' Hdom]. simpl in Hdom |- *. exists l'. destruct Hdom.  split...
                    StringSet.D.fsetdec. 

        (* while *)
        - edestruct IHHderiv... split.
            + intros v Hdom. apply Henv in Hdom. simpl in Hdom |- *. StringSet.D.fsetdec.
            + intros l Hdom. apply Hmem in Hdom as [l' Hdom]. simpl in Hdom |- *. exists l'. destruct Hdom.  split...
                StringSet.D.fsetdec. 
            

        (* seq *)
        - admit. 

        (* fcall *)
        - destruct IHHderiv with ((empty_env <| env; vars ::= p_map_addall_back params vals |>))...
            + admit. (* need refl env *)
            + split.
                * intros. exfalso.  apply (d_sub_d_empty (empty_env <| env; vars ::= p_map_addall_back params vals |>)).
                    now exists v.
                * intros. exfalso.  apply (d_sub_d_empty (empty_env <| env; vars ::= p_map_addall_back params vals |>).(mstate)). 
                    now exists x.
            + clear IHHderiv. exists (ev₀' <| env ; vars ::= {{c\Def z}} |> <| mstate := x |>). econstructor...
                * exists params. repeat split... 
                    eapply (List.Forall2_impl (R1:=generic_exp_sem ev_args) (generic_exp_sem ev₀'))...
                    intros. eapply LC1_weakening_of_expression_semantics_3... split.
                    -- intros v Hdom. apply Henv in Hdom. simpl in Hdom |- *. StringSet.D.fsetdec || admit.
                    -- intros l Hdom. apply Hmem in Hdom as [l' Hdom]. simpl in Hdom |- *. exists l'. destruct Hdom.  split...
                        StringSet.D.fsetdec || admit.


                * apply stmt_deter in Hderiv...
                    -- apply Hderiv in H4. now subst. 
                    -- apply determinist_exp_eval.
        (* pcall *)
        - destruct IHHderiv with ((empty_env <| env; vars ::= p_map_addall_back params vals |>))...
            + admit. (* need refl env *)
            + split.
                * intros. exfalso.  apply (d_sub_d_empty (empty_env <| env; vars ::= p_map_addall_back params vals |>)).
                    now exists v.
                * intros. exfalso.  apply (d_sub_d_empty (empty_env <| env; vars ::= p_map_addall_back params vals |>).(mstate)). 
                    now exists x.
            + clear IHHderiv. exists (ev₀' <| mstate := x |>). econstructor...  exists params. repeat split...
                eapply (List.Forall2_impl (R1:=generic_exp_sem ev_args) (generic_exp_sem ev₀'))...
                intros. eapply LC1_weakening_of_expression_semantics_3... split.
                * intros v Hdom. apply Henv in Hdom. simpl in Hdom |- *. StringSet.D.fsetdec || admit.
                * intros l Hdom. apply Hmem in Hdom as [l' Hdom]. simpl in Hdom |- *. exists l'. destruct Hdom.  split...
                    StringSet.D.fsetdec || admit.

        (* return *)
        - exists (ev₀' <| env ; vars ::= {{res_f\Def z}} |>). apply S_Return.
            eapply LC1_weakening_of_expression_semantics_3 in H...
            
        (* assert *)
        - exists ev₀'. apply S_PAssert with z...         

        (* other cases *)
        - unfold _LC23_weakening_of_statement_semantics in ext_stmt_weak.
            edestruct ext_stmt_weak...
    Admitted.
End GenericLemmas.



Definition weakening_of_c_expression_semantics {T} := 
    LC1_weakening_of_expression_semantics 
        (@Empty_exp_sem T) 
        weakening_of_empty_expression_semantics. 


Definition weakening_of_c_expression_semantics_3 {T} := 
    @LC1_weakening_of_expression_semantics_3  T
        (@Empty_exp_sem T) 
        (weakening_of_empty_expression_semantics_3 strong_env_mem_partial_order). 


Definition weakening_of_c_statements_semantics_1 {S T} f ext_ty := 
    @LC21_weakening_of_statement_semantics S T f Empty_ext_used ext_ty (@Empty_exp_sem T) (@Empty_stmt_sem S T) 
    weakening_of_empty_expression_semantics
    (weakening_of_empty_statement_semantics_1 exist_env_mem_partial_order env_mem_partial_order f (@Empty_exp_sem T)).  


Definition weakening_of_c_statements_semantics_2 {S T} f ext_ty := 
    @LC22_weakening_of_statement_semantics S T f Empty_ext_used ext_ty (@Empty_exp_sem T) (@Empty_stmt_sem S T) 
    weakening_of_empty_expression_semantics
    (weakening_of_empty_statement_semantics_2 exist_env_mem_partial_order env_mem_partial_order f (@Empty_exp_sem T)). 



Definition weakening_of_c_statements_semantics_3 {S T} f ext_ty := 
    @LC23_weakening_of_statement_semantics S T f Empty_ext_used ext_ty (@Empty_exp_sem T) (@Empty_stmt_sem S T) 
    (weakening_of_empty_expression_semantics_3 strong_env_mem_partial_order) 
    (weakening_of_empty_statement_semantics_3 strong_env_mem_partial_order Empty_ext_used f). 