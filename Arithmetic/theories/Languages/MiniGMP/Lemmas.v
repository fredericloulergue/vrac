From Coq Require Import ZArith.ZArith.
From RecordUpdate Require Import RecordUpdate.
From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax Semantics MiniC.Lemmas. 


Import FunctionalEnv Domain.

#[local] Open Scope utils_scope.
#[local] Open Scope Z_scope. 

(* helper lemma for gmp cmp semantics *)
Fact cmp_induced : forall zx zy (b: 𝕍) sub,
    (zx > zy <-> b = one) /\ (zx < zy <-> b = sub_one) /\ (Z.eq zx zy <-> b = zero)
    -> 
    (zx > zy <-> induced sub b = one) /\
(zx < zy <-> induced sub b = sub_one) /\ (Z.eq zx zy <-> induced sub b = zero).
Proof.
    intros zx zy b sub (Hone & Hsubone &Hzero). split.
    - split.
        * intros Hzxzy. apply Hone in Hzxzy. now subst.
        * intros Hzxzy. apply induced_int_iff in Hzxzy. inversion Hzxzy. now apply Hone.
    - split.
       * split.
            + intros Hzxzy. apply Hsubone in Hzxzy. now subst.
            + intros Hzxzy. apply induced_int_iff in Hzxzy. inversion Hzxzy. now apply Hsubone.
        * split.
            + intros Hzxzy. apply Hzero in Hzxzy. now subst.
            + intros Hzxzy. apply induced_int_iff in Hzxzy. inversion Hzxzy. now apply Hzero.
Qed.



Lemma _weakening_of_gmp_statements_semantics_1 : 
    _weakening_of_statement_semantics_1 Empty_exp_sem _gmp_stmt_sem strong_env_mem_partial_order
.
Proof with eauto using refl_env_mem_partial_order with rac_hint ; try easy.
    intros _ f ev₀ s ev₁ Hderiv. 
    induction Hderiv; intros ev₀' sub Hstrenvmem; apply strong_env_mem_stronger in Hstrenvmem as Henvmem; 
        epose proof (fun y => weakening_of_c_expression_semantics y ev₀) as weak_exp;
        pose proof (eq_defined_mpz_mem_partial_order ev₀ ev₀' sub Henvmem) as eq_defined ;
        pose proof (eq_mpz_env_mem_partial_order ev₀ ev₀' sub Henvmem) as  eq_mpz ;
        pose proof (mem_def_partial_order_add) as mpz_add;
        pose proof (env_partial_order_add ev₀ ev₀' sub Henvmem) as env_add.
        (* init *)
        * clear weak_exp eq_defined eq_mpz env_add. exists (ev₀' <| env ; vars ::= {{x \ Def (VMpz (Some (proj1_sig sub l)))}} |> <| mstate ::= {{proj1_sig sub l \Defined 0}} |> ).
            split.
            + admit. (* now apply mpz_add. *)
            + clear mpz_add. apply S_init with u.
                ++ intros v. admit.
                ++ destruct Hstrenvmem as [e m]. now apply e in H0.
                    
        (* clear *)
        * exists (ev₀' <| env ; vars ::= {{x\Def (VMpz None)}} |><| mstate ::= {{(proj1_sig sub) a \ Undefined u}} |>). split.
            + admit. (* now apply mpz_add. *)
            + apply S_clear. now apply (eq_mpz x (Some a)).

        (* set_i *)
        * exists (ev₀' <| mstate ::= {{(proj1_sig sub) a \ Defined (z) ̇}} |>).  split... admit.
            apply S_set_i...
            ++ now apply (eq_mpz x (Some a)).
            ++ apply weak_exp... now exists sub.

        (* set_z *)
        * exists (ev₀' <| mstate ::= {{(proj1_sig sub) a \Defined z}} |>). split... admit.
            + apply S_set_z with (proj1_sig sub n)...
                ++ now apply (eq_mpz x (Some a)).
                ++ now apply (eq_mpz y (Some n)).

        (* get_int *)
        *  exists (ev₀' <| env ; vars ::= fun e =>  e{x \ Def (VInt (zy ⁱⁿᵗ ir))} |>). split... admit.
            apply S_get_int with (proj1_sig sub ly)... now apply (eq_mpz y (Some ly)).
        
        (* set_s *)
        * exists (ev₀' <| mstate ::= {{(proj1_sig sub) lx \ Defined zx}} |>). split... admit.
            constructor... now apply (eq_mpz x (Some lx)).

        (* cmp *)
        *  exists (ev₀' <| env ; vars ::= fun e => e{c \induced (proj1_sig sub) b} |>).  split ... admit.
            apply S_cmp with (proj1_sig sub lx) (proj1_sig sub ly) zx zy...
                ++ now apply (eq_mpz x (Some lx)).
                ++ now apply (eq_mpz y (Some ly)).
                ++ now apply cmp_induced.
        (* op *)
        * eexists (ev₀' <| mstate ::= {{(proj1_sig sub) lr \Defined (⋄ bop zx zy)}} |>). split. 
            + admit. (* now apply (mem_def_partial_order_add). *)
            + apply S_op with (proj1_sig sub lx) (proj1_sig sub ly)...
                ++ now apply (eq_mpz x (Some lx)).
                ++ now apply (eq_mpz y (Some ly)).
                ++ now apply (eq_mpz r (Some lr)).
        (* scope*)
        * eexists. split.
            + admit.
            + apply S_Scope with ev_s ev_s. inversion H.
                ++ rewrite <- H1. admit.
                ++ subst. constructor. admit.
Admitted.

(* Definition weakening_of_gmp_statements_semantics_1 := 
    weakening_of_statement_semantics_1 Empty_exp_sem _gmp_stmt_sem _gmp_stmt_vars _weakening_of_gmp_statements_semantics_1 . *)
 
Lemma _weakening_of_gmp_statements_semantics_2 : 
    _weakening_of_statement_semantics_2 Empty_exp_sem _gmp_stmt_sem env_mem_partial_order
.
Proof with eauto using refl_env_mem_partial_order with rac_hint ; try easy.
    intros  exp_sem stmt_sem f ev₀ ev₀' s ev₁ sub [Hderiv1 Hrel].
    generalize dependent ev₀'.
    induction Hderiv1;  intros ev Henvmem ev' Hderiv.
    - admit.     
    - admit.  
    - inversion Hderiv; subst; [|destruct bop; simpl in H1; discriminate]. split...
        intros l Hnotused. destruct (eq_dec a0 (proj1_sig sub l)).
        + subst. exfalso. specialize (Hnotused x). apply Hnotused. clear Hnotused. destruct Henvmem as [Henv _]. specialize (Henv x).
            inversion Henv;  try congruence. rewrite H3 in H2. inversion H2. destruct sub. 
            apply bijective_eq_iff_f_eq in H6... now subst.
        +  symmetry. subst. now apply p_map_not_same.

    - inversion Hderiv; subst; [|destruct bop; simpl in H1; discriminate]. split...
        intros l Hnotused.  destruct (eq_dec a0 (proj1_sig sub l)).
        + subst. exfalso. specialize (Hnotused x). apply Hnotused. clear Hnotused. destruct Henvmem as [Henv _]. specialize (Henv x).
            inversion Henv; subst;  try congruence.
            ++ rewrite H3 in H4. inversion H4. destruct sub. apply bijective_eq_iff_f_eq in H8... now subst.
            ++ now rewrite H3 in H4.
        + symmetry. now apply p_map_not_same_eq.

    - admit.  
    - admit.  
    - admit.
    - admit.
Admitted.

Definition weakening_of_gmp_statements_semantics_2 := 
    weakening_of_statement_semantics_2 Empty_exp_sem _gmp_stmt_sem _gmp_stmt_vars _weakening_of_gmp_statements_semantics_2.



Lemma _weakening_of_gmp_statements_semantics_3 : 
    _weakening_of_statement_semantics_3 _gmp_stmt_sem _gmp_stmt_vars exist_strong_env_mem_partial_order
.
Proof with eauto using refl_env_mem_partial_order with rac_hint ; try easy.
    intros Hweak ev s ev1 Hderiv. 
    induction Hderiv; intros ev' [ [sub [subrev [Hsub1 Hsub2]]] Hrel] [Henv Hmem].
    - exists (ev' <| env ; vars ::= {{x \ Def (VMpz (Some (subrev l)))}} |> <| mstate ::= {{subrev l \Defined 0}} |> ).
        apply S_init with u.
        + intros. specialize (H v). admit.
        +  assert (~(dom ev - dom ev')%utils x). {
            intros contra. apply Henv in contra. apply contra. simpl. auto.
            }
            apply not_in_sub_domain_prop in H1;[|apply in_domain_dec| apply in_domain_dec]. destruct H1.
            * now epose proof (strong_reverse_dom_same ev' ev x (UMpz u) sub subrev Hsub1 Hsub2 Hrel _ H1).
            * exfalso. apply H1. now exists (UMpz u).
    
    -  exists (ev' <| env ; vars ::= {{x\Def (VMpz None)}} |><| mstate ::= {{subrev a \ Undefined u}} |>). apply S_clear.
        assert (~(dom ev - dom ev')%utils x). {
            intros contra. apply Henv in contra. apply contra. simpl. auto.
        }
        apply not_in_sub_domain_prop in H0;[|apply in_domain_dec| apply in_domain_dec]. destruct H0.
        * now epose proof (strong_reverse_dom_same ev' ev x a sub subrev Hsub1 Hsub2 Hrel _ H0).
        * exfalso. apply H0. now exists a.

    - exists (ev' <| mstate ::= {{subrev a \ Defined (z) ̇}} |>). apply S_set_i.
        + assert (~(dom ev - dom ev')%utils x). {
            intros contra. apply Henv in contra. apply contra. simpl. auto.
        }
        apply not_in_sub_domain_prop in H1;[|apply in_domain_dec| apply in_domain_dec]. destruct H1.
        * now epose proof (strong_reverse_dom_same ev' ev x a sub subrev Hsub1 Hsub2 Hrel _ H1).
        * exfalso. apply H1. now exists a.

        + apply weakening_of_c_expression_semantics_3 with ev... 
            * eexists...
            * split. 
                **intros v Hdom. apply Henv in Hdom. simpl in Hdom.  
                apply Decidable.not_or in Hdom. now destruct Hdom.
                ** intros l Hdom. apply Hmem in Hdom as [l' Hdom]. simpl in Hdom.  exists l'. destruct Hdom. split... 
    - admit.  
    - admit.  
    - admit.  
    - admit.  
    - admit.
    - admit.
Admitted.




Definition weakening_of_gmp_statements_semantics_3 := 
    weakening_of_statement_semantics_3 Empty_exp_sem _gmp_stmt_sem _gmp_stmt_vars 
    (weakening_of_empty_expression_semantics_3 exist_strong_env_mem_partial_order) 
    _weakening_of_gmp_statements_semantics_3.
