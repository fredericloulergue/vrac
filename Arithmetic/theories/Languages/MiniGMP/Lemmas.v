From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax Semantics MiniC.Lemmas. 
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import ZArith.ZArith.
Open Scope Z_scope. 

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
    _weakening_of_statement_semantics_1 Empty_exp_sem _gmp_stmt_sem
.
Proof with eauto using refl_env_mem_partial_order with rac_hint ; try easy.
    intros _ f ev₀ s ev₁ Hderiv. 
    induction Hderiv; intros ev₀' sub Henvmem; 
        epose proof (fun y => weakening_of_c_expression_semantics y ev₀) as weak_exp;
        pose proof (eq_defined_mpz_mem_partial_order ev₀ ev₀' sub Henvmem) as eq_defined ;
        pose proof (eq_mpz_env_mem_partial_order ev₀ ev₀' sub Henvmem) as  eq_mpz ;
        pose proof (mem_def_partial_order_add) as mpz_add;
        pose proof (env_partial_order_add ev₀ ev₀' sub Henvmem) as env_add.
        (* init *)
        * exists (ev₀' <| env ; vars ::= {{x \ Def (VMpz (Some (proj1_sig sub l)))}} |> <| mstate ::= {{proj1_sig sub l \Defined 0}} |> ). split.
            + now apply mpz_add.
            + apply S_init with u.
                ++ intros v Hcontra.
                    (* the fact v is not bound to mpz location l by Ω₀ doesn't mean 
                        that v will also not be bound to mpz location l' by Ω₀' 
                    *) 
                    admit.
                ++ (* the semantic of ⊑ only ensures a defined mpz must stay the same, 
                        but here, x points to an undefined mpz value so it can be either stay like so or
                        be defined 
                    *)
                    admit.
        (* clear *)
        * exists (ev₀' <| env ; vars ::= {{x\Def (VMpz None)}} |><| mstate ::= {{(proj1_sig sub) a \ Undefined u}} |>). split.
            + now apply mpz_add.
            + apply S_clear. now apply (eq_mpz x (Some a)).

        (* set_i *)
        * exists (ev₀' <| mstate ::= {{(proj1_sig sub) a \ Defined (z) ̇}} |>).  split...
            apply S_set_i...
            ++ now apply (eq_mpz x (Some a)).
            ++ apply weak_exp... now exists sub.

        (* set_z *)
        * exists (ev₀' <| mstate ::= {{(proj1_sig sub) a \Defined z}} |>). split...
            + apply S_set_z with (proj1_sig sub n)...
                ++ now apply (eq_mpz x (Some a)).
                ++ now apply (eq_mpz y (Some n)).

        (* get_int *)
        *  exists (ev₀' <| env ; vars ::= fun e =>  e{x \ Def (VInt (zy ⁱⁿᵗ ir))} |>). split...
            apply S_get_int with (proj1_sig sub ly)... now apply (eq_mpz y (Some ly)).
        
        (* set_s *)
        * exists (ev₀' <| mstate ::= {{(proj1_sig sub) lx \ Defined zx}} |>). split...
            constructor... now apply (eq_mpz x (Some lx)).

        (* cmp *)
        *  exists (ev₀' <| env ; vars ::= fun e => e{c \induced sub b} |>). 
            split ... apply S_cmp with (proj1_sig sub lx) (proj1_sig sub ly) zx zy...
                ++ now apply (eq_mpz x (Some lx)).
                ++ now apply (eq_mpz y (Some ly)).
                ++ now apply cmp_induced.
        (* op *)
        * eexists (ev₀' <| mstate ::= {{(proj1_sig sub) lr \Defined (⋄ bop zx zy)}} |>). split.
            + now apply (mem_def_partial_order_add).
            + apply S_op with (proj1_sig sub lx) (proj1_sig sub ly)...
                ++ now apply (eq_mpz x (Some lx)).
                ++ now apply (eq_mpz y (Some ly)).
                ++ now apply (eq_mpz r (Some lr)).
Admitted.

Definition weakening_of_gmp_statements_semantics_1 := 
    weakening_of_statement_semantics_1 Empty_exp_sem _gmp_stmt_sem _weakening_of_gmp_statements_semantics_1.

Lemma _weakening_of_gmp_statements_semantics_2 : 
    _weakening_of_statement_semantics_2 Empty_exp_sem _gmp_stmt_sem
.
Proof with eauto using refl_env_mem_partial_order with rac_hint ; try easy.
    intros  exp_sem stmt_sem f ev₀ ev₀' s ev₁ [Hderiv1 Hrel].
    generalize dependent ev₀'.
    induction Hderiv1;  intros ev₀' Henvmem.
    - admit.      
    - admit.  
    - admit.  
    - admit.  
    - admit.  
    - admit.  
    - admit.  
    - admit.
Admitted.

Definition weakening_of_gmp_statements_semantics_2 := 
    weakening_of_statement_semantics_2 Empty_exp_sem _gmp_stmt_sem _weakening_of_gmp_statements_semantics_2.



Lemma _weakening_of_gmp_statements_semantics_3 : 
    _weakening_of_statement_semantics_3  _gmp_stmt_sem
.
Proof with eauto using refl_env_mem_partial_order with rac_hint ; try easy.
    intros Hweak ev s ev1 Hderiv. 
    induction Hderiv; intros ev' [sub Hrel] [Henv Hmem].
    - admit.      
    - exists (ev' <| env ; vars ::= {{x\Def (VMpz None)}} |><| mstate ::= {{(proj1_sig sub) a \ Undefined u}} |>). apply S_clear.
        admit.

    - exists (ev' <| mstate ::= {{(proj1_sig sub) a \ Defined (z) ̇}} |>). apply S_set_i.
        * admit.
        * eapply weakening_of_c_expression_semantics_3...  split.
            + intros v Hdom. now inversion Hdom.
            + intros l Hdom. now inversion Hdom.
    - admit.  
    - admit.  
    - admit.  
    - admit.  
    - admit.
Admitted.




Definition weakening_of_gmp_statements_semantics_3 := 
    weakening_of_statement_semantics_3 Empty_exp_sem _gmp_stmt_sem weakening_of_empty_expression_semantics_3 _weakening_of_gmp_statements_semantics_3.
