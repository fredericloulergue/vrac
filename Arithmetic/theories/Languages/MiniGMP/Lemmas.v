From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax Semantics MiniC.Lemmas. 
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import ZArith.ZArith.
Open Scope Z_scope. 

Lemma _weakening_of_gmp_statements_semantics_1 : 
    _weakening_of_statement_semantics_1 Empty_exp_sem _gmp_stmt_sem
.
Proof with eauto using eq_env_partial_order, eq_mem_partial_order,refl_env_mem_partial_order with rac_hint ; try easy.
    intros Hweak f ev₀ s ev₁.
    - intro Hderiv. induction Hderiv; intros ev₀' [Henv Hmem]; epose proof (fun y => weakening_of_c_expression_semantics y ev₀) as weak_exp.
        (* init *)
        * exists (ev₀' <| env ; vars ::= {{x \ Def (VMpz (Some l))}} |> <| mstate ::= {{l \Defined 0}} |> ). split.
            + split. 
                ++ apply env_partial_order_add... 
                ++ apply mems_partial_order_add...
            + apply S_init.
                ++ intros v Hcontra. 
                    (* the fact v is not bound to mpz location l by Ω₀ doesn't mean 
                        that v will also not be bound to mpz location l by Ω₀' 
                    *) 
                    admit.
                ++ (* the semantic of ⊑ only ensures a defined mpz must stay the same, 
                        but here, x points to an undefined mpz value so it can be either stay like so or
                        be defined 
                    *)
                    admit.
        (* clear *)
        * exists (ev₀' <| env ; vars ::= {{x\Def (VMpz None)}} |><| mstate ::= {{a \ Undefined u}} |>). split.
            + split.
                ++ apply env_partial_order_add...
                ++ apply mems_partial_order_add...
            + constructor... 

        (* set_i *)
        * exists (ev₀' <| mstate ::= {{a \ Defined (z) ̇}} |>). split.
            + split... intro n. apply (mems_partial_order_add ev₀ ev₀' Hmem a z ̇).  
            + apply S_set_i. eapply eq_env_partial_order... apply weak_exp...   

        (* set_z *)
        * exists (ev₀' <| mstate ::= {{a \ z}} |>). split.
            + split... intro n0.  apply (mems_partial_order_add ev₀ ev₀' Hmem a).
            + apply S_set_z with n...

        (* get_int *)
        *  eexists (ev₀' <| env ; vars ::= fun e =>  e{x \ Def (VInt (zy ⁱⁿᵗ ir))} |>)...  split.
            + split... simpl. pose proof env_partial_order_add...
            + apply S_get_int with ly...
        
        (* set_s *)
        * exists (ev₀' <| mstate ::= {{lx \ Defined zx}} |>). split.
            + split... apply (mems_partial_order_add ev₀ ev₀' Hmem lx zx). 
            + constructor...

        (* cmp *)
        *  eexists (ev₀' <| env ; vars ::= fun e => e{c \ b} |>). split.
            + split... simpl. pose env_partial_order_add...
            + apply S_cmp with lx ly zx zy...        
        
        (* op *)
        * eexists (ev₀' <| mstate ::= {{lr \Defined (⋄ bop zx zy)}} |>). split.
            + split... intro n. apply mems_partial_order_add...   
            + apply S_op with lx ly ; try apply weak_exp...  
Admitted.

Definition weakening_of_gmp_statements_semantics_1 := 
    weakening_of_statement_semantics_1 Empty_exp_sem _gmp_stmt_sem _weakening_of_gmp_statements_semantics_1.

