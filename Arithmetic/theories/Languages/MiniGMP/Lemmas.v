From Coq Require Import ZArith.ZArith.

From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax Semantics MiniC.Lemmas MiniGMP.Facts. 

Import FunctionalEnv Domain.
Import Environnement.Facts.

#[local] Open Scope utils_scope.
#[local] Open Scope Z_scope. 


Section GMPLemmas.

    Context {fe : rac_prog_fenv}.

    

    Lemma _LC21_weakening_of_gmp_statement_semantics :
        _LC21_weakening_of_statement_semantics Empty_exp_sem _gmp_stmt_sem
            exist_strong_env_mem_partial_order strong_env_mem_partial_order (fe:=fe)
    .
    Proof with eauto using refl_env_mem_partial_order with rac_hint ; try easy.
        intros _ ev₀ s ev₁ Hderiv. 
        induction Hderiv; intros ev₀' sub Hstrenvmem; apply strong_env_mem_stronger in Hstrenvmem as Henvmem; 
            epose proof (fun y => weakening_of_c_expression_semantics y ev₀) as weak_exp;
            pose proof (eq_defined_mpz_mem_partial_order ev₀ ev₀' sub Henvmem) as eq_defined ;
            pose proof (eq_mpz_env_mem_partial_order ev₀ ev₀' sub Henvmem) as  eq_mpz ;
            pose proof (mem_def_partial_order_add) as mpz_add;
            pose proof (env_partial_order_add ev₀ ev₀' sub Henvmem) as env_add.

        (* init *)
        - clear weak_exp eq_defined eq_mpz env_add. 
            exists (ev₀'    <| env ; vars ::= {{x \ Def (VMpz (Some (proj1_sig sub l)))}} |> 
                            <| mstate ::= {{proj1_sig sub l \Defined 0}} |> ).
            split.
            + admit. (* now apply mpz_add. *)
            + clear mpz_add. apply S_init with u.
                * intros v. admit.
                * destruct Hstrenvmem as [e m]. now apply e in H0.
                    
        (* clear *)
        - exists (ev₀'  <| env ; vars ::= {{x\Def (VMpz None)}} |>
                        <| mstate ::= {{(proj1_sig sub) a \ Undefined u}} |>). split.
            + admit. (* now apply mpz_add. *)
            + apply S_clear. now apply (eq_mpz x (Some a)).

        (* set_i *)
        - exists (ev₀' <| mstate ::= {{(proj1_sig sub) a \ Defined (z) ̇}} |>).  split...
            +  admit.
            + apply S_set_i...
                * now apply (eq_mpz x (Some a)).
                * apply weak_exp... now exists sub.

        (* set_z *)
        - exists (ev₀' <| mstate ::= {{(proj1_sig sub) a \Defined z}} |>). split...
            + admit.
            + apply S_set_z with (proj1_sig sub n)...
                * now apply (eq_mpz x (Some a)).
                * now apply (eq_mpz y (Some n)).

        (* get_int *)
        -  exists (ev₀' <| env ; vars ::= fun e =>  e{x \ Def (VInt (zy ⁱⁿᵗ ir))} |>). split... 
            + admit.
            + apply S_get_int with (proj1_sig sub ly)... now apply (eq_mpz y (Some ly)).
        
        (* set_s *)
        - exists (ev₀' <| mstate ::= {{(proj1_sig sub) lx \ Defined zx}} |>). split... 
            + admit.
            + constructor... now apply (eq_mpz x (Some lx)).

        (* cmp *)
        -  exists (ev₀' <| env ; vars ::= fun e => e{c \induced (proj1_sig sub) b} |>).  split ... 
            + admit.
            + apply S_cmp with (proj1_sig sub lx) (proj1_sig sub ly) zx zy...
                * now apply (eq_mpz x (Some lx)).
                * now apply (eq_mpz y (Some ly)).
                * now apply cmp_induced.
        (* op *)
        - eexists (ev₀' <| mstate ::= {{(proj1_sig sub) lr \Defined (⋄ bop zx zy)}} |>). split. 
            + admit. (* now apply (mem_def_partial_order_add). *)
            + apply S_op with (proj1_sig sub lx) (proj1_sig sub ly)...
                * now apply (eq_mpz x (Some lx)).
                * now apply (eq_mpz y (Some ly)).
                * now apply (eq_mpz r (Some lr)).
    Admitted.



    Definition LC21_weakening_of_gmp_statement_semantics := 
        LC21_weakening_of_statement_semantics_strong Empty_exp_sem _gmp_stmt_sem 
        _determinist_gmp_stmt_eval
        weakening_of_empty_expression_semantics
        _LC21_weakening_of_gmp_statement_semantics
        (LC1_weakening_of_expression_semantics Empty_exp_sem weakening_of_empty_expression_semantics)
        (ext_used_stmt_vars:=_gmp_used_stmt_vars) (ext_ty_val:=_type_of_gmp) (fe:=fe)
    .
    

    Lemma _LC22_weakening_of_gmp_statement_semantics : 
        _LC22_weakening_of_statement_semantics Empty_exp_sem _gmp_stmt_sem exist_env_mem_partial_order env_mem_partial_order (fe:=fe)
    .
    Proof with unshelve eauto using refl_env_mem_partial_order with rac_hint ; try easy.
        red. intros Hexpsem * [Hderiv1 Hrel]. generalize dependent ev₀'.
        assert (Hvars : 
            forall (ev ev': Env) v v' val val' mem, 
            ev v' = Some val' ->
            (v ∉ ev)%dom_ ->
            ev' v = (ev' <| env; vars ::= {{v' \ Def val}} |> <|mstate := mem |>) v
        ). {
            intros. destruct (eq_dec v v').
            - subst. exfalso. congruence.  
            - symmetry. now apply p_map_not_same_eq. 
        }
        assert (Hlocs : 
            forall (ev ev': Env) (v v' v'':location) val x e, 
            env_mem_partial_order ev ev' sub ->
            ev x = Some (Def (VMpz v'')) ->
            ev' x = Some (Def (VMpz (Some v'))) ->
            fresh_location ev  v  ->
            ev'.(mstate) (proj1_sig sub v) = (ev' <| env;vars ::=e |> <| mstate ::= {{v'\val}} |>).(mstate) (proj1_sig sub v)
            ). {
            intros ev ev' v v' v'' val x e Henvmem Hnotused Hev Hev'. destruct (eq_dec (proj1_sig sub v) v').
            - subst. exfalso. destruct Henvmem as [Henv _]. specialize (Henv x). 
                inversion Henv;  try congruence.  rewrite Hev in H0. inversion H0. destruct sub. simpl in *.
                apply bijective_eq_iff_f_eq in H2... subst. eapply Hev'...
            - symmetry. now apply p_map_not_same_eq.
        }

        induction Hderiv1;  intros ev Henvmem ev' Hderiv; specialize (Hvars ev₀ ev); specialize (Hlocs ev₀ ev);
        inversion Hderiv; subst; try (destruct bop; simpl in H1; discriminate). 
        

        (* init *)
        - split.
            + intros. eapply Hvars... 
            + intros l' Hnotused. destruct (eq_dec (proj1_sig sub l') l0).
                * subst. exfalso.  admit. 
                    (* not provable, requires stronger Hnotused hypothesis *)
                * symmetry. now apply p_map_not_same_eq.

        (* clear *)
        - split.
            + intros. eapply Hvars...
            + intros. eapply Hlocs...

        (* set_i *)
        -  split...
            intros. eapply Hlocs... 

        (* set_z *)
        - split... intros. eapply Hlocs with (v'':= a)...
        
        (* get_int *)
        - split...
            intros v [Hnotused Hcomp]. destruct (eq_dec v x). 
            * subst. admit. (* semantics doesn't give assignment restriction for x *)
            * symmetry. now apply p_map_not_same_eq.
            
        (* set_s *)   
        - split... intros. eapply Hlocs...

        (* cmp *)
        -  split...
            intros v [Hnotused Hcomp]. destruct (eq_dec v c).
            * subst. exfalso. admit. (* same issue as get_int *)
            * symmetry. now apply p_map_not_same_eq.
        
        (* binop *)
        - split... intros. eapply Hlocs...  destruct bop,bop0; simpl in H4; inversion H4; now subst. 
        
    Admitted.

    Definition LC22_weakening_of_gmp_statement_semantics := 
        LC22_weakening_of_statement_semantics Empty_exp_sem _gmp_stmt_sem  
        weakening_of_empty_expression_semantics
        _LC22_weakening_of_gmp_statement_semantics
        (LC1_weakening_of_expression_semantics Empty_exp_sem weakening_of_empty_expression_semantics)
        (ext_used_stmt_vars:=_gmp_used_stmt_vars) (ext_ty_val:=_type_of_gmp) (fe:=fe)
    .



    Lemma _LC23_weakening_of_gmp_statement_semantics : 
        _LC23_weakening_of_statement_semantics _gmp_stmt_sem strong_env_mem_partial_order
            (ext_used_stmt_vars := _gmp_used_stmt_vars) (fe:=fe) 
    .
    Proof with eauto using refl_env_mem_partial_order with rac_hint ; try easy.
        intros ev s ev1 [sub [subrev [Hsub1 Hsub2]]] Hderiv. 
        induction Hderiv; intros ev' Hrel [Henv Hmem].
        (* todo: factorize *)

        (* init *)
        - exists (ev' <| env ; vars ::= {{x \ Def (VMpz (Some (subrev l)))}} |> <| mstate ::= {{subrev l \Defined 0}} |> ).
            apply S_init with u.
            + intros x'. specialize (H x'). intros contra. destruct Hrel as [Hrel _]. specialize (Hrel x _ _ contra). simpl in *.  
                inversion Hrel. congruence.

            +  assert (~(dom ev - dom ev')%dom_ x). {
                intros contra. apply Henv in contra. apply contra. simpl. StringSet.D.fsetdec. 
                }
                apply not_in_sub_domain_prop in H1;[|apply in_domain_dec| apply in_domain_dec]. destruct H1.
                * now unshelve epose proof (strong_reverse_dom_same_env ev' ev x (UMpz u) sub subrev Hsub1 Hsub2 Hrel _ H1).
                * exfalso. apply H1. now exists (UMpz u).
        
        (* clear *)
        -  exists (ev' <| env ; vars ::= {{x\Def (VMpz None)}} |><| mstate ::= {{subrev a \ Undefined u}} |>). apply S_clear.
            assert (~(dom ev - dom ev')%dom_ x). {
                intros contra. apply Henv in contra. apply contra. simpl. StringSet.D.fsetdec.
            }
            apply not_in_sub_domain_prop in H0;[|apply in_domain_dec| apply in_domain_dec]. destruct H0.
            * now unshelve epose proof (strong_reverse_dom_same_env ev' ev x a sub subrev Hsub1 Hsub2 Hrel _ H0).
            * exfalso. apply H0. now exists a.

        (* set_i *)
        - exists (ev' <| mstate ::= {{subrev a \ Defined (z) ̇}} |>). apply S_set_i.
            + assert (~(dom ev - dom ev')%dom_ x). {
                intros contra. apply Henv in contra. apply contra. simpl. StringSet.D.fsetdec.
            }
            apply not_in_sub_domain_prop in H1;[|apply in_domain_dec| apply in_domain_dec]. destruct H1.
            * now unshelve epose proof (strong_reverse_dom_same_env ev' ev x a sub subrev Hsub1 Hsub2 Hrel _ H1).
            * exfalso. apply H1. now exists a.

            + eapply weakening_of_c_expression_semantics_3... split. 
                * intros v Hdom. apply Henv in Hdom. simpl in Hdom. StringSet.D.fsetdec.
                * intros l Hdom. apply Hmem in Hdom as [l' Hdom]. simpl in Hdom.  exists l'. destruct Hdom. split... 
                    StringSet.D.fsetdec.
        
        (* set_z *)
        - exists (ev' <| mstate ::= {{subrev a \ Defined z}} |>). apply S_set_z with (subrev n).
            + assert (~(dom ev - dom ev')%dom_ x). {
                intros contra. apply Henv in contra. apply contra. simpl. StringSet.D.fsetdec.
                }
                apply not_in_sub_domain_prop in H2;[|apply in_domain_dec| apply in_domain_dec]. destruct H2.
                * now unshelve epose proof (strong_reverse_dom_same_env ev' ev x a sub subrev Hsub1 Hsub2 Hrel _ H2).
                * exfalso. apply H2. now exists a.
            + assert (~(dom ev - dom ev')%dom_ y). {
                intros contra. apply Henv in contra. apply contra. simpl. StringSet.D.fsetdec.
                }
                apply not_in_sub_domain_prop in H2;[|apply in_domain_dec| apply in_domain_dec]. destruct H2.
                * now unshelve epose proof (strong_reverse_dom_same_env ev' ev y n sub subrev Hsub1 Hsub2 Hrel _ H2).
                * exfalso. apply H2. now exists n.
            + assert (~(dom ev.(mstate) - dom ev'.(mstate))%dom_ (subrev n)). {
                intros contra. apply Hmem in contra. destruct contra. simpl in H2. destruct H2 as [H2 []].
                rewrite Hsub2 in H2. assert (x0 = y). { admit. (* no aliasing *) } subst. StringSet.D.fsetdec.
                } 
                apply not_in_sub_domain_prop in H2;[|apply in_domain_dec| apply in_domain_dec]. destruct H2.
                * now unshelve epose proof (strong_reverse_dom_same_mem ev' ev _ z sub subrev Hsub1 Hsub2 Hrel _ H2).
                * destruct H2. admit.

        - exists (ev' <| env ; vars ::= {{x\VInt (zy ⁱⁿᵗ ir) : 𝕍}} |>). apply S_get_int with (subrev ly).
            + assert (~(dom ev - dom ev')%dom_ y). {
                intros contra. apply Henv in contra. apply contra. simpl. StringSet.D.fsetdec.
                }
                apply not_in_sub_domain_prop in H1;[|apply in_domain_dec| apply in_domain_dec]. destruct H1.
                * now  unshelve epose proof (strong_reverse_dom_same_env ev' ev y ly sub subrev Hsub1 Hsub2 Hrel _ H1).
                * destruct H1. now exists ly.

            + assert (~(dom ev.(mstate) - dom ev'.(mstate))%dom_ (subrev ly)). {
                intros contra. apply Hmem in contra. destruct contra. simpl in H1. destruct H1 as [H1 []].
                rewrite Hsub2 in H1. assert (x0 = y). { admit. (* no aliasing *) } subst. StringSet.D.fsetdec.
                } 
                apply not_in_sub_domain_prop in H1;[|apply in_domain_dec| apply in_domain_dec]. destruct H1.
                * now unshelve epose proof (strong_reverse_dom_same_mem ev' ev _ zy sub subrev Hsub1 Hsub2 Hrel _ H1).
                *  destruct H1. admit.
        
        - exists (ev' <| mstate ::= {{subrev lx\Defined zx}} |>). apply S_set_s...
            assert (~(dom ev - dom ev')%dom_ x). {
                intros contra. apply Henv in contra. apply contra. simpl. StringSet.D.fsetdec.
                }
                apply not_in_sub_domain_prop in H1;[|apply in_domain_dec| apply in_domain_dec]. destruct H1.
                * now  unshelve epose proof (strong_reverse_dom_same_env ev' ev x lx sub subrev Hsub1 Hsub2 Hrel _ H1).
                * destruct H1. now exists lx.


        - exists (ev' <| env ; vars ::= {{c\b}} |>). eapply S_cmp with (subrev lx) (subrev ly) _ _...  
            +  assert (~(dom ev - dom ev')%dom_ x). {
                intros contra. apply Henv in contra. apply contra. simpl. StringSet.D.fsetdec.
                }
                apply not_in_sub_domain_prop in H4;[|apply in_domain_dec| apply in_domain_dec]. destruct H4.
                * now  unshelve epose proof (strong_reverse_dom_same_env ev' ev x lx sub subrev Hsub1 Hsub2 Hrel _ H4).
                * destruct H4. now exists lx.
            + assert (~(dom ev - dom ev')%dom_ y). {
                intros contra. apply Henv in contra. apply contra. simpl. StringSet.D.fsetdec.
                }
                apply not_in_sub_domain_prop in H4;[|apply in_domain_dec| apply in_domain_dec]. destruct H4.
                * now  unshelve epose proof (strong_reverse_dom_same_env ev' ev y ly sub subrev Hsub1 Hsub2 Hrel _ H4).
                * destruct H4. now exists ly.
            + assert (~(dom ev.(mstate) - dom ev'.(mstate))%dom_ (subrev lx)). {
                intros contra. apply Hmem in contra. destruct contra. simpl in H4. destruct H4 as [H4 []].
                rewrite Hsub2 in H4. assert (x0 = y). { admit. (* no aliasing *) } subst. StringSet.D.fsetdec.
                } 
                apply not_in_sub_domain_prop in H4;[|apply in_domain_dec| apply in_domain_dec]. destruct H4.
                * now unshelve epose proof (strong_reverse_dom_same_mem ev' ev _ zx sub subrev Hsub1 Hsub2 Hrel _ H4).
                *  destruct H4. admit.
            + assert (~(dom ev.(mstate) - dom ev'.(mstate))%dom_ (subrev ly)). {
                intros contra. apply Hmem in contra. destruct contra. simpl in H4. destruct H4 as [H4 []].
                rewrite Hsub2 in H4. assert (x0 = y). { admit. (* no aliasing *) } subst. StringSet.D.fsetdec.
                } 
                apply not_in_sub_domain_prop in H4;[|apply in_domain_dec| apply in_domain_dec]. destruct H4.
                * now unshelve epose proof (strong_reverse_dom_same_mem ev' ev _ zy sub subrev Hsub1 Hsub2 Hrel _ H4).
                *  destruct H4. admit.


        - exists (ev'<| mstate ::= {{subrev lr\Defined (⋄ (□ bop) zx zy) }} |>). apply S_op with (subrev lx) (subrev ly).
            + assert (~(dom ev - dom ev')%dom_ x). {
                intros contra. apply Henv in contra. apply contra. simpl. destruct bop; simpl ; StringSet.D.fsetdec.
                }
                apply not_in_sub_domain_prop in H4;[|apply in_domain_dec| apply in_domain_dec]. destruct H4.
                * now  unshelve epose proof (strong_reverse_dom_same_env ev' ev x lx sub subrev Hsub1 Hsub2 Hrel _ H4).
                * destruct H4. now exists lx.

            
            + assert (~(dom ev - dom ev')%dom_ y). {
                intros contra. apply Henv in contra. apply contra. simpl. destruct bop; simpl ; StringSet.D.fsetdec.
                }
                apply not_in_sub_domain_prop in H4;[|apply in_domain_dec| apply in_domain_dec]. destruct H4.
                * now  unshelve epose proof (strong_reverse_dom_same_env ev' ev y ly sub subrev Hsub1 Hsub2 Hrel _ H4).
                * destruct H4. now exists ly.

            + assert (~(dom ev.(mstate) - dom ev'.(mstate))%dom_ (subrev lx)). {
                intros contra. apply Hmem in contra. destruct contra. simpl in H4. destruct H4 as [H4 []].
                rewrite Hsub2 in H4. assert (x0 = y). { admit. (* no aliasing *) } subst. destruct bop; simpl ; StringSet.D.fsetdec.
                } 
                apply not_in_sub_domain_prop in H4;[|apply in_domain_dec| apply in_domain_dec]. destruct H4.
                * now unshelve epose proof (strong_reverse_dom_same_mem ev' ev _ zx sub subrev Hsub1 Hsub2 Hrel _ H4).
                *  destruct H4. admit.

            + assert (~(dom ev.(mstate) - dom ev'.(mstate))%dom_ (subrev ly)). {
                intros contra. apply Hmem in contra. destruct contra. simpl in H4. destruct H4 as [H4 []].
                rewrite Hsub2 in H4. assert (x0 = y). { admit. (* no aliasing *) } subst. destruct bop; simpl ; StringSet.D.fsetdec.
                } 
                apply not_in_sub_domain_prop in H4;[|apply in_domain_dec| apply in_domain_dec]. destruct H4.
                * now unshelve epose proof (strong_reverse_dom_same_mem ev' ev _ zy sub subrev Hsub1 Hsub2 Hrel _ H4).
                *  destruct H4. admit.
            
            + assert (~(dom ev - dom ev')%dom_ r). {
                intros contra. apply Henv in contra. apply contra. simpl. destruct bop; simpl ; StringSet.D.fsetdec.
                }
                apply not_in_sub_domain_prop in H4;[|apply in_domain_dec| apply in_domain_dec]. destruct H4.
                * now  unshelve epose proof (strong_reverse_dom_same_env ev' ev _ lr sub subrev Hsub1 Hsub2 Hrel _ H4).
                * destruct H4. now exists lr.                
    Admitted.


    Definition LC23_weakening_of_gmp_statement_semantics := 
        LC23_weakening_of_statement_semantics Empty_exp_sem  _gmp_stmt_sem 
        (weakening_of_empty_expression_semantics_3 strong_env_mem_partial_order) 
        _LC23_weakening_of_gmp_statement_semantics
        (ext_used_stmt_vars:=_gmp_used_stmt_vars) (ext_ty_val:=_type_of_gmp)
    .

End GMPLemmas.

