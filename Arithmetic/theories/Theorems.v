From Coq Require Import ZArith.ZArith Strings.String Strings.Ascii Ensembles.
From RAC Require Import Utils Environnement.Facts Macros Oracle Translation Invariants.
From RAC.Languages Require Import Syntax Semantics Lemmas MiniFSL.Semantics.

#[local] Open Scope utils_scope.
#[local] Open Scope list.
#[local] Open Scope Z_scope.
#[local] Open Scope string_scope.


Import RecordSetNotations.
Import FunctionalEnv Domain.

Module Theorems(Or:Oracle).
    #[local] Open Scope mini_c_scope.
    #[local] Open Scope mini_gmp_scope.

    Module I := Invariants(Or).
    Import I.

    (* Section C : PROPERTIES OF THE SEMANTICS *)
    (* -> Languages/{MiniC,MiniGMP}/Lemmas.v *)

    Parameter P : fsl_pgrm.

    Parameter WellFormedProgram : 
        List.NoDup (snd P)    
    .

    Section D. (* PROOFS OF STRUCTURAL PROPERTIES OF THE TRANSLATION *)

        (* `if the generated program has a semantic [...]'  but no semantic given for a program   *)
        Lemma LD1_mpz_pointer_invariant : forall fenv,
            Forall_routines ⟦P⟧ ( fun _ _ b => 
                forall (renv renv' : Env),
                forall v, type_of_value (renv v) = Some (T_Ext Mpz) ->
                forall s, between <( init(v) )> s <( cl(v) )> b -> 
                (renv |= s => renv')%gmpssem fenv ->
                renv v = renv' v
            )
        .
        Proof.
        Admitted.

        Lemma LD2_absence_of_aliasing : forall fenv,
            Forall_routines ⟦P⟧ ( fun _ _ b => 
                forall s (renv renv' : Env),
                (renv |= s => renv')%gmpssem fenv ->
                forall v (l:location), renv' v = Some (Def (VMpz l)) ->
                forall v' (l':location), v' <> v /\ renv' v' =  Some (Def (VMpz l')) ->
                l <> l'
            )
        .
        Proof.
        Admitted.


        Lemma LD3_preservation_of_control_flow : 
            Forall_routines ⟦P⟧ ( fun _ _ b => 
                forall decls s,
                In_stmt (S_Ext (GMP_Scope decls s)) b -> 
                (* passes through: how to represent control flow ?  *)
                True
            )
        .
        Admitted.

        Lemma LD4 :
            (* translate_predicate ... *)
            True.
        Proof.
        Admitted.


        Lemma LD5_memory_transparency_of_generated_code :
            Forall_routines ⟦P⟧ ( fun _ _ b => 
                forall decls s,
                In_stmt (S_Ext (GMP_Scope decls s)) b -> 
                (* todo: add decls tec *)
                True
            )
        .
        Proof.
        Admitted.

        Theorem T61_absence_of_dangling_pointers : forall fenv,
            Forall_routines ⟦P⟧ ( fun _ _ b => 
                forall s (renv renv' : Env),
                (renv |= s => renv')%gmpssem fenv ->
                forall (l:location), renv'.(mstate) l <> None <->  exists! x, renv' x = Some (Def (VMpz l))
            ). 
        Proof. 
        Admitted.   

        Theorem T62_absence_of_memory_leak :  forall P env env',
            gmp_pgrm_sem env ⟦P⟧ env' ->
            env'.(mstate) = ⊥
        .
        Proof. 
    Admitted.

    End D.

    (* Section E : PROOFS OF THE SEMANTICS OF THE MACROS *)

    (* -> Macros.v *)

    (* Section F  : INVARIANTS FOR ROUTINE TRANSLATION *)

    (* -> Invariants.v *)



    (* Section G : PRESERVATION OF THE SEMANTICS *)
    #[local] Open Scope fsl_sem_scope.


    Definition env_Γ (env env': Env) (g:Γ) : Prop :=  
        forall (ens : 𝐴),
        (
            I1 env g ->
            forall t v z, 
                Ensembles.In _ ens (t,v,z) 
                <-> 
                Γdom g v /\
                Some z = env.(binds) v /\
                exists i,
                StringMap.find v (snd g) = Some i /\
                t = ϴ i
        )
        /\
        (env +++ ens) env'
    .


    Definition env_Γ_t fenv (env env': Env) (g:Γ) (p:T.ψ) (t:ℨ) : Prop :=  
        forall env'' (ens : 𝐴),
        (
            forall ty v z,  
                (Ensembles.In _ ens (ty,v,z) 
                <-> 
                
                List.In (v,ty) (TM.exec (translate_term fenv g p t)).(decls))
                /\
                (z = 0 <-> ty = T_Ext Mpz)
                /\
                (exists u, z = u (*fixme: must be undef value *)  <-> ty = C_Int)       
        ) /\
        env_Γ env env'' g /\
        (env'' +++ ens) env'
    .

    Definition env_Γ_p fenv (env env': Env) (g:Γ) (p:T.ψ) (pred:𝔅) : Prop :=  
        forall env'' (ens : 𝐴),
        (
            forall ty v z,  
                (Ensembles.In _ ens (ty,v,z) 
                <-> 
                List.In (v,ty) (TM.exec (translate_pred fenv g p pred)).(decls))
                /\
                (z = 0 <-> ty = T_Ext Mpz)
                /\
                (exists u, z = u (*fixme: must be undef value *)  <-> ty = C_Int)       
        ) ->
        env_Γ env env'' g /\
        (env'' +++ ens) env'
    .


    Lemma LG1_semantics_of_term_translation : 
        forall (t:fsl_term) fenv (env:Env) g (p:T.ψ), 
            I1 env g ->
            I2 p g fenv ->
            forall env_g, env_Γ env env_g g ->
            forall env_gt, env_Γ_t fenv env env_gt g p t  ->

            forall z,
            (
                (env |= t => z)%fsltsem fenv
                <-> 
                (
                    let result := TM.exec (translate_term fenv g p t) in

                    exists env', 
                        (env_g ⊑ env')%envmem 
                    /\
                        forall fenv', (env_gt |= result.(tr).(chunk) =>  env')%gmpssem fenv'
                    /\
                        env' |= C_Id (fst result.(res)) (snd result.(res)) ⇝ z
                    /\
                        match get_ty (t,snd g) with
                        | C_Int =>  
                            exists irz, env'.(vars) (fst (result.(res))) = Some (Def (VInt (z ⁱⁿᵗ irz)))
                        | T_Ext Mpz => 
                            exists l, env'.(vars) (fst result.(res)) = Some (Def (VMpz (Some l)))
                            /\
                            env'.(mstate) l = Some (Defined z)
                        | _ => False
                        end
                    )
                
            ) 

    with LG2_semantics_of_predicate_translation :        
        forall (pred:predicate) fenv (env:Env) g (p:T.ψ), 
            I1 env g ->
            I2 p g fenv ->
            forall env_g,  env_Γ env env_g g ->
            forall env_gp, env_Γ_p fenv env env_gp g p pred ->

            forall b,
            (
                (env |= pred => b)%fslpsem fenv
                <->
                (
                    let result := TM.exec (translate_pred fenv g p pred) in
                    
                    exists env', 
                        (env_g ⊑ env')%envmem 
                    /\
                        forall fenv', (env_gp |= result.(tr).(chunk) =>  env')%gmpssem fenv'
                    /\
                        exists irb, env'.(vars) (fst result.(res)) = Some (Def (VInt (((𝔹_to_Z b) ⁱⁿᵗ irb))))
                )
            )
    with LG3_semantics_of_function_generation : 
        forall p g (fe : fsl_prog_fenv) vargs, 
        I2 p g fe ->
        (
            forall f body, StringMap.find f fe.(lfuns) = Some (vargs,body) ->
            List.Forall (fun v => Γdom g v)%dom_ vargs -> True
            (* TM.exec (generate_function fe g p f)  *)
            (* let new_fenv : @fenv _fsl_statement Datatypes.Empty_set := 
            mk_fenv _ _ fe.(funs) fe.(procs) (StringMap.add result.(chunk) _ fe.(lfuns)) fe.(preds) in  *)
            (* suitable new_fenv g result.(chunk) f *)
        )
        /\
        (
            forall f body, StringMap.find f fe.(preds) = Some (vargs,body) ->
            List.Forall (fun v => Γdom g v)%dom_ vargs ->
            (* TM.exec (generate_function fe g p f)  *)
            (* let new_fenv : @fenv _fsl_statement Datatypes.Empty_set :=
             mk_fenv _ _ fe.(funs) fe.(procs) fe.(lfuns) (StringMap.add result.(chunk) _ fe.(preds)) in  *)
            (* suitable new_fenv g result.(chunk) f *)
            True
        )


    .
    Proof.
    {
        induction t; intros fenv e g p HI1 HI2 env_g Henvg env_gt Henvgt z'; split; intros Htsem.

        (* t is an integer *)
        -  remember (get_ty (T_Z z',snd g)) as ty. destruct ty; simpl in * ; inversion Htsem ; subst ; simp translate_fsl in *; cbn in *.
            + rewrite <- Heqty in *. 
                pose proof (Or.type_soundness _ (snd g) _ _  _  Htsem) as Hfit. inversion Hfit; [|congruence].
                exists (env_gt <| env; vars ::= {{"_v0"\Def (VInt (z' ⁱⁿᵗ H0))}} |> ).   repeat split.
                * admit.
                * subst. simpl. apply LE3_semantics_of_the_Z_assgn_macro_tint.
                    ** unfold is_comp_var. simpl. admit.
                    ** admit.

                * subst. simpl.  epose proof (M_Int (env_gt <| env; vars ::= {{"_v0" \Def (VInt (z' ⁱⁿᵗ H0))}} |> ) (C_Id "_v0" C_Int) (z' ⁱⁿᵗ H0)). apply H1. 
                    ** easy.
                    ** simpl. now constructor.
                * exists H0. subst. simpl. constructor.

            + exfalso. admit.

            + destruct t.
                * exfalso. admit.
                * rewrite <- Heqty in *.
                    assert (H2: exists x, env_gt = (env_g <| env; vars ::= {{"_v0"\Def x}} |> <| mstate ::= {{x\Defined 0}} |>)) by admit.
                    destruct H2 as [l H2].
                    exists (env_gt <| mstate ::= {{l\Defined z'}} |> ). repeat split.
                    ** admit.
                    **  apply LE3_semantics_of_the_Z_assgn_macro_tmpz. subst. apply p_map_same.
                    ** subst. simpl. apply M_Mpz with l; auto. simpl. apply p_map_same.
                    ** exists l. subst. simpl. split; apply p_map_same.

        - admit.

        (* t is a program/logic variable *)
        - inversion Htsem; subst;  simp translate_fsl in *;  cbn in *.
            (* logic variable *)
                + {
                    assert (Hsome :
                    exists r,  StringMap.find name (fst g) = Some r
                    ) by admit.
                    destruct Hsome as [x Hsome].  destruct x. 
                    exists env_g. repeat split.
                
                    - apply refl_env_mem_partial_order.
                    - subst. simpl. admit.
                    - subst. simpl in *.  inversion HI1. admit.
                    - subst. simpl. destruct get_ty eqn:ty.
                        * admit.
                        * exfalso. admit.
                        * destruct t.
                        + exfalso. admit.
                        + admit.
                    }

            (* program variable *)
            + {
                exists env_g.  repeat split.
                - apply refl_env_mem_partial_order.
                - subst. simpl. admit.
                - subst. simpl. constructor.
                    + easy.
                    + simpl. constructor. admit.
                - assert (H3: (get_ty (T_Id name FSL_Int,snd g)) = C_Int) by admit. rewrite H3. subst. simpl. 
                destruct x. simpl in *. exists i. admit.  
            }


        - admit.


        (* t is the application of an operation *)
        - (* assert (Hgt1: ((env_Γ_t fenv e g p (T_BinOp t1 op t2) env_gt1) ⊑ (env_Γ_t fenv e g p (T_BinOp t1 op t2) env_gt))%envmem ). *)
        
            specialize (IHt1 fenv e g p HI1 HI2 env_g Henvg env_gt).  inversion Htsem. subst.  admit.
        - admit.

        (* t is a conditional *)
        - admit.
        - admit.

        (* t is a call *)
        - admit.
        - admit.
    }

    {
        admit.
    }
    {
        admit.
    }
    Admitted.


    Theorem TG4_soundness_of_assertion_translation : 
        forall env pred fenv g p, 
        (env |= pred => BTrue)%fslpsem fenv
        <->
        (
            let assert_trans := TM.exec (translate_statement fenv g p <{ /*@ assert pred */ }>) in
            exists (env':Ω),
            (env <| mstate := ⊥ |> |= assert_trans.(chunk) => mkEnv env' ⊥)%gmpssem (build_rac_fenv assert_trans.(glob))
        )
    .
    Proof.
        intros env pred fenv g p.

        assert (I1 env g) as HI1 by admit.
        assert (I2 p g fenv) as HI2 by admit.
        assert (env_g : Env) by auto. assert (Henv_g : env_Γ env env_g g) by admit.  
        assert (env_gp : Env) by auto. assert (Henv_gp : env_Γ_p fenv env env_gp g p pred ) by admit.


        pose proof (LG2_semantics_of_predicate_translation pred fenv env g p HI1 HI2 env_g Henv_g env_gp Henv_gp BTrue).


        simpl.  unfold TM.ret, TM.exec, TM.bind, translate_pred in *. simpl in H.

        destruct (translate_fsl tr_pred fenv g p pred 0%nat) eqn:TrEq.

        pose (C_Id (fst (res t)) (snd (res t))) as var.
        pose (<{(INITS (decls t)); (chunk (tr t)); assert var; (CLEARS (decls t))}>)%gmp as instrs.
        pose (GMP_Scope (DECLS (decls t)) instrs) as scope.
        pose (tr t <| chunk := S_Ext scope |> ) as assert_res.
        pose (build_rac_fenv (glob (tr t))) as fenv'.


        split.

        - intros Hptrue. destruct H as [H _]. specialize (H Hptrue).
            destruct H as [env' [Hrel Hsem]]. specialize (Hsem fenv'). 
            exists env. simpl. 
        
            pose proof (S_Scope (build_rac_fenv (glob (tr t))) (env <| mstate := ⊥ |>) (DECLS (decls t)) instrs env_g env') as Scope. 
            simpl in Scope. 
            assert (env'.(mstate) = ⊥) by admit.   (* T62_absence_of_memory_leak *) rewrite H in Scope.
            constructor. subst scope instrs var assert_res. apply Scope; clear Scope.
            + admit.
            + econstructor.
                * admit.
                * econstructor.
                    -- admit.
                    -- admit.
        
        - intros Htrans. destruct H as [_ H]. apply H. clear H. destruct Htrans as [env' Henv]. exists (mkEnv env' ⊥). split.
            + admit.
            + intros. split.
                * admit.
                * exists oneinRange. subst scope instrs var assert_res. simpl in Henv. 
    Admitted.


    Theorem TG5_transparancy_of_assertion_translation : 
    forall pred g p fenv,
    let assert_trans :=TM.exec (translate_statement fenv g p <{ /*@ assert pred */ }>) in
    forall env env',
    (env <| mstate := ⊥ |> |= assert_trans.(chunk) => mkEnv env' ⊥)%gmpssem (build_rac_fenv assert_trans.(glob)) ->
    (env ⊑ env')%env
    .
    Proof.
        intros pred g p fenv Htrans env env' Hsem. 
    Admitted.



    (* Fact correctness_of_routine_translation : forall (P:fsl_pgrm),
        forall (e:Ω),
        fsl_pgrm_sem empty_env P (empty_env <|env ; vars := e|>) <->
        forall fe t_env routines,
        TMOps.fold (translate_routine fe t_env) routines (nil, nil, GlobalDef.empty) = TM.ret (nil,nil,GlobalDef.empty).
    Proof.
    Admitted. *)


    Theorem T63_correctness_of_code_generation : 
        forall  (e  : Ω),
        fsl_pgrm_sem empty_env P (empty_env <|env ; vars := e|>)
        <-> 
        exists (e': Ω),
        gmp_pgrm_sem empty_env ⟦P⟧ (empty_env <|env ; vars := e'|>)
        /\ 
        (e ⊑ e')%env
        
    .
    Proof.        
        intros e. destruct P as [decls routines].  (* induction routines.
        - split.
            (* there must exist at least one function (main) *)
            + intros Hsem. exfalso. inversion Hsem. inversion H0 as (_ & Hsome & _). now subst fe.
            + intros [e' [Htrans  _]]. exfalso. destruct Htrans as [? _ ? ? _ ? Hmain _ _]. inversion Hmain as (_ & Hsome & _). now subst fe.

        - simpl in IHroutines. split.
            + intros Hsem. apply proj1 in IHroutines. inversion Hsem as [? ? ? ? Hev_decls fe (_ & Hmain & Hmain_args & Hmain_body) Hresf Hb_ev]. simpl in *. subst.
                eexists ?[e']. split.
               * econstructor. 
                    --   red.  constructor. simpl.  translate_routine. simpl. simpl. simp translate_routine. admit.
               * admit.
            + intros [e' [Hpsem Hrel]].  admit.
            *)


        split.
        - intros Hsem. inversion Hsem as [? ? ? ? Hev_decls fe (params & Hlength & Hmain & Hmain_args & Hmain_body) Hresf Hb_ev]. simpl in *. eexists.
    Admitted.
End Theorems.