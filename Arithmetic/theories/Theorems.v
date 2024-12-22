From Coq Require Import ZArith.ZArith Program.Equality.
From Coq.Strings Require Import String Ascii.
From Coq.Sets Require Import Ensembles Uniset.
From RAC Require Import Utils Environment.Facts Macros Oracle Translation Invariants.
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

    Module Inv := Invariants(Or).
    Import Inv.

    (* Section C : PROPERTIES OF THE SEMANTICS *)
    (* -> Languages/{MiniC,MiniGMP}/Lemmas.v *)

    Parameter P : fsl_pgrm.

    Parameter WellFormedProgram : 
        (* no duplicate global variable declaration *)
        SetoidList.NoDupA (fun '(C_Decl _ name1) '(C_Decl _ name2) => name1 = name2) (fst P)
        /\  
         (* no duplicate function declaration *)
        SetoidList.NoDupA (
            fun r1 r2 => match r1,r2 with
            | PFun _ name1 _ _ _,PFun _ name2 _ _ _ 
            | F_Ext (LFun _ name1 _ _), F_Ext (LFun _ name2 _ _) 
            | F_Ext (Predicate name1 _ _), F_Ext (Predicate name2 _ _)
            => name1 = name2
            | _,_ => False
            end
        ) (snd P)
        /\
        (* all used variables are declared and don't use comp var prefix *)
        StringSet.For_all (fun v => 
            (* (v ∈ env)%dom_ *)
            (is_comp_var v) = false
        ) (fsl_used_prgrm_vars P)
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
                In_stmt (Scope decls s) b -> 
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
                In_stmt (Scope decls s) b -> 
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

(*
    Inductive env_Γ (env: Env) (g:Γ) | : Env -> Prop :=  
    | env_Γ_intro (ens: 𝐴) (env':Env) : 
        I1 env g ->
        VarSet.For_all (fun '(t,v,z) => 
            Γdom g v /\ (* v ∈ dom Γ *)
            Some z = env.(binds) v /\  (* z is the logic value of v *)
            exists i,StringMap.find v (snd g) = Some i /\ 
            t = ϴ i (* infered type for v *)
        ) ens ->
        (env +++ ens) env' ->
        env_Γ env'
    .
*)


    Definition env_Γ (env env': Env) (g:Γ) : Prop :=  
        I1 env g ->
        exists (ens : 𝐴),
        (forall ty v z,
            Ensembles.In _ ens (ty,v,z) <->
                Γdom g v /\ (* v ∈ dom Γ *)
                Some z = env.(binds) v /\  (* z is the logic value of v *)
                exists i,StringMap.find v (snd g) = Some i /\ 
                ty = ty_from_interval i (* infered type for v *)
        ) /\
        (env +++ ens) env'
    .

    Definition env_Γ_t fenv (env env': Env) (g:Γ) (p:T.ψ) (t:ℨ) : Prop :=  
        forall env'',
        exists (ens : 𝐴),
        (forall ty v z,
            Ensembles.In _ ens (ty,v,z) <->
                List.In (v,ty) (TM.exec (translate_term fenv g p t)).(decls) /\
                (ty = T_Ext Mpz -> z = 0) /\
                (ty = C_Int -> exists u, z = u (*fixme: must be undef value *))  
        ) /\
        env_Γ env env'' g /\
        (env'' +++ ens) env'
    .

    Definition env_Γ_p fenv (env env': Env) (g:Γ) (p:T.ψ) (pred:𝔅) : Prop :=  
        forall env'',
        exists (ens : 𝐴),
        (forall ty v z,
            Ensembles.In _ ens (ty,v,z) <->
            List.In (v,ty) (TM.exec (translate_pred fenv g p pred)).(decls) /\
            (ty = T_Ext Mpz -> z = 0) /\
            (ty = C_Int -> exists u, z = u (*fixme: must be undef value *))  
        )  
        /\
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
                    forall cnt,
                    let result := fst (translate_term fenv g p t cnt)  in

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
            List.Forall (Γdom g) vargs -> True
            (* TM.exec (generate_function fe g p f)  *)
            (* let new_fenv : @fenv _fsl_statement Datatypes.Empty_set := 
            mk_fenv _ _ fe.(funs) fe.(procs) (StringMap.add result.(chunk) _ fe.(lfuns)) fe.(preds) in  *)
            (* suitable new_fenv g result.(chunk) f *)
        )
        /\
        (
            forall f body, StringMap.find f fe.(preds) = Some (vargs,body) ->
            List.Forall (Γdom g) vargs ->
            (* TM.exec (generate_function fe g p f)  *)
            (* let new_fenv : @fenv _fsl_statement Datatypes.Empty_set :=
             mk_fenv _ _ fe.(funs) fe.(procs) fe.(lfuns) (StringMap.add result.(chunk) _ fe.(preds)) in  *)
            (* suitable new_fenv g result.(chunk) f *)
            True
        )


    .
    Proof.
    {
        induction t; intros fenv e g p HI1 HI2 env_g Henvg env_gt Henvgt z'; split; intros Htsem ;
            specialize (Henvg HI1) as Henvgapp; destruct Henvgapp as (ens1 & Hens1 & Henvgapp);
            specialize (Henvgt env_g) as Henvgtapp; destruct Henvgtapp as (ens2 & Hens2 & _ & Henvgtapp).

        (* t is an integer *)
        -  clear LG1_semantics_of_term_translation LG3_semantics_of_function_generation LG2_semantics_of_predicate_translation.
            intros cnt.
            set ("_v" ++ string_of_nat cnt) as var.
            remember (translate_term fenv g p z cnt) as trans in *.
            inversion Htsem. subst z0 z'. remember (get_ty (T_Z z,snd g)) as ty. destruct ty; autorewrite with translate_fsl in Heqtrans; rewrite <- Heqty in *; cbn in Heqtrans; subst; simpl in *.
            + pose proof (Or.type_soundness _ (snd g) _ _  _  Htsem) as Hfit. inversion Hfit; [|congruence].  
                exists (env_gt <| env; vars ::= {{var\Def (VInt (z ⁱⁿᵗ H0))}} |> ).  repeat split.
                * (* v_gt + v0  subsumes env_g  *) admit.
                * subst. apply LE3_semantics_of_the_Z_assgn_macro_tint ; [easy|].
                    assert (Hv0 : env_gt var = Some (Def (VInt (MI.to_mi z H0)))). {
                        admit.
                    } now rewrite Hv0.
                * subst. simpl. epose proof (M_Int (env_gt <| env; vars ::= {{var \Def (VInt (z ⁱⁿᵗ H0))}} |> ) (C_Id var C_Int) (z ⁱⁿᵗ H0)). apply H1. 
                    ** easy.
                    ** simpl. constructor. apply p_map_same.
                * exists H0. subst. simpl. subst var. apply p_map_same.

            + exfalso. pose proof Or.ϴ_int_or_mpz as Hcontra. unfold get_ty in Heqty. specialize (Hcontra (oracle (T_Z z, snd g))). destruct Hcontra; congruence. 

            + destruct t.
                * exfalso. pose proof Or.ϴ_int_or_mpz as Hcontra. unfold get_ty in Heqty. specialize (Hcontra (oracle (T_Z z, snd g))). destruct Hcontra; congruence.
                * assert (H2: exists x, env_gt = (env_g <| env; vars ::= {{var\Def x}} |> <| mstate ::= {{x\Defined 0}} |>)) by admit.
                    destruct H2 as [l H2].
                    exists (env_gt <| mstate ::= {{l\Defined z}} |> ). repeat split.
                    -- subst. admit.
                    -- apply LE3_semantics_of_the_Z_assgn_macro_tmpz. subst. apply p_map_same.
                    -- subst. simpl. apply M_Mpz with l; auto ; apply p_map_same.
                    -- exists l. subst. simpl. split; apply p_map_same.

        - clear LG1_semantics_of_term_translation LG3_semantics_of_function_generation LG2_semantics_of_predicate_translation.
            assert (z = z'). {
                autorewrite with translate_fsl in Htsem. simpl in Htsem. specialize Htsem with 0%nat. destruct Htsem as (e' & H & H1). edestruct H1 as [_ (_ & H2)]. clear H1.
                destruct (get_ty (T_Z z, snd g)); simpl in Hens2; admit.
            }
            subst. apply S_T_Int.

        (* t is a program/logic variable *)
        - clear LG1_semantics_of_term_translation LG3_semantics_of_function_generation LG2_semantics_of_predicate_translation.
            intros cnt.
            remember (fst (translate_term fenv g p (T_Id name ty) cnt) ) as trans in *.
            inversion Htsem; apply type_soundness with (te:= snd g) in Htsem; subst ty name z'; autorewrite with translate_fsl in Heqtrans.
            (* logic variable *)
            + {
                remember (Logic.inspect (StringMap.find x (fst g))) as s. dependent destruction s. destruct x0; [|exfalso;admit (* HI1 *)]. destruct p0.
                simpl in Heqtrans. unfold TM.exec, TM.ret  in Heqtrans. simpl in Heqtrans. 
                assert (env_gt = env_g) by admit. subst env_gt.
                exists env_g. split.
                - easy.
                - intros fenv'. subst trans. simpl. split ;[constructor|]. unfold get_ty in Htsem. remember (oracle (T_Id x FSL_Integer, snd g)) as i' in *.  assert (i = i') by admit.
                    destruct ty_from_interval eqn:Zty; subst; inversion Htsem; split; unfold get_ty; rewrite Zty; subst.
                    + replace z with (MI.of_mi (exist _ z H)) by auto. apply M_Int ; [easy|]. simpl. constructor. admit.
                    + exists H. admit.
                    + eapply M_Mpz; [easy| |]; simpl; admit.
                    + admit.
            }

            (* program variable *)
            + {
                assert (env_gt = env_g) by admit. subst.
                exists env_g.  repeat split.
                - easy.
                - constructor.
                - simpl. constructor; auto. simpl. constructor. admit.
                - rewrite Or.get_ty_prog_var in *. destruct x as [x irx]. simpl in *. exists irx. admit.   
            }


        - clear LG1_semantics_of_term_translation LG3_semantics_of_function_generation LG2_semantics_of_predicate_translation. admit.


        (* t is the application of an operation *)
        - clear LG1_semantics_of_term_translation LG3_semantics_of_function_generation LG2_semantics_of_predicate_translation.
            intros cnt.
            inversion Htsem. subst.
            remember (fst (translate_term fenv g p (T_BinOp t1 op t2) cnt)) as trans in *.
            autorewrite with translate_fsl in Heqtrans. unfold TM.bind in Heqtrans. simpl in Heqtrans.
            remember (translate_fsl tr_term fenv g p t1 (S (S (S (S cnt))))) as trans1. destruct trans1 as [t1_res n] eqn:trans1Eqn.
            remember (translate_fsl tr_term fenv g t1_res.(tr).(tenv) t2 n) as trans2.  destruct trans2 as [t2_res n'] eqn:Trans2Eqn.
            simpl in Heqtrans.
            destruct t1_res.(res) eqn:T1res. 
            destruct t2_res.(res) eqn:T2res. simpl.

            assert (Henv_gt1 : exists env_gt1, env_Γ_t fenv e env_gt1 g p t1) by admit. destruct Henv_gt1 as [env_gt1 Henvgt1].
            assert (Henv_gt2 :  exists env_gt2, env_Γ_t fenv e env_gt2 g t1_res.(tr).(tenv) t2) by admit. destruct Henv_gt2 as [env_gt2 Henvgt2].
            
            assert (Hrel_t1: (env_gt1 ⊑ env_gt)%envmem) by admit. destruct Hrel_t1 as [t1sub Hrel_t1].
            assert (Hrel_t2 : (env_gt2 ⊑ env_gt)%envmem) by admit. destruct Hrel_t2 as [t2sub Hrel_t2].

            assert (Hrel2 : (env_gt2 ⊑ env_gt)%envmem) by admit.
            assert (Hdom1 : (dom env_gt1.(env) ∩ dom env_gt2.(env)  = dom env_g.(env))%dom_) by admit.
            assert (Hdom2 : (dom env_gt1.(mstate) ∩ dom env_gt2.(mstate)  = dom env_g.(mstate))%dom_) by admit.
        

            specialize (IHt1 fenv e g p HI1 HI2 env_g Henvg env_gt1 Henvgt1 z).
            assert (HI2' : I2 t1_res.(tr).(tenv) g fenv) by admit.
            specialize (IHt2 fenv e g t1_res.(tr).(tenv) HI1 HI2' env_g Henvg env_gt2 Henvgt2 z'0).
            
            apply IHt1  with (cnt:=(S (S (S (S cnt))))) in H2 as [env't1 [Hrelt1 Ht1]]. clear IHt1.
            apply IHt2 with (cnt:=n) in H4 as [env't2 [Hrelt2 Ht2]]. clear IHt2.

            eexists ?[env]. repeat split.
            2: {
                assert (Henv' : exists env', 
                (env_gt |= t1_res.(tr).(chunk) => env')%gmpssem fenv' /\ 
                (env_g ⊑ env')%envmem /\
                (env' |= C_Id (fst t1_res.(res)) (snd t1_res.(res)) ⇝ z)
                ). {
                    specialize (Ht1 fenv') as (Hsemt1 & Hmt1 & Hzt1).
                    simpl in Hsemt1.
                    pose proof LC21_weakening_of_gmp_statement_semantics (fe:=fenv') as LC21.
                    unfold translate_term in Hsemt1. rewrite <- Heqtrans1 in Hsemt1.

                    specialize (LC21 env_gt1 t1_res.(tr).(chunk) env't1 Hsemt1 env_gt t1sub Hrel_t1).
                    destruct LC21 as (env''_t1 & Hrel''_t1 & Hsem''_t1). exists env''_t1. repeat split.
                    - assumption.
                    - transitivity  env't1; [assumption|]. now exists t1sub.
                    - admit.
                } destruct Henv' as (env' & Hsemt1 & Henvt1 & Hmt1). 

                assert (Henv'' : exists env'', 
                    (env' |= t2_res.(tr).(chunk) => env'')%gmpssem fenv' /\
                    (env_g ⊑ env'')%envmem /\
                    (env' |= C_Id (fst t2_res.(res)) (snd t2_res.(res)) ⇝ z'0)
                ). {
                    specialize (Ht2 fenv') as (Hsemt2 & Hmt2 & Hzt2).
                    pose proof LC21_weakening_of_gmp_statement_semantics (fe:=fenv') as LC21.
                    unfold translate_term in Hsemt2. rewrite <- Heqtrans2 in Hsemt2.
                    assert (Hrel't2 : env_mem_partial_order env_gt2 env' t2sub) by admit.
                    specialize (LC21 env_gt2 t2_res.(tr).(chunk) env't2 Hsemt2 env' t2sub Hrel't2).
                    destruct LC21 as (env''_t2 & Hrel''_t2 & Hsem''_t2). exists env''_t2. repeat split.
                    - assumption.
                    - transitivity env't2; [assumption|]. now exists t2sub.
                    - admit.
                }  destruct Henv'' as (env'' & Hsemt2 & Henvt2 & Hmt2).               

                assert (Henv'' :  env'' |= C_Id (fst t1_res.(res)) (snd t1_res.(res)) ⇝ z). {
                    pose proof LC22_weakening_of_gmp_statement_semantics (fe:=fenv') as LC22.
                    (* t1.res not in dom env_g_t2 -> use C22 *)
                    admit.
                } simpl in Heqtrans.
                remember (get_ty (T_BinOp t1 op t2, snd g)) as ty in *.
                destruct g0.
                - destruct g1. 
                    + destruct ty; autorewrite with translate_fsl in Heqtrans; simpl in Heqtrans; subst; simpl.
                        * econstructor ;  admit.
                        * exfalso. admit.
                        * destruct t eqn:Teq.
                            -- exfalso. admit. 
                            -- eapply S_Seq.
                                ++ admit.
                                ++ eapply S_Seq.
                                    ** admit.
                                    ** eapply S_Seq.
                                        --- admit.
                                        --- eapply S_Seq.
                                            +++ admit.
                                            +++ constructor. admit.

                    + exfalso. admit.
                    + destruct ty; autorewrite with translate_fsl in Heqtrans; simpl in Heqtrans; subst; simpl.
                        * admit.
                        * admit.
                        * admit.

                - exfalso. admit.
                - admit.
            }
            + admit.
            + admit.
            + admit.

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
        pose (tr t <| chunk := Scope (DECLS (decls t)) instrs |> ) as assert_res.
        pose (build_rac_fenv (glob (tr t))) as fenv'.


        split.

        - intros Hptrue. destruct H as [H _]. specialize (H Hptrue).
            destruct H as [env' [Hrel Hsem]]. specialize (Hsem fenv'). 
            exists env. simpl. 
            (*
            pose proof (S_Scope (build_rac_fenv (glob (tr t))) (env <| mstate := ⊥ |>) (DECLS (decls t)) instrs env_g env') as Scope. 
            simpl in Scope. 
            assert (env'.(mstate) = ⊥) by admit.   (* T62_absence_of_memory_leak *) rewrite H in Scope.
            
            constructor. subst scope instrs var assert_res. apply Scope; clear Scope. *)
            + admit.
        
        - intros Htrans. destruct H as [_ H]. apply H. clear H. destruct Htrans as [env' Henv]. exists (mkEnv env' ⊥). split.
            + admit.
            + intros. split.
                * admit.
                * exists oneinRange. simpl. admit.
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
