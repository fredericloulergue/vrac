From Coq Require Import ZArith.ZArith Strings.String Ensembles.
From RAC Require Import Utils Environnement Macros Oracle Translation Invariants.
From RAC.Languages Require Import Syntax Semantics MiniFSL.Semantics.

#[local] Open Scope utils_scope.
#[local] Open Scope list.
#[local] Open Scope Z_scope.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.
Import FunctionalEnv FunctionalEnv.Domain.


Module Theorems(O:Oracle).
    #[local] Open Scope mini_c_scope.
    #[local] Open Scope mini_gmp_scope.

    Module I := Invariants(O).
    Import I.

    (* Section C : PROPERTIES OF THE SEMANTICS *)
    (* -> Languages/{MiniC,MiniGMP}/Lemmas.v *)


    (* Section D : PROOFS OF STRUCTURAL PROPERTIES OF THE TRANSLATION *)


    (* `if the generated program has a semantic [...]'  but no semantic given for a program   *)
    Lemma LD1_mpz_pointer_invariant : forall P fenv t_fenv env,
        well_formed_pgrm P env fenv ->
        forall P', T.translate_program P = Some P' ->
        Forall_routines P' ( fun _ _ b => 
            forall (renv renv' : Env),
            forall v, type_of_value (renv v) = Some (T_Ext Mpz) ->
            forall s, between <( init(v) )> s <( cl(v) )> b -> 
            (renv |= s => renv')%gmpssem t_fenv ->
            renv v = renv' v
        )
    .
    Proof.
        intros P args env env' Hwf. intros. unfold Forall_routines. apply List.Forall_forall. intros R Hr. destruct R eqn:REqn;[|trivial].
        intros renv renv' v Hv stmt Hstmt Hsem. 
        (* unroll translation... *)
        admit.
    Admitted.

    Lemma LD2_absence_of_aliasing : forall P fenv t_fenv env,
        well_formed_pgrm  P env fenv ->
        forall P', T.translate_program P = Some P' ->
        Forall_routines P' ( fun _ _ b => 
            forall s (renv renv' : Env),
            (renv |= s => renv')%gmpssem t_fenv ->
            forall v (l:location), renv' v = Some (Def (VMpz l)) ->
            forall v' (l':location), v' <> v /\ renv' v' =  Some (Def (VMpz l')) ->
            l <> l'
        )
    .
    Proof.
        intros P fenv args env env' P' Hwf. unfold Forall_routines. apply List.Forall_forall. intros R Hr. destruct R eqn:REqn;[|trivial].
        intros renv renv' v Hv stmt Hstmt Hsem. 
        (* unroll translation... *)
        admit.
    Admitted.


    Lemma LD3_preservation_of_control_flow : forall P fenv env,
        well_formed_pgrm  P env fenv ->
        forall P', T.translate_program P = Some P' ->
        Forall_routines P' ( fun _ _ b => 
            forall decls s,
            In_stmt (S_Ext (GMP_Scope decls s)) b -> 
            (* passes through: how to represent control flow ?  *)
            True
        )
    .
    Admitted.

    Lemma LD4 : forall P env fenv,
        well_formed_pgrm  P env fenv ->
        (* translate_predicate ... *)
        True.
    Proof.
    Admitted.


    Lemma LD5_memory_transparency_of_generated_code : forall P fenv env,
        well_formed_pgrm  P env fenv ->
        forall P', T.translate_program P = Some P' ->
        Forall_routines P' ( fun _ _ b => 
            forall decls s,
            In_stmt (S_Ext (GMP_Scope decls s)) b -> 
            (* todo: add decls tec *)
            True
        )
    .
    Proof.
    Admitted.

    Theorem T61_absence_of_dangling_pointers : forall P fenv t_fenv env,
        well_formed_pgrm  P env fenv ->
        forall P', T.translate_program P = Some P' ->
        Forall_routines P' ( fun _ _ b => 
            forall s (renv renv' : Env),
            (renv |= s => renv')%gmpssem t_fenv ->
            forall (l:location), renv'.(mstate) l <> None <->  exists! x, eq (renv' x) (Some (Def (VMpz l)))
        ). 
    Proof. 
    Admitted.   

    Theorem T62_absence_of_memory_leak :  forall P args fenv env env',
        well_formed_pgrm  P env fenv ->
        forall P', T.translate_program P = Some P' ->
        gmp_pgrm_sem env P' args env' ->
        env'.(mstate) = ⊥
    .
    Proof. 
    Admitted.


    (* Section E : PROOFS OF THE SEMANTICS OF THE MACROS *)

    (* -> Macros.v *)

    (* Section F  : INVARIANTS FOR ROUTINE TRANSLATION *)

    (* -> Invariants.v *)



    (* Section G : PRESERVATION OF THE SEMANTICS *)
    #[local] Open Scope fsl_sem_scope.


    Inductive env_Γ (env: Env) (g:Γ) : Env -> Prop :=  
    | env_Γ_Cons env' (ens : 𝐴) : 
        (
            forall t v z, 
                Ensembles.In _ ens (t,v,z) 
                <-> 
                Γdom g v /\
                Some z = env.(binds) v /\
                exists i,
                StringMap.find v (snd g) = Some i /\
                t = ϴ i
        ) ->
        (env +++ ens) env' ->
        env_Γ env g env'
    .


    Inductive env_Γ_t fenv (env: Env) (g:Γ) (p:T.ψ) (t:ℨ) : Env -> Prop :=  
    | env_Γ_t_Cons env' env'' (ens : 𝐴) : 
        (
            forall ty v z  fuel tr,  
                Ensembles.In _ ens (ty,v,z) 
                <-> 
                TM.exec (translate_term fenv (fst g) (snd g) p t fuel) = Some tr /\
                List.In (v,ty) tr.(decls)
                /\
                z = 0 <-> ty = T_Ext Mpz 
                /\
                (exists u, z = u (*fixme: must be undef value *) )%type <-> ty = C_Int            
        ) ->
        env_Γ env g env' ->
        (env' +++ ens) env'' ->
        env_Γ_t fenv env g p t env''
    .


    Lemma LG1_semantics_of_term_translation : 
        forall fenv t (env:Env) g (p:T.ψ) fuel, 
            I1 env g ->
            I2 p g fenv ->
            forall env_gt, 
                env_Γ_t fenv env g p t env_gt ->

            (forall z fenv', 

                (env |= t => z)%fsltsem fenv
                <-> 
                (exists env', 
                    forall result,
                    TM.exec (translate_term fenv (fst g) (snd g) p t fuel) = Some result -> 
                    (env_gt ⊑ env')%envmem 
                    /\
                    (env_gt |= result.(tr).(chunk) =>  env')%gmpssem fenv'
                    /\
                    env' |= C_Id (fst result.(res)) (snd result.(res)) ⇝ z
                    /\
                    (* more specifically ... *)
                    (match 𝒯 t (snd g) with
                    | C_Int =>  
                        exists irz, (env'.(vars) (fst (result.(res))) = Some (Def (VInt (z ⁱⁿᵗ irz))))%type
                    | T_Ext Mpz => 
                        exists l, (env'.(vars) (fst result.(res)) = Some (Def (VMpz (Some l))))%type
                        /\
                        env'.(mstate) l = Some (Defined z)
                    | _ => False
                    end)
                )
                
            ) 
    .
    Proof.
    Admitted.

    (*
    Lemma LG1_semantics_of_term_translation : 
        True
    with LG2_semantics_of_predicate_translation : 
        True
    with LG3 : 
        True.
    Proof. 
        auto.
    Qed.
    *)


    Theorem TG4_soundness_of_assertion_translation : True.
    Proof. 
        auto.
    Qed.

    Theorem TG5_soundness_of_assertion_translation : True.
    Proof. 
        auto.
    Qed.



    Theorem T63_correctness_of_code_generation :  forall (P:fsl_pgrm) args,
        forall P', T.translate_program P = Some P' ->
        exists  (e  e' : Ω),
        (fsl_pgrm_sem empty_env P args (empty_env <|env ; vars := e|>)
        <-> 
        gmp_pgrm_sem empty_env P' args (empty_env <|env ; vars := e'|>)
        )
        /\ (e ⊑ e')%env.

    Proof.
    Admitted.


End Theorems.