From Coq Require Import ZArith.ZArith Strings.String.
From RAC Require Import Utils Environnement Macros Oracle Translation.
From RAC.Languages Require Import Syntax Semantics MiniFSL.Semantics.

#[local] Open Scope utils_scope.
#[local] Open Scope list.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.
Import FunctionalEnv FunctionalEnv.Domain.


Module Theorems(O:Oracle).
    #[local] Open Scope mini_c_scope.
    #[local] Open Scope mini_gmp_scope.

    Module T := Translation(O).
    Import T O.

    (* Section C : PROPERTIES OF THE SEMANTICS *)
    (* -> Languages/{MiniC,MiniGMP}/Lemmas.v *)


    (* Section D : PROOFS OF STRUCTURAL PROPERTIES OF THE TRANSLATION *)


    (* `if the generated program has a semantic [...]'  but no semantic given for a program   *)
    Lemma LD1_mpz_pointer_invariant : forall P fenv t_fenv env,
        well_formed_pgrm  P env fenv ->
        Forall_routines (T.translate_program P) ( fun _ _ b => 
            forall (renv renv' : Env),
            forall v, type_of_value (renv v) = Some (T_Ext Mpz) ->
            forall s, between <( init(v) )> s <( cl(v) )> b -> 
            (renv |= s => renv')%gmpssem t_fenv ->
            renv v = renv' v
        )
    .
    Proof.
        intros P args env env' Hwf. unfold Forall_routines. apply List.Forall_forall. intros R Hr. destruct R eqn:REqn;[|trivial].
        intros renv renv' v Hv stmt Hstmt Hsem. 
        (* unroll translation... *)
        destruct P as [Pdecls Pfuns]. destruct Pfuns eqn:PfunsEqn; simpl in Hr; [easy|]. 
        destruct Pdecls eqn:PdeclsEqn; simpl in Hr. admit.
    Admitted.

    Lemma LD2_absence_of_aliasing : forall P fenv t_fenv env,
        well_formed_pgrm  P env fenv ->
        Forall_routines (T.translate_program P) ( fun _ _ b => 
            forall s (renv renv' : Env),
            (renv |= s => renv')%gmpssem t_fenv ->
            forall v (l:location), renv' v = Some (Def (VMpz l)) ->
            forall v' (l':location), v' <> v /\ renv' v' =  Some (Def (VMpz l')) ->
            l <> l'
        )
    .
    Proof.
        intros P args env env' Hwf. unfold Forall_routines. apply List.Forall_forall. intros R Hr. destruct R eqn:REqn;[|trivial].
        intros renv renv' v Hv stmt Hstmt Hsem. 
        (* unroll translation... *)
        destruct P as [Pdecls Pfuns]. destruct Pfuns eqn:PfunsEqn; simpl in Hr; [easy|]. 
        destruct Pdecls eqn:PdeclsEqn; simpl in Hr. admit.
    Admitted.


    Lemma LD3_preservation_of_control_flow : forall P fenv env,
        well_formed_pgrm  P env fenv ->
        Forall_routines (translate_program P) ( fun _ _ b => 
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
        Forall_routines (translate_program P) ( fun _ _ b => 
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
        Forall_routines (translate_program P) ( fun _ _ b => 
            forall s (renv renv' : Env),
            (renv |= s => renv')%gmpssem t_fenv ->
            forall (l:location), renv'.(mstate) l <> None <->  exists! x, eq (renv' x) (Some (Def (VMpz l)))
        ). 
    Proof. 
    Admitted.   

    Theorem T62_absence_of_memory_leak :  forall P args fenv env env',
        well_formed_pgrm  P env fenv ->
        gmp_pgrm_sem env (T.translate_program P) args env' ->
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


    Theorem T64_correctness_of_code_generation :  forall (P:fsl_pgrm) args,

        exists  (e  e' : Ω),
        (fsl_pgrm_sem empty_env P args (empty_env <|env ; vars := e|>)
        <-> 
        gmp_pgrm_sem empty_env (translate_program P) args (empty_env <|env ; vars := e'|>)
        )
        /\ (e ⊑ e')%env.

    Proof.
    Admitted.


End Theorems.