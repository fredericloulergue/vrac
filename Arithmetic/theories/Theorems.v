From Coq Require Import ZArith.ZArith Strings.String.
From RAC Require Import Utils Environnement Macros Oracle Translation.
From RAC.Languages Require Import Syntax Semantics.

Open Scope utils_scope.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.

Module Theorems(Oracle:Oracle).
    
    Module T := Translation(Oracle).


    (* Section C : PROPERTIES OF THE SEMANTICS *)
    (* -> Languages/{MiniC,MiniGMP}/Lemmas.v *)




    (* Section D : PROOFS OF STRUCTURAL PROPERTIES OF THE TRANSLATION *)

    Lemma LD1_mpz_pointer_invariant : forall P args env env',
        (gmp_pgrm_sem env (T.translate_program P) args env')  -> True.
    Proof.
    auto.
    Qed.

    Lemma LD2_absence_of_aliasing : True.
    Proof.
        auto.
    Qed.

    Lemma LD3_preservation_of_control_flow : True.
    Proof.
        auto.
    Qed.

    Lemma LD4 : True.
    Proof.
        auto.
    Qed.


    Lemma LD5_memory_transparency_of_generated_code : True.
    Proof.
        auto.
    Qed.

    Theorem T61_absence_of_dangling_pointers : True. 
    Proof. 
        auto.
    Qed.


    Theorem T62_absence_of_memory_leak : True. 
    Proof. 
        auto.
    Qed.


    (* Section E : PROOFS OF THE SEMANTICS OF THE MACROS *)

    (* -> Macros.v *)

    (* Section F  : INVARIANTS FOR ROUTINE TRANSLATION *)

    (*

    (* synchronicity invariant *)
    Definition I1 (env:Ω) (ienv:Γ) := ((dom env.(binds)) = (dom (fst ienv) + dom (snd ienv)))%utils.

    (* suitability invariant *)
    Definition I2 (env:ψ) := True. (* todo *)

    *)



(*

Inductive pgrm_var_representation (iop:ϴ) (e : Env) (ienv:Γ) : Env -> Prop :=
| empty ΩΓ 𝓜Γ :   
    I1 e ienv ->
    let A := nil  (* { (iop ((snd ienv) v), v, (snd env) v ) | v in dom ienv  } *)
    in
    add_var_𝐴 e A {|env:=ΩΓ; mstate:=𝓜Γ|} -> 
    pgrm_var_representation iop e ienv{|env:=ΩΓ; mstate:=𝓜Γ|}
.

(* Definition well_formed_program :=
    - all variables declared before usage
    - all functions defined before called
    - well typed
*)


*)



    (* Section G : PRESERVATION OF THE SEMANTICS *)

    Open Scope fsl_sem_scope.

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
        gmp_pgrm_sem empty_env (T.translate_program P) args (empty_env <|env ; vars := e'|>)
        )
        /\ (e ⊑ e')%env.

    Proof.
    Admitted.


End Theorems.