From Coq Require Import ZArith.ZArith Strings.String.
From RAC Require Import Utils Environnement Macros Oracle Translation.
From RAC.Languages Require Import Syntax Semantics MiniFSL.Semantics.

Open Scope utils_scope.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.
Import FunctionalEnv FunctionalEnv.Domain.


Fixpoint flatten {S T}  (s: @_c_statement S T) : list (@_c_statement S T) := match s with
| Seq s1 s2 => flatten s1 ++ flatten s2
| Skip => nil
| _ => s::nil
end
.

Definition unflatten {S T}  : list (@_c_statement S T) -> @_c_statement S T := fun l =>
    List.fold_left (fun new_s  s => Seq new_s s) l Skip
.

Fact flatten_noseq_noskip {S T} s : List.Forall (fun i => i <> Skip /\ forall s1 s2, i <> @Seq S T s1 s2) (@flatten S T s).
Admitted.

Fact flatten_unflatten {S T} {ext_exp} {ext_stmt} {ext_stmt_vars} : forall f e e' s, 
    @generic_stmt_sem S T ext_exp ext_stmt ext_stmt_vars f e s e' ->
    @generic_stmt_sem S T ext_exp ext_stmt ext_stmt_vars f e (unflatten (flatten s)) e.
Admitted.

Lemma flatten_unique {S T} {ext_exp} {ext_stmt} {ext_stmt_vars} : forall s s' f e e', 
    flatten s = flatten s' ->
    @generic_stmt_sem S T ext_exp ext_stmt ext_stmt_vars f e s e' ->
    @generic_stmt_sem S T ext_exp ext_stmt ext_stmt_vars f e s' e'.
Proof.
    assert (Hcon_nil_not : forall X (x :X) a b, x :: nil <> a ++ b). {
        intros X x a b H. pose proof (List.nil_cons ). destruct b. simpl in H. admit. admit.
    }
    assert (Hnil: forall s f e, flatten s = nil <-> @generic_stmt_sem S T ext_exp ext_stmt ext_stmt_vars f e s e) by admit.
    assert (Hsmth: forall s s' f e e',  
                s :: nil = flatten s' -> 
                @generic_stmt_sem S T ext_exp ext_stmt ext_stmt_vars f e s e' ->
                @generic_stmt_sem S T ext_exp ext_stmt ext_stmt_vars f e s' e'
        ) by admit.

    intros s. induction s; intros  s' f  env env' Hflat Hsem ; simpl in Hflat.
    - inversion Hsem.  destruct s'; subst; try discriminate.
        + assumption.
        + assert (flatten s'1 = nil /\ flatten s'2 = nil) as [Hs'1 Hs'2] by admit.
            apply (Hnil _ f env') in Hs'2, Hs'1. now apply S_Seq with env'.
    - now apply Hsmth with (f:=f) (e:=env)  (e':=env') in Hflat.
    - now apply Hsmth with (f:=f) (e:=env)  (e':=env') in Hflat.
    - now apply Hsmth with (f:=f) (e:=env)  (e':=env') in Hflat.
    - subst. destruct (flatten s1) eqn:s1Eqn.
        + simpl in Hflat.  specialize (IHs2 <{s'}> f env env'). apply IHs2 ; [assumption|]. clear IHs2. 
            apply (Hnil _ f env) in s1Eqn. inversion Hsem; subst. admit.
        + admit.
Admitted.


(* Compute (flatten  (Seq (Seq (Assign "x" 1) (Assign "x" 2)) (Assign "x" 3))).
Compute (flatten  (Seq (Assign "x" 1) (Seq  (Assign "x" 2) (Assign "x" 3)))).
Compute flatten ((Seq (Seq (Assign "x" 1) (Assign "x" 2)) (Seq (Assign "x" 3) (Assign "x" 4)))). *)



(* [between left x right s] means [x] is between [left] and [right] inside [s] *)

Inductive between : gmp_statement -> gmp_statement -> gmp_statement -> gmp_statement ->  Prop :=
| Between_base : forall s1 s s2 s_whole, 
    flatten s_whole = flatten s1 ++ flatten s ++ flatten s2 -> 
    between s1 s s2 s_whole
| Between_add_l s1 s_whole : forall s1' s s2 s_whole',
    between s1 s s2 s_whole ->
    flatten s_whole' = flatten s1'++ flatten s_whole ->
    between s1' s s2 s_whole'

| Between_add_r s2 s_whole : forall s1 s  s2' s_whole',
    between s1 s s2 s_whole ->
    flatten s_whole' = flatten s_whole ++ flatten s2' ->
    between s1 s s2' s_whole' 
.

(* Goal forall s1 s2 s3 s4, between s1 s2 s4  (Seq (Seq s1 (Seq s2 s3)) s4).
Proof.
    intros. eapply (Between_add_r s3 (Seq s1 (Seq s2 s3))).
    - now constructor.
    - auto.
Qed.

Goal forall s1 s2 s3 s4, between s1 s2 s4  (Seq s1 (Seq s2 (Seq s3 s4))).
Proof.
    intros. eapply (Between_add_r s3 (Seq s1 (Seq s2 s3))).
    - now constructor.
    - simpl. now repeat rewrite <- List.app_assoc.
Qed.

Goal forall s1 s2 s3 s4, between s1 s3 s4  (Seq s1 (Seq s2 (Seq s3 s4))).
Proof.
    intros. eapply (Between_add_l s2 <{s2;s3;s4}>).
    - now constructor. 
    - simpl. now repeat rewrite <- List.app_assoc.
Qed.


Goal forall s1 s2 s3 s4, between s1 s2 s4  (Seq (Seq s1 s2) (Seq s3 s4)).
    intros. eapply (Between_add_r s3 (Seq (Seq s1 s2) s3)).
    - constructor. simpl. now rewrite <- List.app_assoc.
    - simpl. now repeat rewrite <- List.app_assoc.  
Qed. *)


Definition In_stmt {S T} (s s' : @_c_statement S T) : Prop := List.In s (flatten s').


Definition Forall_routines {F S T } (pgrm : @_c_program F S T) 
    (PFuns : @_c_decl T * -> @_c_decl T * -> @_c_statement S T  -> Prop)
    (* (PLFun : fsl_statement -> Prop)
    (PPred : fsl_statement -> Prop) *)
     : Prop :=
    List.Forall (fun f => match f with
        | PFun _ _ args decls body => PFuns args decls body
        (* | F_Ext (LFun _ _ _ _) => True
        | F_Ext (Predicate _ _ _) => True *)
        | _ => True
        end
    ) (snd pgrm)
.


(* 
    well_formed_program :
    - all variables declared before usage
    - all functions defined before called
    - well typed
*)
Definition well_formed_pgrm (P : fsl_pgrm) (env : Env) (fenv: @fenv _fsl_statement Empty_set) := 
    Forall_routines P ( fun args decls b =>
        (* all used variables are declared *)
        (forall v, List.In v (fsl_stmt_vars b) -> v ∈ env) /\ 
        (* all functions are defined before being called *)
        (forall rvar fname args, 
            @In_stmt _fsl_statement Empty_set (FCall rvar fname args) b -> 
            fname ∈ fenv.(funs)
        
        ) /\
        True (* fixme: well typed ? *)
    )
.



Module Theorems(Oracle:Oracle).
    
    Module T := Translation(Oracle).


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
        Forall_routines (T.translate_program P) ( fun _ _ b => 
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
        Forall_routines (T.translate_program P) ( fun _ _ b => 
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
        Forall_routines (T.translate_program P) ( fun _ _ b => 
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