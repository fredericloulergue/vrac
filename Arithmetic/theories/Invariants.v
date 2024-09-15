From Coq Require Import ZArith.
From RecordUpdate Require Import RecordUpdate.
From RAC Require Import Utils Oracle Translation Environnement.
From RAC.Languages Require Import Syntax Semantics.


#[local] Open Scope Z_scope.
#[local] Open Scope list_scope.
#[local] Open Scope utils_scope.


Module Invariants(O: Oracle).    
    Import RecordSetNotations.

    Module T := Translation(O).
    Import FunctionalEnv FunctionalEnv.Domain.
    Export O T.
    
    (* Section F  : INVARIANTS FOR ROUTINE TRANSLATION *)

    Definition in_interval (tenv:Γᵢ) x (n:Z) i :=
        StringMap.find x tenv = Some i /\
        fst i  <= n <= snd i.



    Definition Γdom (g:Γ) := (dom (fst g) + dom (fun k => StringMap.find k (snd g)))%utils.
    
    (* synchronicity invariant *)
    Definition I1 (env:Ω) (ienv:Γ) := 
        dom env.(binds) = Γdom ienv
        /\
        forall x, (Γdom ienv) x -> 
        exists y, env.(binds) x = Some y /\          
        exists i, in_interval (snd ienv) x y i
    .



    (* ϕ is suitable to represent f in Γ  *)
    Inductive suitable (fenv: @fenv _fsl_statement Empty_set) (tenv : Γ) (ϕ f:id) : Prop := 
    | Suite_L (z:Z) :
        forall vargs b zargs iargs xargs,
        
        fenv.(lfuns) f = Some (vargs,b)  ->
        List.length zargs = List.length vargs ->
        List.length zargs = List.length iargs ->
        List.Forall2 (fun v zi => in_interval (snd tenv) v (fst zi) (snd zi)) vargs (List.combine zargs iargs) ->

        match  𝒯 b (snd tenv) with
        | C_Int =>
            forall s envᶠ irz,
            fenv.(funs) ϕ = Some (xargs,s) ->
            List.length zargs = List.length xargs ->

            let new := List.map (fun xzv => let '(i,x,z) := xzv in (ϴ i,x,z))
                                (List.combine (List.combine iargs xargs) zargs) 
            in
            add_z_vars empty_env (list_to_ensemble new) envᶠ ->

            (empty_env <| env;binds ::= p_map_addall_back vargs zargs |> |= b => z)%fsltsem fenv 
            <->
            exists Ω, 
                    Ω.(vars) res_f = Some (Def (VInt (z ⁱⁿᵗ irz)))
                /\ ( envᶠ |= s => envᶠ <| env; vars := Ω |>)%fslsem fenv
        | T_Ext Mpz =>
            forall s x1 v0 envᶠ,
            fenv.(procs) ϕ = Some (x1::xargs,s) ->
            List.length zargs = List.length xargs ->

            (* fixme: is v0 fresh ? constraints ? *)
            (*fixme: says x_i+1 but x only goes up to n  .... *)
            let new := (T_Ext Mpz, v0, 0)::List.map (fun xzv => let '(i,x,z) := xzv in (ϴ i,x,z)) 
                                                    (List.combine (List.combine iargs xargs) zargs)
            in
            add_z_vars empty_env (list_to_ensemble new) envᶠ ->
            (
                (empty_env <| env;binds ::= p_map_addall_back vargs zargs |> |= b => z)%fsltsem fenv 
                /\ (z < Int.m_int \/ Int.M_int < z)
            )
            <->
                exists Ω l,
                envᶠ x1 = Some (Def (VMpz (Some l)))
                /\ ( envᶠ |= s => envᶠ <| env; vars := Ω |> <| mstate ::= {{ l \ Defined z}}|>)%fslsem fenv

        | _ => False
        end 
        -> suitable fenv tenv ϕ f 


    | Suite_P (z:𝔹) :
        forall vargs b zargs iargs xargs,
        
        fenv.(preds) f = Some (vargs,b)  ->
        List.length zargs = List.length vargs ->
        List.length zargs = List.length iargs ->
        List.Forall2 (fun v zi => in_interval (snd tenv) v (fst zi) (snd zi)) vargs (List.combine zargs iargs) ->

        (*fixme: oracle only infers for a term, not a predicate, assume it is always int for now *)
            forall s envᶠ irz,
            fenv.(funs) ϕ = Some (xargs,s) ->
            List.length zargs = List.length xargs ->

            let new := List.map (fun xzv => let '(i,x,z) := xzv in (ϴ i,x,z))
                                (List.combine (List.combine iargs xargs) zargs) 
            in
            add_z_vars empty_env (list_to_ensemble new) envᶠ ->
            
            (empty_env <| env;binds ::= p_map_addall_back vargs zargs |> |= b => z)%fslpsem fenv 
            <->
            (exists Ω, 
                (forall resf, (* fixme: get actual resf *) 
                    Ω.(vars) resf = Some (Def (VInt ((𝔹_to_Z z) ⁱⁿᵗ irz)))) 
                /\ ( envᶠ |= s => envᶠ <| env; vars := Ω |>)%fslsem fenv)

            -> suitable fenv tenv ϕ f 
    .


    (* suitability invariant *)
    Definition I2 (env:ψ) (inf:Γ) fenv := 
        forall f, 
            GlobalDef.mem (f, snd inf) env = true ->
            exists ϕ, GlobalDef.find (f, snd inf) env = Some ϕ  /\ suitable fenv inf ϕ f.

End Invariants.
