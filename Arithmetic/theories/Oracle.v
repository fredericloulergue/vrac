From Coq Require Import ZArith.ZArith Strings.String.
From Coq.Structures Require Import Orders OrdersEx.
From Coq.Sets Require Import Ensembles Finite_sets.
From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax Semantics.



Module Type Oracle.

    Definition interval : Type := Z ⨉ Z. (* interval *) (* using 𝐼 messes up vscoq *)

    Definition Γᵢ : Type :=  StringMap.t interval. (* typing env mapping logic binders to intervals *)

    Parameter get_Γᵢ : fsl_pgrm -> Γᵢ. (* static analysis *)

    Parameter oracle : ℨ ⨉ Γᵢ -> interval. (* oracle *) (* using 𝓘 messes up vscoq *)

    Parameter ty_from_interval :  interval -> 𝔗. (* using ϴ messes up vscoq *)

    Parameter ϴ_int_or_mpz : forall i, ty_from_interval i = C_Int \/  ty_from_interval i = T_Ext Mpz.

    Definition get_ty : ℨ ⨉ Γᵢ -> 𝔗 := fun x => (ty_from_interval (oracle x)). (* using 𝒯 messes up vscoq *)


    (* a program variable can't be an Mpz *)
    Parameter get_ty_prog_var : forall x i, get_ty (T_Id x FSL_Int, i) = C_Int.

    Parameter ty_funcall_is_ty_body: 
        forall (f : fsl_prog_fenv) fname xargs (targs:list ℨ) (iargs:list interval) b, 
        StringMap.find fname f.(lfuns) = Some (xargs,b) ->
        forall te,
        List.Forall2 (fun e => eq (oracle (e,te))) targs iargs ->
                    get_ty (T_Call fname targs, te) = get_ty (b,StringMap.add_all xargs iargs StringMap.empty).


    (* a term always fits in an mpz and only fits in a machine integer if it is in range *)
    Inductive fits (z:Z) : 𝔗 -> Prop := 
    | InInt : MI.inRange z -> fits z C_Int
    | InMpz : fits z (T_Ext Mpz)
    .


    Parameter type_soundness : forall env te f t z, 
        fsl_term_sem f env t z -> fits z (get_ty (t,te)).


    (* 
        - assuming "getting typed" means having a type inferred by the oracle 
        - `ty_funcall_is_ty_body` tells this is the same as typing the body with infered argument intervals
     *)
    Parameter convergence_of_lfuns_ty : 
        forall fname (targs:list ℨ) (iargs:list interval), 
        forall (typing_envs : Ensemble Γᵢ)  (fe:Γᵢ), Ensembles.In Γᵢ typing_envs fe ->
        (exists ty te, get_ty (T_Call fname targs, te) = ty) -> 
        Finite_sets.Finite _ typing_envs
    .


    (* fixme: there is also convergence for predicates but the oracle is for terms, not predicates, what to do? *)
    (* Parameter convergence_of_pred_ty : 
    forall S (f : fsl_prog_fenv) pname xargs (targs:list ℨ) (iargs:list 𝐼) b, 
    f.(preds) pname = Some (xargs,b) ->
    forall (typing_envs : Ensemble Γᵢ)  (fe:Γᵢ), Ensembles.In Γᵢ typing_envs fe ->
    (exists ty te, eq (get_ty  (P_Call pname targs) te) ty) -> 
    Finite_sets.Finite _ typing_envs
    . *)


End Oracle.