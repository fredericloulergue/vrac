From Coq Require Import ZArith.ZArith Strings.String Sets.Ensembles Sets.Finite_sets Orders Structures.OrdersEx.
From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax Semantics.



Module Type Oracle.

    Definition 𝐼 : Type := Z ⨉ Z. (* interval *)

    Definition Γᵢ : Type :=  StringMap.t 𝐼. (* typing env mapping logic binders to intervals *)

    Parameter get_Γᵢ : fsl_pgrm -> Γᵢ. (* static analysis *)

    Parameter 𝓘 : ℨ -> Γᵢ -> 𝐼. (* oracle *)

    Parameter ϴ :  𝐼 -> 𝔗.

    Definition 𝒯 : ℨ -> Γᵢ -> 𝔗 := fun t τᵢ =>  ϴ (𝓘 t τᵢ).

    Parameter ty_funcall_is_ty_body: 
        forall S (f : @fenv _fsl_statement S) fname xargs (targs:list ℨ) (iargs:list 𝐼) b, 
        f.(lfuns) fname = Some (xargs,b) ->
        forall te,
        List.Forall2 (fun e => eq (𝓘 e te)) targs iargs ->
                    𝒯 (T_Call fname targs) te = 𝒯 b (StringMap.add_all xargs iargs StringMap.empty).


    (* a term always fits in an mpz and only fits in a machine integer if it is in range *)
    Inductive fits (z:Z) : 𝔗 -> Prop := 
    | InInt : Int.inRange z -> fits z C_Int
    | InMpz : fits z (T_Ext Mpz)
    .


    Parameter type_soundness : forall env te f t z, 
        fsl_term_sem f env t z -> fits z (𝒯 t te).


    (* 
        - assuming "getting typed" means having a type inferred by the oracle 
        - `ty_funcall_is_ty_body` tells this is the same as typing the body with infered argument intervals
     *)
    Parameter convergence_of_lfuns_ty : 
        forall fname (targs:list ℨ) (iargs:list 𝐼), 
        forall (typing_envs : Ensemble Γᵢ)  (fe:Γᵢ), Ensembles.In Γᵢ typing_envs fe ->
        (exists ty te, 𝒯 (T_Call fname targs) te = ty) -> 
        Finite_sets.Finite _ typing_envs
    .


    (* fixme: there is also convergence for predicates but the oracle is for terms, not predicates, what to do? *)
    (* Parameter convergence_of_pred_ty : 
    forall S (f : @fenv _fsl_statement S) pname xargs (targs:list ℨ) (iargs:list 𝐼) b, 
    f.(preds) pname = Some (xargs,b) ->
    forall (typing_envs : Ensemble Γᵢ)  (fe:Γᵢ), Ensembles.In Γᵢ typing_envs fe ->
    (exists ty te, eq (𝒯  (P_Call pname targs) te) ty) -> 
    Finite_sets.Finite _ typing_envs
    . *)


End Oracle.