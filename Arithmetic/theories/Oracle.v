From Coq Require Import ZArith.ZArith Strings.String.
From Coq.Structures Require Import Orders OrdersEx.
From Coq.Sets Require Import Ensembles Finite_sets.
From Coq.Lists Require Streams.
From RAC Require Import Utils Environment.
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

Module AbstractInterpretation.
    Import Lists.Streams.

    Open Scope Z_scope.

    Definition interval : Type := (Z ⨉ Z). 

    Definition Γᵢ : Type :=  StringMap.t interval.

    (* collecting environment: set of logic environments (from a binder to an integer )*)
    Definition Ξ : Type := list Ωₗ.
    


    (* collecting semantics *)
    Definition C (E:Ξ) (t: ℨ) (z:Z) (fenv: fenv) : Prop :=  
        exists (e : Env), List.In e.(env).(binds) E /\ (e |= t => z)%fsltsem fenv.

    Definition min_inf := MI.m_int - 1.
    Definition plus_inf := MI.M_int + 1.


    Definition clamp (z: Z) : Z := 
        if z <? MI.m_int then min_inf 
        else if z >? MI.M_int then plus_inf
        else z.

    Module OrderedInterval <: OrderedType := PairOrderedType(Z_as_OT)(Z_as_OT).
    Module OrderedIntervalOption <: OrderedType := OptionOrderedType(OrderedInterval).

    Module Interval := MSetEnv(OrderedIntervalOption).
    Infix "⊑" := Interval.subset.

    (* Lattice *)
    Definition bot : Interval.elt := None.
    Definition top : Interval.elt := Some (min_inf,plus_inf).
    Definition join := Interval.union.
    Definition meet := Interval.inter.

    Definition abstract_map (X: IntSet.t) : Interval.t := 
        if IntSet.is_empty X then 
            Interval.singleton bot 
        else
            match (IntSet.min_elt X, IntSet.max_elt X ) with 
            | (Some min, Some max) => Interval.singleton (Some (clamp min, clamp max))
            | (None,None) => Interval.singleton (Some (min_inf, plus_inf))
            | (Some min, None) => Interval.singleton (Some (clamp min, plus_inf))
            | (None, Some max) => Interval.singleton (Some (min_inf, clamp max))
            end
    .

    #[program ] Definition concrete_map : Interval.t -> IntSet.t. Proof. admit. Admitted.
    
            
    Lemma galois_connection (X : IntSet.t) (I : Interval.t) :  
        IntSet.Subset X (concrete_map I) <-> Interval.Subset (abstract_map X) I.
    Proof.
        split.
        - revert X. induction I using Interval.Props.set_induction; intros X Hx.
            + admit.
            +  admit.
        - admit.
    Admitted.


    Definition op_lift (op: IntSet.t -> IntSet.t -> IntSet.t) : Interval.t -> Interval.t -> Interval.t := 
        fun i1 i2 => abstract_map (op (concrete_map i1) (concrete_map i2))
    .

    Definition op_set (op: fsl_binop_int) (X Y : IntSet.t) : IntSet.t := 
        IntSet.fold (fun x s =>
            IntSet.fold (fun y s' => IntSet.add ((fsl_binop_int_model op) x y) s') Y s
        ) X IntSet.empty
    . 

    Axiom widening_op : Interval.t -> Interval.t -> Interval.t.
    Axiom W1 : forall I I', Interval.Subset I (widening_op I I') /\ Interval.Subset I' (widening_op I I').
    CoFixpoint widening_seq (Jseq : Stream Interval.t) (I : Stream Interval.t) :  Stream Interval.t. Admitted.
    Axiom W2 : (forall (J: Interval.t)  (Jseq : list Interval.t ), exists n, forall x, x > n -> List.nth n Jseq = List.nth x Jseq)%nat. (*todo*)

        


    Inductive interval_deriv (f: fsl_prog_fenv) (g: Γᵢ) (ev:Env) : ℨ -> Interval.t -> Prop :=
    | interval_z z : interval_deriv f g ev (T_Z z) (Interval.singleton (Some (z,z)))
    
    | interval_lvar x : interval_deriv f g ev (T_Id x FSL_Integer) (Interval.singleton (StringMap.find x g))
    
    | inteval_var x : interval_deriv f g ev (T_Id x FSL_Int) (Interval.singleton (Some (MI.m_int, MI.M_int)))
    
    | interval_binop t1 t2 I1 I2 op :
        interval_deriv f g ev t1 I1 ->
        interval_deriv f g ev t2 I2 ->
        interval_deriv f g ev (T_BinOp t1 op t2) (op_lift (op_set op) I1 I2)
    
    | interval_cond cond t1 t2 I1 I2 : 
        interval_deriv f g ev t1 I1 ->
        interval_deriv f g ev t2 I2 ->
        interval_deriv f g ev (T_Cond cond t1 t2) (join I1 I2)

    | interval_fun fname bdy targs Iargs params :
        List.length params = List.length targs ->
        StringMap.find fname f.(funs) = Some (params,bdy) /\
        List.Forall2 (fun t I => interval_deriv f g ev t I) targs Iargs ->
        List.Forall2 (fun I param => True (* todo *)) Iargs params->
        interval_deriv f g ev (T_Call fname targs) (Interval.singleton None (* todo *)) 

    | interval_fun_init fname bdy targs Iargs params I :
        List.length params = List.length targs ->
        StringMap.find fname f.(funs) = Some (params,bdy) /\
        List.Forall2 (fun t I => interval_deriv f g ev t I) targs Iargs ->
        interval_fderiv f g ev fname I ->
        interval_deriv f g ev (T_Call fname targs) I

    with interval_fderiv (f: fsl_prog_fenv) (g: Γᵢ) (ev:Env) : id -> Interval.t -> Prop :=
    | fderiv_base fname bdy I : 
        interval_deriv f g ev bdy I ->
        (* I included in delta_res f *)
        interval_fderiv f g ev fname I

    | fderiv_ind fname bdy I J :
        interval_deriv f g ev bdy I ->
        interval_fderiv f g ev fname J ->
        interval_fderiv f g ev fname J
    .

    (* determinization by choosing fun over fun_init and fderiv_base over fderiv_ind*)

    (* Lemma 1: deterministic *)

    (* Theorem 1: termination of the rule system *)

    (* Theorem 2: soundness of the rule system *)

End AbstractInterpretation.