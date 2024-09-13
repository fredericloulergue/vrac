From Coq Require Import Strings.String ZArith.ZArith.
From RecordUpdate Require Import RecordUpdate.
From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax.
From RAC.Environnement Require Import Facts.


Import RecordSetNotations.


Declare Scope c_sem_scope.
Delimit Scope c_sem_scope with csem.

Declare Scope generic_stmt_sem_scope.
Delimit Scope generic_stmt_sem_scope with gssem.

Declare Scope generic_exp_sem_scope.
Delimit Scope generic_exp_sem_scope with gesem.


Definition compiler_prefix : id := "_".
Definition comp_var x : id  := (compiler_prefix ++ x)%string.
Definition is_comp_var := String.prefix compiler_prefix.
Definition res_f : id := comp_var "res".

Definition exp_sem_sig {T : Set} : Type := Env -> @_c_exp T -> 𝕍 -> Prop.
Definition stmt_sem_sig {S T: Set} : Type  :=  @fenv S T -> Env -> @_c_statement S T ->  Env -> Prop.
Definition Empty_exp_sem {T: Set} : @exp_sem_sig T := fun _ _ _ => False.
Definition Empty_stmt_sem {S T: Set} : @stmt_sem_sig S T := fun _ _ _ _ => False.



(* extensible expression semantic *)
Inductive generic_exp_sem {T:Set} {ext_exp : @exp_sem_sig T} (ev:Env): @_c_exp T -> 𝕍 -> Prop :=
| C_E_Int (z:Z) irz : ev |= z => VInt (z ⁱⁿᵗ irz)
| C_E_Var (x:𝓥) z : 
    ev x = Some (Def (VInt z)) -> 
    ev |=  (C_Id x C_Int) => z
| C_E_BinOpInt e e' (z z':Z) op z_ir z'_ir
    (H:Int.inRange (⋄ op z z')) :
    ev |= e =>  VInt (z ⁱⁿᵗ z_ir) ->
    ev |= e' =>  VInt (z' ⁱⁿᵗ z'_ir) ->
    ev |=  BinOpInt e op e' => VInt ((⋄ op) z z' ⁱⁿᵗ H)
| C_E_BinOpTrue e e' (z z' : Z) z_ir z'_ir op :
    ev |= e => VInt (z ⁱⁿᵗ z_ir) ->
    ev |= e' => VInt (z' ⁱⁿᵗ z'_ir) ->
    (◁ op) z z' = true ->
    ev |= BinOpBool e op e' => VInt one
| C_E_BinOpFalse e e' (z z' : Z) op z_ir z'_ir :
    ev |= e => VInt (z ⁱⁿᵗ z_ir) -> 
    ev |= e' => VInt (z' ⁱⁿᵗ z'_ir) -> 
    ((◁ op) z z' = false ) ->
    ev |= BinOpBool e op e' => VInt zero
(* | C_Ext x v t: 
    (* variable must not be of type int (treated by C_E_Var) *)
    t <> C_Int ->
    
    (* variable must be bound and init *)
    ev x = Some (Def v) ->


    (* the external semantic can only add additional constraint, the result is always v *)
    ext_exp ev (C_Id x t) v ->

    ev |= (C_Id x t) => v *)

where  "env '|=' e => z" := (generic_exp_sem env e z) : generic_exp_sem_scope.
#[global] Hint Constructors generic_exp_sem  : rac_hint.

Definition c_exp_sem := @generic_exp_sem Empty_set Empty_exp_sem.
Notation "Ω '|=' e => v"  := (c_exp_sem Ω e v) : c_sem_scope.

#[local] Open Scope utils_scope.
#[local] Open Scope mini_c_scope.
Import FunctionalEnv.

(* extensible statement semantic *)
Inductive generic_stmt_sem {S T: Set} {ext_exp: @exp_sem_sig T} {ext_stmt: @stmt_sem_sig S T} {ext_stmt_vars:  S -> list id} (f : @fenv S T) (ev:Env) : @_c_statement S T -> Env -> Prop := 
    | S_skip  :  (ev |= <{ skip }> => ev) f
    | S_Assign x (z: Int.MI) (e : @_c_exp T) : 
        (* must not be a compiler variable i.e. function return value *)
        is_comp_var x = false ->

        type_of_value (ev x) = Some C_Int ->
        @generic_exp_sem T ext_exp ev e z -> 
        (ev |= <{x = e}> => (ev <| env ; vars ::= {{x\Def z}} |>)) f

    | S_IfTrue ev' (z : Int.MI) e s s' :
        @generic_exp_sem T ext_exp ev e z /\ ~ (z = VInt zero) ->
        (ev  |= s => ev') f ->
        (ev  |= <{ if e s else s'}> => ev') f

    | S_IfFalse ev' e s s' :
        @generic_exp_sem T ext_exp ev e (VInt zero) ->
        (ev |= s' => ev') f ->
        (ev |= <{ if e s else s'}> => ev') f

    | S_While e s  ev' :
        (ev |= <{ if e s ; while e s else skip }> => ev') f ->
        (ev |= <{ while e s }> => ev') f

    | S_Seq  ev' ev'' s s' :
        (ev |= s => ev') f ->
        (ev' |= s' => ev'') f ->
        (ev |= <{ s ; s' }> =>  ev'') f

    | S_FCall fname (b: @_c_statement S T) b_ev c xargs eargs (zargs : Int.MI*) z : 
        let vargs := List.map (fun x => Def (VInt x)) zargs in 
        List.length xargs = List.length eargs ->
        f.(funs) fname = Some (xargs,b) ->
        List.Forall2 (@generic_exp_sem T ext_exp ev) eargs vargs ->
        (empty_env <| env ; vars ::= p_map_addall_back xargs vargs |> |= b => b_ev) f -> 
        ~ List.In res_f (stmt_vars b ext_stmt_vars) -> 
        b_ev res_f = Some (Def (VInt z)) -> (* must be a defined integer value *)
        (ev |= (FCall c fname eargs) => ev <| env ; vars ::= {{c\Def z}} |> <| mstate := b_ev |>) f

    | S_PCall p b ev' xargs eargs (zargs : Int.MI*) : 
        let vargs := List.map (fun x => Def (VInt x)) zargs  in 
        List.length xargs = List.length eargs ->
        f.(procs) p = Some (xargs,b) ->
        List.Forall2 (@generic_exp_sem T ext_exp ev) eargs vargs ->
        (empty_env <| env ; vars ::= p_map_addall_back xargs vargs |> |= b => ev') f -> 
        (ev |= PCall p eargs => ev <| mstate := ev' |>) f

    | S_Return e (z: Int.MI) : 
        @generic_exp_sem T ext_exp ev e (Def (VInt z)) ->
        (ev |= <{ return e }> => ev <| env ; vars ::= {{res_f\Def (VInt z)}} |>) f

    | S_PAssert e (z: Int.MI) :
        @generic_exp_sem T ext_exp ev e z -> z <> VInt zero ->
        (ev |= <{ assert e }> => ev) f

    | S_ExtSem s ev' :  
        (* only S_Ext constructor allowed to use external semantic*)
        ext_stmt f ev (S_Ext s) ev' 
        -> (ev |= (S_Ext s) => ev') f
    
    where "env |= s => env'"  := (fun f => generic_stmt_sem f env s env') : generic_stmt_sem_scope.
#[global] Hint Constructors generic_stmt_sem  : rac_hint.



Inductive generic_decl_sem {T} {ext_ty_val: 𝕍 -> @_c_type T} (ev:Env) : @_c_decl T -> Env -> Prop :=
| D_Decl x (t:@_c_type T) u:
    ev.(vars) x  = None -> 
    _type_of_value ext_ty_val (Some (Undef u)) = Some t  ->
    generic_decl_sem ev (C_Decl t x) (ev <| env ;vars ::= {{x\Undef u}} |>)
.


From Coq Require Import Sets.Ensembles.



Inductive declare_vars {T} {ext_ty_val: 𝕍 -> @_c_type T} (e : Env) : Ensemble (@_c_decl T) -> Env -> Prop :=
| DV_nil : 
    declare_vars e (Empty_set _) e

| DV_cons decls d e': 
    @generic_decl_sem T ext_ty_val e d e' -> 
    declare_vars e (Add _ decls d) e'
.



Definition declare_funs {F S T} : @fenv S T -> Ensemble (@_c_routine F S T) -> Prop := fun _ _ => True. (* todo *)


Inductive generic_pgrm_sem {F S T:Set} 
    {ext_ty_val: 𝕍 -> @_c_type T} {ext_exp : @exp_sem_sig T} {ext_stmt: @stmt_sem_sig S T} {ext_stmt_vars: S -> list id} 
    (ev:Env) (P : @_c_program F S T) (args:Int.MI* ) : Env -> Prop :=

    | P_Pgrm params b ret z ev_decls fenv  ev':

        (* add global declarations to the env *)
        @declare_vars T ext_ty_val ev (list_to_ensemble (fst P)) ev_decls ->
        (* add all functions to fenv *)
        declare_funs fenv (list_to_ensemble (snd P))  -> 

        (* call the main function with the given parameters (same as F_Call except the evaluation env for the body is not empty and we keep the env from the body) *) 
        let vargs := List.map (fun x => Def (VInt x)) args in 
        fenv.(funs) "main"%string = Some (params,b) ->
        List.length params = List.length vargs ->
        @generic_stmt_sem S T ext_exp ext_stmt ext_stmt_vars fenv (ev_decls <| env ; vars ::= p_map_addall_back params vargs |>)  b ev' -> 
        ~ List.In res_f (stmt_vars b ext_stmt_vars) -> 
        ev' res_f = Some (Def (VInt z)) -> (* must be a defined integer value *)

        generic_pgrm_sem ev P args (ev' <| env; vars ::= {{ret\Def z}} |>)
.


Definition _untouched_var_same_eval_exp {T : Set} (exp_sem : @exp_sem_sig T) := 
    forall (ev:Env) (e: @_c_exp T) v x,
    ~ List.In v (exp_vars e) -> 
    exp_sem ev e x ->
    (forall x', exp_sem (ev <| env ; vars ::= {{v\x'}} |>)  e x)
    /\ 
    (forall l z', 
    no_aliasing ev ->
    ev v = Some (Def (VMpz (Some l))) -> exp_sem (ev <| mstate ::= {{l\z'}} |>) e x).



Definition _untouched_var_same_eval_stmt {S T : Set} (exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) (ext_stmt_vars : S -> list id) := 
    forall f ev ev' (s: @_c_statement S T) x, 
    stmt_sem f ev s ev' ->
    ~ List.In x (stmt_vars s ext_stmt_vars) /\ is_comp_var x = false -> 
    ev x = ev' x
.

Definition _no_mem_aliasing {S T : Set} (stmt_sem : @stmt_sem_sig S T)  : Prop := 
    forall (exp_sem:@exp_sem_sig T) f (ev:Env) s (ev':Env), 
    no_aliasing ev
    -> stmt_sem f ev s ev' 
    -> no_aliasing ev'.


Definition _determinist_exp_eval {T : Set} (exp_sem : @exp_sem_sig T) : Prop := 
forall e ev v,  exp_sem ev e v ->  (forall v', exp_sem ev e v' -> v = v')
.


Definition _determinist_stmt_eval {S T : Set} (ext_exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) : Prop := 
    @_determinist_exp_eval T ext_exp_sem  -> 
    forall f s ev ev',  stmt_sem f ev s ev' ->  (forall ev'', stmt_sem f ev s ev'' -> ev' = ev'').

Definition _weakening_of_expression_semantics {T} (exp_sem : @exp_sem_sig T) (rel: Env -> Env -> Prop): Prop := 
    forall e ev (x:𝕍), 
    exp_sem ev e x <-> (forall ev', rel ev ev' -> exp_sem ev' e x).


Fact weakening_of_empty_expression_semantics {T} : _weakening_of_expression_semantics (@Empty_exp_sem T) exist_env_mem_partial_order. 
Proof.
    unfold _weakening_of_expression_semantics. intros. split ; unfold Empty_exp_sem.
    - intros [].
    - intro H. apply H with ev... apply refl_env_mem_partial_order.
Qed.



Definition _weakening_of_statement_semantics_1  {S T : Set} (exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) 
    (rel: Env -> Env -> σ -> Prop) := 
    (*
    should be in both directions according to the article but right to left does not work :
    We will see if the 'bad' direction is used in the proof 
    If this is the cast, one direction is trying to add to have a new env_01 = ev_0 + a and a new env_02 = ev_0 + b so that 
        (ev0 + a) inter ev0 + b) = ev1
    *)  
    _weakening_of_expression_semantics exp_sem (fun e e' => existify (rel e e')) ->
    forall (f : @fenv S T) ev₀ s ev₁,
    stmt_sem f ev₀ s ev₁ ->
    ( forall ev₀' sub, rel ev₀ ev₀' sub ->
        exists ev₁', 
        rel ev₁ ev₁' sub /\ stmt_sem f ev₀' s ev₁').

Fact weakening_of_empty_statement_semantics_1 {S T}: forall rel, _weakening_of_statement_semantics_1 (@Empty_exp_sem T) (@Empty_stmt_sem S T) rel.
Proof. 
    easy. 
Qed.

Import Domain.

Definition _weakening_of_statement_semantics_2  {S T : Set} (exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) 
    (rel: Env -> Env -> σ -> Prop)
    := 
    _determinist_exp_eval exp_sem ->
    _weakening_of_expression_semantics exp_sem (fun e e' => existify (rel e e')) ->
    forall (f: @fenv S T) ev₀ ev₀' s ev₁ sub,
    stmt_sem f ev₀ s ev₁ /\ rel ev₀ ev₀' sub  ->
    (
        forall ev₁',
        stmt_sem f ev₀' s ev₁'->
        (* if v is a compiler variable, i.e. a function return value, v can change*)
        (forall (v:𝓥), (v ∉ ev₀) /\ is_comp_var v = false  -> ev₀' v = ev₁' v) 
        /\
        (forall (x:location), (forall v, ev₀ v <> Some (Def (VMpz x))) -> ev₀'.(mstate) (proj1_sig sub x) = ev₁'.(mstate) (proj1_sig sub x))
    ).


Fact weakening_of_empty_statement_semantics_2 {S T}: forall rel, _weakening_of_statement_semantics_2 (@Empty_exp_sem T) (@Empty_stmt_sem S T) rel.
Proof. 
    easy. 
Qed.


(* required to prove _weakening_of_statement_semantics_3 *)
Definition _weakening_of_expression_semantics_3 {T : Set} (exp_sem : @exp_sem_sig T)  (rel: Env -> Env -> Prop) := 
    forall ev e z,
    exp_sem ev e z ->
    forall ev', rel ev' ev ->
    (
        (forall v, (dom ev - dom ev') v -> ~ List.In v (exp_vars e))
        /\
        (forall x, (dom ev.(mstate) - dom ev'.(mstate)) x -> (exists v, ev v = Some (Def (VMpz x)) /\ ~ List.In v (exp_vars e)))
    ) ->

    exp_sem  ev' e z
.


Fact weakening_of_empty_expression_semantics_3 {T}: forall rel, _weakening_of_expression_semantics_3 (@Empty_exp_sem T) rel.
Proof. 
    easy.
Qed.



Definition _weakening_of_statement_semantics_3  {S T : Set} (stmt_sem : @stmt_sem_sig S T) (ext_stmt_vars: S -> list id)
    (rel: Env -> Env -> Prop)  := 
    forall f ev₀  s ev₁,
    stmt_sem f ev₀ s ev₁ -> 

    forall ev₀', rel ev₀' ev₀ ->
    (
        (forall v, (dom ev₀ - dom ev₀') v -> ~ List.In v (stmt_vars s ext_stmt_vars))
        /\
        (forall x, (dom ev₀.(mstate) - dom ev₀'.(mstate)) x -> (exists v, ev₀ v = Some (Def (VMpz x)) /\ ~ List.In v (stmt_vars s ext_stmt_vars)))
    ) ->

    exists ev₁', stmt_sem f ev₀' s ev₁'
    .

Fact weakening_of_empty_statement_semantics_3 {S T}: forall f rel, _weakening_of_statement_semantics_3 (@Empty_stmt_sem S T) f rel.
Proof. 
    easy. 
Qed.