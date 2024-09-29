From Coq Require Import ZArith.ZArith Strings.String Logic.FinFun Sets.Ensembles.
From Coq.Structures Require Import Equalities EqualitiesFacts Orders OrdersEx.


From RAC Require Import Utils. 
From RAC.Languages Require Import Syntax. 

#[local] Open Scope utils_scope.

Import FunctionalEnv.
Import RecordSetNotations.


Record fenv {S T : Set} := mk_fenv {
    funs : @𝓕 S T ;
    procs : @𝓟 S T ;
    lfuns : StringMap.t (𝔏★ ⨉ ℨ) ;
    preds : StringMap.t (𝔏★ ⨉ 𝔅) ;
}.

Definition empty_fenv {S T : Set} := (mk_fenv S T  StringMap.empty  StringMap.empty  StringMap.empty  StringMap.empty). 


Definition fsl_prog_fenv : Type := @fenv _fsl_statement Datatypes.Empty_set.
Definition rac_prog_fenv : Type := @fenv _gmp_statement _gmp_t.

#[export] Instance eta_fsl_prog_fenv : Settable fsl_prog_fenv := 
    settable! mk_fenv _fsl_statement Datatypes.Empty_set <funs ; procs; lfuns; preds>.
#[export] Instance eta_rac_prog_fenv : Settable rac_prog_fenv := 
    settable!  mk_fenv _gmp_statement _gmp_t <funs ; procs; lfuns; preds>.


Definition build_fsl_fenv (routines: list fsl_routine) : fsl_prog_fenv := 

    List.fold_left (fun fenv r => 
    match r with 
    | PFun rtype name args _ body => 
        match rtype with 
        | Void => 
            (* procedure *) 
            fenv <| procs := StringMap.add name (extract_c_args args,body) fenv.(procs) |>
        | C_Int =>  
            (* function *)
            fenv <| funs := StringMap.add name (extract_c_args args,body) fenv.(funs) |>

        | T_Ext _ => 
            (* PFun can't have T_Ext rtype *)
            fenv
        end
    | F_Ext (LFun rtype name args body) => 
        (* logic function *)
        fenv <| lfuns := StringMap.add name (extract_fsl_args args,body) fenv.(lfuns) |>
        

    | F_Ext (Predicate name args body) => 
        (* predicate *)
        fenv <| preds := StringMap.add name (extract_fsl_args args,body) fenv.(preds) |>

    end
    ) routines empty_fenv
.



Equations build_rac_fenv (routines: list gmp_routine) : rac_prog_fenv := 
| routines => 
    List.fold_left aux routines empty_fenv

where aux : rac_prog_fenv -> gmp_routine -> rac_prog_fenv := 
| fenv,PFun rtype name args decls body  with rtype => 
    {
        | C_Int => fenv <| funs ::= StringMap.add name (extract_c_args args,body) |>
        | C_Void => fenv <| procs ::= StringMap.add name (extract_c_args args,body) |>
    }
.





Module Int16Bounds.
    Definition m_int := (-32768)%Z.
    Definition M_int := 32767%Z.
End Int16Bounds.

Module MI := MachineInteger Int16Bounds.


Notation "z ̇" := (MI.of_mi z) (at level 0).
Notation "z 'ⁱⁿᵗ'" := (MI.to_mi z) (at level 99).




Fact zeroinRange : MI.inRange 0.  now split. Qed.
Fact oneinRange : MI.inRange 1. now split. Qed.
Fact suboneinRange : MI.inRange (-1). now split. Qed.

#[global] Hint Resolve zeroinRange: rac_hint.
#[global] Hint Resolve oneinRange: rac_hint.
#[global] Hint Resolve suboneinRange: rac_hint.

Definition zero :=  0ⁱⁿᵗ zeroinRange.
Definition one := 1ⁱⁿᵗ oneinRange.
Definition sub_one := (-1)ⁱⁿᵗ suboneinRange.




(* adresses and undefined values must be an enumerable set. We use nat for convenience *)
Definition location := nat. 
Definition undefval := nat.

#[global] Instance location_eq_dec : FunctionalEnv.EqDecC location := {eq_dec := Nat.eq_dec}.


Inductive value := 
    | VInt (n:MI.t) :> value (* set of type int, a machine integer (may overflow) *)
    | VMpz (l:option location) (* memory location for values of type mpz, none is a null pointer *) 
.


Inductive undef := 
    | UInt : undefval -> undef (* set of undefined values of type int *) 
    | UMpz : undefval -> undef (* set of undefined values of type mpz *) 
.


Inductive 𝕍 :=  Def (v : value) :> 𝕍 | Undef (uv : undef) :> 𝕍.
Coercion v_int (mi:MI.t) : 𝕍 := Def (VInt mi). 
Coercion def_v_mpz (l:nat) : 𝕍 := Def (VMpz (Some l)). 
Coercion mpz_loc (l:location) : 𝕍 := VMpz (Some l).

Inductive 𝔹 := BTrue | BFalse.

Definition 𝔹_to_Z  (b:𝔹) : Z := if b then 1 else 0.

Inductive mpz_val := Defined (z:Z) :> mpz_val | Undefined (z:Z).


Definition 𝓜 := location ⇀ mpz_val. 


Definition Ωᵥ : Type := 𝓥 ⇀ 𝕍.
Definition Ωₗ : Type := 𝔏 ⇀ ℤ.


(* Coercion ir_z (x:Z) ir : 𝕍 := VInt (x ⁱⁿᵗ ir). *)
Coercion int_option_loc (l:nat) :=  Some l.


(* Coercion VMpz : nat >-> Value. *)
(* 
Definition same_values (v1 v2: option 𝕍) : bool := match v1,v2 with
    | Some (VInt n1), Some (VInt n2) => MI.mi_eqb n1 n2
    | Some (VMpz n1), Some (VMpz n2) => (n1 =? n2)%nat
    | _,_ => false
end
. *)

Record Ω := mkΩ {vars :> Ωᵥ ;  binds :> Ωₗ}.
Definition empty_Ω  : Ω := {|vars:=⊥;binds:=⊥|}.
#[export] Instance etaΩ : Settable _ := settable! mkΩ <vars ; binds>.
Definition apply_env (a : Ω) (v : 𝓥) : option 𝕍 := a.(vars) v.
Coercion apply_env : Ω >-> Funclass.

Record Env := mkEnv {env :> Ω ;  mstate :> 𝓜}.
Definition empty_env : Env := {|env:=empty_Ω;mstate:=⊥|}.
#[export] Instance etaEnv : Settable _ := settable! mkEnv <env ; mstate>.
Definition apply_mem (a : Ω) (l : 𝔏) : option Z := a.(binds) l.
(* Coercion apply_mem : Ω >-> Funclass. *) (* can't use same coercion path *)


Definition fresh_location (e:Env) (l:location) : Prop := forall v, e v <> Some (Def (VMpz (Some l))).

Definition σ : Type := {f : location -> location | Bijective f}.

Definition induced (f: location -> location) : 𝕍 -> 𝕍 := fun value => match value with
| Def (VMpz (Some l)) => Def (VMpz (Some (f l)))
| v => v
end.



Inductive param_env_partial_order (env env':Ω) (var: 𝓥) (f:σ) : Prop :=
| EsameInt n : 
    env var = Some (Def (VInt n))
    ->  env' var = Some (Def (VInt n))
    -> param_env_partial_order env env' var f
| EsameMpz (l:location) : 
    (* if the mpz is not a null pointer, we must have a corresponding adress *)
    env var = Some (Def (VMpz l)) ->
    env' var = Some (Def (VMpz (proj1_sig f l)))
    -> param_env_partial_order env env' var f
| ENullPtr : 
    (* if the mpz is a null pointer, it must stay null *)
    env var = Some (Def (VMpz None)) ->
    env' var = Some (Def (VMpz None))
    -> param_env_partial_order env env' var f
| EundefInt u : env var = Some (Undef (UInt u))
    -> (exists u', env' var = Some (Undef (UInt u'))) \/  (exists n, env' var = Some (Def (VInt n)))
    -> param_env_partial_order env env' var f
| EundefMpz u: env var = Some (Undef (UMpz u))
    -> (exists u, env' var = Some (Undef (UMpz u))) \/  (exists l, env' var = Some (Def (VMpz l)))
    -> param_env_partial_order env env' var f
| Enone : env var = None -> param_env_partial_order env env' var f
.

Definition param_mem_partial_order (mem mem':𝓜)  (l: location) (f:σ) : Prop := 
    forall i, mem l = Some i ->  (mem' (proj1_sig f l)) = Some i.


(* stronger constraints *)
Definition strong_param_env_partial_order (env env':Ω) (var: 𝓥) (f:σ) : Prop :=
    forall v x, env v = Some x ->  env' v = Some (induced (proj1_sig f) x).



#[global] Hint Constructors param_env_partial_order : rac_hint.

Declare Scope env_scope.
Delimit Scope env_scope with env.
Declare Scope mem_scope.
Delimit Scope mem_scope with mem.
Declare Scope env_mem_scope.
Delimit Scope env_mem_scope with envmem.

Definition existify {A} (p: A -> Prop) : Prop := exists a, p a. 

Definition env_partial_order env env' := fun f => forall v, param_env_partial_order env env' v f.
Definition exist_env_partial_order env env' := existify (env_partial_order env env').
Infix "⊑" := exist_env_partial_order : env_scope.


Definition mem_partial_order env env' := fun f => forall l, param_mem_partial_order env env' l f.
Definition exist_mem_partial_order env env' := existify (mem_partial_order env env').
Infix "⊑" := exist_mem_partial_order : mem_scope.


Definition env_mem_partial_order e e' f := 
    env_partial_order e.(env) e'.(env) f /\ mem_partial_order e.(mstate) e'.(mstate) f.
Definition exist_env_mem_partial_order env env' := existify (env_mem_partial_order env env').
Infix "⊑" := exist_env_mem_partial_order : env_mem_scope.


Definition strong_env_partial_order env env' := fun f => forall v, strong_param_env_partial_order env env' v f.
Definition exist_strong_env_partial_order env env' := existify (strong_env_partial_order env env').

Definition strong_env_mem_partial_order e e' f := 
        strong_env_partial_order e.(env) e'.(env) f /\ mem_partial_order e.(mstate) e'.(mstate) f.
Definition exist_strong_env_mem_partial_order env env' := existify (strong_env_mem_partial_order env env').



Definition no_aliasing (ev : Ω) : Prop := 
    forall v v' l l', 
    v <> v' ->
    ev v = Some (Def (VMpz (Some l)))  ->
    ev v' = Some (Def (VMpz (Some l'))) -> 
    l <> l'.


Definition _type_of_value {T:Set} (ext_valty : 𝕍 -> @c_type T) : option 𝕍 -> option (@c_type T) := fun v => match v with
| Some (VInt _) | Some (UInt _) => Some C_Int
| Some t => Some (ext_valty t)
| None => None
end.

Definition _type_of_gmp :  𝕍 -> gmp_t := fun _ =>  T_Ext Mpz.


Definition type_of_value := _type_of_value _type_of_gmp.



(* environnement enrichers used in section F *)
Inductive add_z_var (e : Env) (τ:gmp_t) (var:id) (z:Z) | : Env -> Prop :=
| typeDefInt irz : 
    (* fixme: section F is able to tell if z is in Uint and in any case transform it into a machine integer (how?) *)
    τ = C_Int ->
    add_z_var (e <| env ; vars ::= {{var\z ⁱⁿᵗ irz : 𝕍}} |>)

| typeMpz l:
    τ = Mpz ->
    fresh_location e l ->
    add_z_var ( e <| env ; vars ::= {{var\l : 𝕍}} |><| mstate ::= {{l\Defined z}} |>)
.

Notation "env '+++' ( t , v , z )" := (add_z_var env t v z) (at level 99).


Module gmp_type_as_MDT <: MiniDecidableType.
    Definition t := gmp_t.
    Definition eq_dec := eq_dec_gmp_t.
End gmp_type_as_MDT.

Module gmp_type_as_UDT := Make_UDT(gmp_type_as_MDT).

(*



Module gmp_type_as_UOT.
    Include gmp_type_as_UDT.

    Parameter lt : t -> t -> Prop.

    Parameter lt_strorder : StrictOrder lt.

    Parameter lt_compat : Proper (eq ==> eq ==> iff) lt.

    Parameter compare : t -> t -> comparison.

    Parameter compare_spec: forall x y, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
End gmp_type_as_UOT.

(* build decidable triple *)
Module Pair1 := PairOrderedType(gmp_type_as_UOT)(String_as_OT).
Module Pair2 := PairOrderedType(Pair1)(Z_as_OT).

Module VarSet := MSetEnv(Pair2). *)

Notation 𝐴 := (Ensemble (gmp_t ⨉ id ⨉ Z)).

Inductive add_z_vars (e : Env) : 𝐴 -> Env -> Prop := 
| add_z_vars_nil : add_z_vars e (Empty_set _) e

| add_z_vars_cons (vars:𝐴) t v z e': 
    e +++ (t,v,z) e' -> 
    add_z_vars e (Add _ vars (t,v,z)) e'
.

Notation "env '+++' e" := (add_z_vars env e) (at level 99).

Fixpoint list_to_ensemble {X} (l:list X) : Ensemble X := match l with
| nil => Empty_set _
| List.cons hd tl => Add _ (list_to_ensemble tl) hd
end.   