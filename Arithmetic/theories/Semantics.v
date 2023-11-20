Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import ZArith.ZArith.
From Coq Require Import Strings.String.
From Coq Require Import BinaryString.
Open Scope Z_scope.

Definition exp_sem_sig {T : Set} : Type := Env -> @_c_exp T -> 𝕍 -> Prop.
Definition stmt_sem_sig {S T: Set} : Type  :=  @𝓕 S T -> @𝓟 S T-> Env -> @_c_statement S T ->  Env -> Prop.
Definition Empty_exp_sem : @exp_sem_sig Empty_set := fun _ _ _ => False.
Definition Empty_stmt_sem : @stmt_sem_sig Empty_set Empty_set := fun _ _ _ _ _ => False.


Declare Scope generic_exp_sem_scope.
Delimit Scope generic_exp_sem_scope with gesem.

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
| C_Ext x v t: 
    (* variable must not be of type int (treated by C_E_Var) *)
    t <> C_Int ->
    
    (* variable must be bound and init *)
    ev x = Some (Def v) ->


    (* the external semantic can only add additional constraint, the result is always v *)
    ext_exp ev (C_Id x t) v ->

    ev |= (C_Id x t) => v

where  "env '|=' e => z" := (generic_exp_sem env e z) : generic_exp_sem_scope.

#[global] Hint Constructors generic_exp_sem  : rac_hint.


Declare Scope c_sem_scope.
Delimit Scope c_sem_scope with csem.


Definition c_exp_sem := @generic_exp_sem Empty_set Empty_exp_sem.

Notation "Ω |= e => v"  := (c_exp_sem Ω ⊥ e v) : c_sem_scope.

Inductive _gmp_exp_sem (ev:Env) : gmp_exp -> 𝕍 -> Prop :=
| GMP_E_Var (x:𝓥) (l:location) (z:mpz_val) : 
    ev x = Some (Def l) -> 
    ev.(mstate) l = Some z ->
    _gmp_exp_sem ev (C_Id x Mpz) (VMpz l)
.

#[global] Hint Constructors _gmp_exp_sem  : rac_hint.

Declare Scope gmp_exp_sem_scope.
Delimit Scope gmp_exp_sem_scope with gmpesem.
Definition gmp_exp_sem := @generic_exp_sem _gmp_t _gmp_exp_sem.
Notation "ev '|=' e => z" := (gmp_exp_sem ev e z) : gmp_exp_sem_scope.

Open Scope mini_c_scope.
From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.

Declare Scope generic_stmt_sem_scope.
Delimit Scope generic_stmt_sem_scope with gssem.

(* extensible statement semantic *)
Inductive generic_stmt_sem {S T: Set} {ext_exp: @exp_sem_sig T} {ext_stmt: @stmt_sem_sig S T} (funs:@𝓕 S T) (procs: @𝓟 S T) (ev:Env) : @_c_statement S T -> Env -> Prop := 
    | S_skip  :  (ev |= <{ skip }> => ev) funs procs
    | S_Assign x z (e : @_c_exp T) : 
        (* must not be a compiler variable i.e. function return value *)
        is_comp_var x = false ->

        type_of_value (ev x) = Some C_Int ->
        (* value returned must be of same type*)
        type_of_value (Some z) = Some C_Int ->

        @generic_exp_sem T ext_exp ev e z -> 
        (ev |= <{x = e}> => (ev <| env ; vars ::= {{x\z}} |>)) funs procs

    | S_IfTrue ev' z e s s' :
        @generic_exp_sem T ext_exp ev e z /\ ~ (z = VInt zero) ->
        (ev  |= s => ev') funs procs ->
        (ev  |= <{ if e s else s'}> => ev') funs procs

    | S_IfFalse ev' e s s' :
        @generic_exp_sem T ext_exp ev e (VInt zero) ->
        (ev |= s' => ev') funs procs ->
        (ev |= <{ if e s else s'}> => ev') funs procs

    | S_While e s  ev' :
        (ev |= <{ if e s ; while e s else skip }> => ev') funs procs ->
        (ev |= <{ while e s }> => ev') funs procs

    | S_Seq  ev' ev'' s s' :
        (ev |= s => ev') funs procs ->
        (ev' |= s' => ev'') funs procs ->
        (ev |= <{ s ; s' }> =>  ev'') funs procs

    | S_FCall f (b: @_c_statement S T) ev' c xargs eargs (zargs : 𝕍 ⃰ ) z : 
        List.length xargs = List.length eargs ->
        funs f = Some (xargs,b) ->
        List.Forall2 (@generic_exp_sem T ext_exp ev) eargs zargs ->
        (empty_env <| env ; vars ::= p_map_addall_back xargs zargs |> |= b => ev') funs procs -> 
        ~ List.In res_f (stmt_vars b) -> 
        ev' res_f = Some (Def z) -> (* must be a defined value *)
        (ev |= (FCall c f eargs) => ev <| env ; vars ::= {{c\Def z}} |> <| mstate := ev' |>) funs procs

    | S_PCall p b ev' xargs eargs zargs : 
        List.length xargs = List.length eargs ->
        procs p = Some (xargs,b) ->
        List.Forall2 (@generic_exp_sem T ext_exp ev) eargs zargs ->
        (empty_env <| env ; vars ::= p_map_addall_back xargs zargs |> |= b => ev') funs procs -> 
        (ev |= PCall p eargs => ev <| mstate := ev' |>) funs procs

    | S_Return e z : 
        (* not allowed to return an unassigned value *)
        @generic_exp_sem T ext_exp ev e (Def z) ->
        (ev |= <{ return e }> => ev <| env ; vars ::= {{res_f\Def z}} |>) funs procs

    | S_PAssert  e z :
        @generic_exp_sem T ext_exp ev e z -> z <> VInt zero ->
        (ev |= <{ assert e }> => ev) funs procs

    | S_ExtSem s ev' :  
        (* only S_Ext constructor allowed to use external semantic*)
        ext_stmt funs procs ev (S_Ext s) ev' 
        -> (ev |= (S_Ext s) => ev') funs procs
    
    where "env |= s => env'"  := (fun funs procs => generic_stmt_sem funs procs env s env') : generic_stmt_sem_scope.
    
#[global] Hint Constructors generic_stmt_sem  : rac_hint.


(* Declare Scope c_sem_scope.
Delimit Scope c_sem_scope with csem. 
Definition c_stmt_sem := @generic_stmt_sem Empty_set Empty_set Empty_exp_sem Empty_stmt_sem.
Notation "ev |= s => ev'"  := (c_stmt_sem ev s ev') : c_sem_scope. *)



Definition c_decl_sem (env env':Ω) (mem mem':𝓜) d : Prop := 
        forall x t u,
        env x  = None -> 
        (Uτ u) = Some t ->
        d = C_Decl t x -> env' = env <| vars ::= {{x\u}} |> /\ mem = mem'.
        


Open Scope gmp_exp_sem_scope.
Open Scope mini_gmp_scope.
Declare Scope gmp_stmt_sem_scope.
Delimit Scope gmp_stmt_sem_scope with gmpssem.

Inductive _gmp_stmt_sem { S T : Set }(funs : @𝓕 S T) (procs : @𝓟 S T) (ev:Env) : gmp_statement -> Env -> Prop := 
    | S_init x (l:location):
        (forall v, ev v <> Some (Def (VMpz (Some l)))) ->
        (exists n, ev x = Some (Undef (UMpz n)))%type ->
        (ev |= <(init(x))> => ev <| env ; vars ::= {{x\Def (VMpz (Some l))}} |> <| mstate ::= {{l\Defined 0}} |>) funs procs
    
    | S_clear x a u:   
        ev x = Some (Def (VMpz (Some a))) ->   
        (ev |= <(cl(x))> => ev <| env ; vars ::= {{x\(Def (VMpz None))}} |> <| mstate ::= {{a\Undefined u}} |>) funs procs

    | S_set_i x y z a :  
        ev x = Some (Def (VMpz (Some a))) ->
        (ev |= y => VInt z)%gmpesem ->
        (ev |= <(set_i(x,y))> => ev <| mstate ::= {{a\Defined (z ̇)}} |>) funs procs

    | S_set_z x y z (a n : location) :  
        ev x = Some (Def (VMpz a)) ->
        ev y = Some (Def (VMpz n)) ->
        ev.(mstate) n = Some z ->
        (ev |= <(set_z(x,y))> => ev <| mstate ::= {{a\z}} |>) funs procs 

    | S_get_int x (y:id) z v (ir:Int.inRange z) :
        (ev |= C_Id y Mpz => VMpz (Some v))%gmpesem ->
        ev.(mstate) v = Some (Defined z) -> 
        (ev |= <(x = get_int(y))> => ev <| env ; vars ::= {{x\VInt (z ⁱⁿᵗ ir) : 𝕍}} |>) funs procs

    | S_set_s s x z a :
        ev x = Some (Def (VMpz (Some a))) ->
        BinaryString.to_Z s = z ->
        (ev |= <(set_s(x,s))> => ev <| mstate ::= {{a\Defined z}} |> ) funs procs

    | S_cmp c x (vx vy :location) lx y ly (b:𝕍):
        (ev |= C_Id x Mpz => vx)%gmpesem ->
        (ev |= C_Id y Mpz => vy)%gmpesem ->
        ev.(mstate) vx = Some (Defined lx) ->
        ev.(mstate) vy = Some (Defined ly) ->
        (
            (Z.gt lx ly <-> b = VInt one) /\
            (Z.lt lx ly <-> b = VInt sub_one) /\
            (Z.eq lx ly <-> b = VInt zero)
        ) ->
        (ev |= <(c = cmp(x,y))> => ev <| env ; vars ::= {{c\b}} |>) funs procs
    
    | S_op bop r lr x y (vx vy : location) z1 z2 :
        (ev |= C_Id x Mpz => vx)%gmpesem ->
        ev.(mstate) vx = Some (Defined z1) -> 
        (ev |= C_Id y Mpz =>  vy)%gmpesem ->
        ev.(mstate) vy = Some (Defined z2) -> 
        ev r = Some (Def (VMpz (Some lr))) ->
        (ev |= op bop r x y => ev <| mstate ::= {{lr\Defined (⋄ (□ bop) z1 z2) }} |>) funs procs

where "ev |= s => ev'"  := (fun funs procs => _gmp_stmt_sem funs procs ev s ev') : gmp_stmt_sem_scope.

#[global] Hint Constructors _gmp_stmt_sem  : rac_hint.


Definition gmp_stmt_sem := @generic_stmt_sem _gmp_statement _gmp_t _gmp_exp_sem _gmp_stmt_sem.
(*
Notation "Ω ⋅ M |= s => Ω' ⋅ M'"  := (fun funs procs => gmp_stmt_sem funs procs Ω M s Ω' M') : gmp_sem_scope. 
 *)

Inductive fsl_term_sem (ev:Env) : ℨ -> Z -> Prop :=
| FSL_E_Int z : fsl_term_sem ev (T_Z z) z 
| FSL_E_LVar x z : ev.(binds) x = Some z -> fsl_term_sem ev (T_Id x) z
| FSL_E_Var x v : 
    ev v = Some (Def (VInt x)) ->  
    fsl_term_sem ev (T_Id v) x ̇

| FSL_E_BinOpInt t t' z zint z' z'int op :  
    fsl_term_sem ev t z ->
    fsl_term_sem ev t' z' ->
    ~ (op = FSL_Div /\ z = 0)%type ->
    fsl_term_sem ev (T_BinOp t op t') ((fsl_binop_int_model op) zint z'int)

| FSL_E_CondTrue p t z t':
    fsl_pred_sem ev p BTrue ->
    fsl_term_sem ev t z ->
    fsl_term_sem ev (T_Cond p t t') z

| FSL_E_CondFalse p t t' z':
    fsl_pred_sem ev p BFalse ->
    fsl_term_sem ev t' z' ->
    fsl_term_sem ev (T_Cond p t t') z'

    with 

fsl_pred_sem (ev:Env) :  𝔅 -> 𝔹 -> Prop :=
| FP_True : fsl_pred_sem ev P_True BTrue
| FP_False : fsl_pred_sem ev P_False BFalse

| FP_BinOpTrue t t' z z' (op:fsl_binop_bool): 
    fsl_term_sem ev t z ->
    fsl_term_sem ev t' z' ->
    (fsl_binop_bool_model op) z z' ->
    fsl_pred_sem ev (P_BinOp t op t) BTrue

| FP_BinOpFalse t t' z z' (op:fsl_binop_bool): 
    fsl_term_sem ev t z ->
    fsl_term_sem ev t' z' ->
    ~ (fsl_binop_bool_model op) z z' ->
    fsl_pred_sem ev (P_BinOp t op t) BFalse

| FP_NotTrue p : 
    fsl_pred_sem ev p BTrue ->
    fsl_pred_sem ev (Not p) BFalse

| FP_NotFalse p : 
    fsl_pred_sem ev p BFalse ->
    fsl_pred_sem ev (Not p) BTrue 

| FP_DisjLeftTrue p p' : 
    fsl_pred_sem ev p BTrue ->
    fsl_pred_sem ev (Disj p p') BTrue 

| FP_DisjLeftFalse p p' z : 
    fsl_pred_sem ev p BFalse ->
    fsl_pred_sem ev p' z ->
    fsl_pred_sem ev (Disj p p') z
.

#[global] Hint Constructors fsl_term_sem : rac_hint.
#[global] Hint Constructors fsl_pred_sem : rac_hint.

Declare Scope fsl_sem_scope.
Delimit Scope fsl_sem_scope with fslsem.

(* Notation "Ω '|=' t => v" := (fsl_term_sem Ω t v) : fsl_sem_scope. *)

Inductive _fsl_assert_sem { S T : Set } (funs : @𝓕 S T) (procs : @𝓟 S T) (ev:Env) : fsl_statement -> Env -> Prop :=
| FSL_Assert (p:𝔅) : 
    fsl_pred_sem ev p BTrue ->
    _fsl_assert_sem funs procs ev (LAssert p) ev
.

#[global] Hint Constructors _fsl_assert_sem : rac_hint.


Definition fsl_stmt_sem := @generic_stmt_sem _fsl_statement _gmp_t gmp_exp_sem _fsl_assert_sem.
Notation "ev |= s => ev'"  := (fun funs procs => fsl_stmt_sem funs procs ev s ev') : fsl_sem_scope. 



(* macro semantic *)


Declare Scope macro_sem_scope.
Inductive macro_sem (ev:Env) (e:gmp_exp): Z -> Prop :=
| M_Int x :  
    gmp_exp_sem ev e (VInt x) ->
    ev |= e ⇝ x ̇
| M_Mpz l z : 
    gmp_exp_sem ev e (VMpz (Some l)) ->
    ev.(mstate) l = Some (Defined z) ->
    ev |= e ⇝ z
where "ev '|=' e ⇝ z" := (macro_sem ev e z) : macro_sem_scope.

#[global] Hint Constructors macro_sem : rac_hint.
