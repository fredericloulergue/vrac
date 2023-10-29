Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import ZArith.ZArith.
From Coq Require Import Strings.String.
From Coq Require Import BinaryString.
Open Scope Z_scope.


#[local] Declare Scope generic_sem_scope.
#[local] Declare Scope _gmp_stmt_sem_scope.



Declare Scope c_sem_scope.
Declare Scope mini_c_decl_scope.
Declare Scope gmp_sem_scope.
Declare Scope fsl_sem_scope.



Definition exp_sem_sig {T : Set} : Type := Ω -> 𝓜 -> @_c_exp T -> 𝕍 -> Prop.
Definition stmt_sem_sig {S T: Set} : Type  :=  @𝓕 S T -> @𝓟 S T-> Ω -> 𝓜 -> @_c_statement S T ->  Ω -> 𝓜 -> Prop.
Definition Empty_exp_sem : @exp_sem_sig Empty_set := fun _ _ _  _ => False.
Definition Empty_stmt_sem : @stmt_sem_sig Empty_set Empty_set := fun _ _ _  _ _ _ _ => False.


(* extensible expression semantic *)
Inductive generic_exp_sem {T:Set} {ext_exp : @exp_sem_sig T} (env : Ω) (mem:𝓜): @_c_exp T -> 𝕍 -> Prop :=
| C_E_Int (z:Z) irz : env ⋅ mem |= z => Int.mkMI z irz
| C_E_Var (x:𝓥) z : 
    (fst env) x = Some (VInt z) -> 
    env ⋅ mem |=  (C_Id x C_Int) => z
| C_E_BinOpInt e e' (z z':Z) op z_ir z'_ir
    (H:Int.inRange (⋄ op z z')) :
    env ⋅ mem |= e =>  (Int.mkMI z z_ir) ->
    env ⋅ mem |= e' =>  (Int.mkMI z' z'_ir) ->
    env ⋅ mem |=  BinOpInt e op e' => Int.mkMI ((⋄ op) z z') H
| C_E_BinOpTrue e e' (z z' : Z) z_ir z'_ir op :
    env ⋅ mem |= e => (Int.mkMI z z_ir) ->
    env ⋅ mem |= e' => (Int.mkMI z' z'_ir) ->
    (◁ op) z z' = true ->
    env ⋅ mem |= BinOpBool e op e'  => one
| C_E_BinOpFalse e e' (z z' : Z) op z_ir z'_ir :
    env ⋅ mem |= e => (Int.mkMI z z_ir) -> 
    env ⋅ mem |= e' => (Int.mkMI z' z'_ir) -> 
    ((◁ op) z z' = false ) ->
    env ⋅ mem |= BinOpBool e op e' => zero
| C_Ext x v t: 
    (* external semantic only allowed for variables not holding a value of type int *)
    t <> C_Int ->
    ext_exp env mem (C_Id x t) v  ->
    env ⋅ mem |= (C_Id x t) => v

where  "Ω ⋅ M '|=' e => z" := (generic_exp_sem Ω M e z) : generic_sem_scope.

Definition c_exp_sem := @generic_exp_sem Empty_set Empty_exp_sem.

Notation "Ω |= e => v"  := (c_exp_sem Ω ⊥ e v) : c_sem_scope.

Open Scope mini_c_scope.

(* extensible statement semantic *)
Inductive generic_stmt_sem {S T: Set} {ext_exp: @exp_sem_sig T} {ext_stmt: @stmt_sem_sig S T} (funs:@𝓕 S T) (procs: @𝓟 S T) (env:Ω) (mem:𝓜) : @_c_statement S T -> Ω -> 𝓜 -> Prop := 
    | S_skip  :  (env ⋅ mem |= <{ skip }> => env ⋅ mem) funs procs
    | S_Assign x z (e : @_c_exp T) : 
        type_of_value ((fst env) x) = Some C_Int ->
        @generic_exp_sem T ext_exp env mem e z -> 
        (env ⋅ mem |= <{x = e}> => ((fst env){x\z},snd env) ⋅ mem) funs procs
    | S_IfTrue env' mem' z e s s' :
        @generic_exp_sem T ext_exp env mem e z /\ ~ (z = zero) ->
        (env ⋅ mem  |= s => env' ⋅ mem') funs procs ->
        (env ⋅ mem  |= <{ if e s else s'}> => env' ⋅ mem') funs procs
    | S_IfFalse env' mem' e s s' :
        @generic_exp_sem T ext_exp env mem e zero ->
        (env ⋅ mem |= s' => env' ⋅ mem') funs procs ->
        (env ⋅ mem |= <{ if e s else s'}> => env' ⋅ mem') funs procs
    | S_While e s   env' mem' :
        (env ⋅ mem |= <{ if e s ; while e s else skip }> =>  env' ⋅ mem') funs procs ->
        (env ⋅ mem |= <{ while e s }> =>  env' ⋅ mem') funs procs
    | S_Seq  env' mem' env'' mem'' s s' :
        (env ⋅ mem |= s => env' ⋅ mem') funs procs ->
        (env' ⋅ mem' |= s' => env'' ⋅ mem'') funs procs ->
        (env ⋅ mem |= <{ s ; s' }> =>  env'' ⋅ mem'') funs procs

    | S_FCall f (b: @_c_statement S T) (env' : Ω) mem' c xargs eargs (zargs : 𝕍 ⃰ ) resf z : 
        List.length xargs = List.length eargs ->
        funs f = Some (xargs,b) ->
        List.Forall2 (@generic_exp_sem T ext_exp env mem) eargs zargs ->
        (((p_map_addall ⊥ xargs zargs),⊥) ⋅ mem |= b => env' ⋅ mem') funs procs -> 
        ~ List.In resf (stmt_vars b) -> (**)
        (fst env') resf = Some z ->
        (env ⋅ mem |= (FCall c resf f eargs) => ((fst env){c\z},(snd env)) ⋅ mem') funs procs

    | S_PCall p b (env' : Ω) mem' xargs eargs zargs : 
        List.length xargs = List.length eargs ->
        procs p = Some (xargs,b) ->
        List.Forall2 (@generic_exp_sem T ext_exp env mem) eargs zargs ->
        (((p_map_addall ⊥ xargs zargs),⊥) ⋅ mem |= b => env'⋅ mem') funs procs ->
        (env ⋅ mem |= PCall p eargs => env ⋅ mem') funs procs

    | S_Return e z resf : 
        @generic_exp_sem T ext_exp env mem e z ->
        (env ⋅ mem |= <{ return e in resf }> =>  ((fst env){resf\z},snd env)⋅ mem) funs procs

    | S_PAssert  e z :
        @generic_exp_sem T ext_exp env mem e z -> z <>  zero ->
        (env ⋅ mem |= <{ assert e }> => env ⋅ mem) funs procs

    | S_ExtSem s env' mem' : 
        (* only S_Ext constructor allowed to use external semantic*)
        ext_stmt funs procs env mem (S_Ext s) env' mem' 
        -> (env ⋅ mem |= (S_Ext s) => env' ⋅ mem') funs procs
    
    where "Ω ⋅ M |= s => Ω' ⋅ M'"  := (fun funs procs => generic_stmt_sem funs procs Ω M s Ω' M') : generic_sem_scope.
    

    Definition c_stmt_sem := @generic_stmt_sem Empty_set Empty_set Empty_exp_sem Empty_stmt_sem.
    Notation "Ω ⋅ M |= s => Ω' ⋅ M'"  := (c_stmt_sem Ω M s Ω' M') : c_sem_scope.


Definition c_decl_sem (env env':Ω) (mem mem':𝓜) d : Prop := 
        forall x t u,
        (fst env) x  = None -> 
        (Uτ u) = Some t ->
        d = C_Decl t x -> env' = ((fst env){x\u},snd env) /\ mem = mem'.
        
Notation "Ω ⋅ M |= d => Ω' ⋅ M'"  := (c_decl_sem Ω Ω' M M' d) : mini_c_decl_scope.


Inductive _gmp_exp_sem (env : Ω) (mem:𝓜) : gmp_exp -> 𝕍 -> Prop :=
| GMP_E_Var (x:𝓥) (l:location) (z:mpz_val) : 
    (fst env) x = Some (VMpz l) -> 
    mem l = Some z ->
    _gmp_exp_sem env mem (C_Id x Mpz) (VMpz l)
.

Definition gmp_exp_sem := @generic_exp_sem _gmp_t _gmp_exp_sem.
Notation "Ω ⋅ M '|=' e => z" := (gmp_exp_sem Ω M e z) : gmp_sem_scope.


Open Scope gmp_sem_scope.
Open Scope mini_gmp_scope.

Inductive _gmp_stmt_sem { S T : Set }(funs : @𝓕 S T) (procs : @𝓟 S T) (env:Ω) (mem:𝓜) : gmp_statement -> Ω -> 𝓜 -> Prop := 
    | S_init x (l:location):
        fresh_location mem l ->
        (forall v, (fst env) v <> Some (VMpz (Some l))) ->
        (exists n, (fst env) x = Some (UMpz n))%type ->
        (env ⋅ mem |= <init(x)> => ((fst env){x\VMpz (Some l)}, snd env) ⋅ mem{l\Defined 0}) funs procs
    
    | S_clear x a z :   
        (fst env) x = Some (VMpz (Some a)) ->   
        (* added *)
        mem a = Some (Defined z) ->   
        (* cl is not deterministic unless the umpz value used is always the same *)
        (env ⋅ mem |= <cl(x)> => ((fst env){x\(VMpz None)}, snd env) ⋅ mem{a\Undefined z}) funs procs

    | S_set_i x y z a :  
        (fst env) x = Some (VMpz (Some a)) ->
        env ⋅ mem |= y => VInt z ->
        (env ⋅ mem |= <set_i(x,y)> => env ⋅ mem{a\Defined (z ̇)}) funs procs

    | S_set_z x y z (a n : location) :  
        (fst env) x = Some (VMpz a) ->
        (fst env) y = Some (VMpz n) ->
        mem n = Some z ->
        (env ⋅ mem |= <set_z(x,y)> => env ⋅ mem{a\z}) funs procs 

    | S_get_int x (y:id) z v (ir:Int.inRange z) :
        env ⋅ mem |= C_Id y Mpz => VMpz (Some v) ->
        mem v = Some (Defined z) -> 
        (env ⋅ mem |= <x = get_int(y)> => ((fst env){x\z ⁱⁿᵗ ir : 𝕍},(snd env)) ⋅ mem) funs procs

    | S_set_s s x z a :
        (fst env) x = Some (VMpz (Some a)) ->
        BinaryString.to_Z s = z ->
        (env ⋅ mem |= <set_s(x,s)> => env ⋅ mem{a\Defined z}) funs procs

    | S_cmp c x (vx vy :location) lx y ly (b:𝕍):
        env ⋅ mem |= C_Id x Mpz => vx ->
        env ⋅ mem |= C_Id y Mpz => vy ->
        mem vx = Some (Defined lx) ->
        mem vy = Some (Defined ly) ->
        (
            (Z.gt lx ly <-> b = one) /\
            (Z.lt lx ly <-> b = sub_one) /\
            (Z.eq lx ly <-> b = zero)
        ) ->
        (env ⋅ mem |= <c = cmp(x,y)> => ((fst env){c\b}, snd env) ⋅ mem) funs procs
    
    | S_op bop r lr x y (vx vy : location) z1 z2 :
        env ⋅ mem |= C_Id x Mpz => vx ->
        mem vx = Some (Defined z1) -> 
        env ⋅ mem |= C_Id y Mpz =>  vy ->
        mem vy = Some (Defined z2) -> 
        (fst env) r = Some (VMpz (Some lr)) ->
        (env ⋅ mem |= op bop r x y => env ⋅ mem{lr\Defined (⋄ (□ bop) z1 z2) }) funs procs

where "Ω ⋅ M |= s => Ω' ⋅ M'"  := (fun funs procs => _gmp_stmt_sem funs procs Ω M s Ω' M') : _gmp_stmt_sem_scope.


Definition gmp_stmt_sem := @generic_stmt_sem _gmp_statement _gmp_t _gmp_exp_sem _gmp_stmt_sem.
Notation "Ω ⋅ M |= s => Ω' ⋅ M'"  := (fun funs procs => gmp_stmt_sem funs procs Ω M s Ω' M') : gmp_sem_scope. 


Inductive fsl_term_sem (env:Ω) : ℨ -> Z -> Prop :=
| FSL_E_Int z : fsl_term_sem env (T_Z z) z 
| FSL_E_LVar x z : (snd env) x = Some z -> fsl_term_sem env (T_Id x) z
| FSL_E_Var x v : 
    (fst env) v = Some (VInt x) ->  
    fsl_term_sem env (T_Id v) x ̇

| FSL_E_BinOpInt t t' z zint z' z'int op :  
    fsl_term_sem env t z ->
    fsl_term_sem env t' z' ->
    ~ (op = FSL_Div /\ z = 0)%type ->
    fsl_term_sem env (T_BinOp t op t') ((fsl_binop_int_model op) zint z'int)

| FSL_E_CondTrue p t z t':
    fsl_pred_sem env p BTrue ->
    fsl_term_sem env t z ->
    fsl_term_sem env (T_Cond p t t') z

| FSL_E_CondFalse p t t' z':
    fsl_pred_sem env p BFalse ->
    fsl_term_sem env t' z' ->
    fsl_term_sem env (T_Cond p t t') z'

    with 

fsl_pred_sem (env:Ω) :  𝔅 -> 𝔹 -> Prop :=
| FP_True : fsl_pred_sem env P_True BTrue
| FP_False : fsl_pred_sem env P_False BFalse

| FP_BinOpTrue t t' z z' (op:fsl_binop_bool): 
    fsl_term_sem env t z ->
    fsl_term_sem env t' z' ->
    (fsl_binop_bool_model op) z z' ->
    fsl_pred_sem env (P_BinOp t op t) BTrue

| FP_BinOpFalse t t' z z' (op:fsl_binop_bool): 
    fsl_term_sem env t z ->
    fsl_term_sem env t' z' ->
    ~ (fsl_binop_bool_model op) z z' ->
    fsl_pred_sem env (P_BinOp t op t) BFalse

| FP_NotTrue p : 
    fsl_pred_sem env p BTrue ->
    fsl_pred_sem env (Not p) BFalse

| FP_NotFalse p : 
    fsl_pred_sem env p BFalse ->
    fsl_pred_sem env (Not p) BTrue 

| FP_DisjLeftTrue p p' : 
    fsl_pred_sem env p BTrue ->
    fsl_pred_sem env (Disj p p') BTrue 

| FP_DisjLeftFalse p p' z : 
    fsl_pred_sem env p BFalse ->
    fsl_pred_sem env p' z ->
    fsl_pred_sem env (Disj p p') z
.

Notation "Ω '|=' t => v" := (fsl_term_sem Ω t v) : fsl_sem_scope.

Inductive _fsl_assert_sem { S T : Set } (funs : @𝓕 S T) (procs : @𝓟 S T) (env : Ω) (mem:𝓜) : fsl_statement -> Ω -> 𝓜 -> Prop :=
| FSL_Assert (p:𝔅) : 
    fsl_pred_sem env p BTrue ->
    _fsl_assert_sem funs procs env mem (LAssert p) env mem
.

Definition fsl_stmt_sem := @generic_stmt_sem _fsl_statement _gmp_t gmp_exp_sem _fsl_assert_sem.
Notation "Ω ⋅ M |= s => Ω' ⋅ M'"  := (fun funs procs => fsl_stmt_sem funs procs Ω M s Ω' M') : fsl_sem_scope. 



(* macro semantic *)

Reserved Notation "Ω ⋅ M '|=' e ⇝ z" (M at next level, at level 70).
Inductive macro_sem (env : Ω) (mem:𝓜) (e:gmp_exp): Z -> Prop :=
| M_Int x :  
    gmp_exp_sem env mem e (VInt x) ->
    env ⋅ mem |= e ⇝ x ̇
| M_Mpz l z : 
    gmp_exp_sem env mem e (VMpz (Some l)) ->
    mem l = Some (Defined z) ->
    env ⋅ mem |= e ⇝ z
where "Ω ⋅ M '|=' e ⇝ z" := (macro_sem Ω M e z).


#[global] Hint Constructors _c_statement  : rac_hint.
#[global] Hint Constructors _c_exp  : rac_hint.
#[global] Hint Constructors _gmp_statement  : rac_hint.

#[global] Hint Constructors generic_exp_sem  : rac_hint.
#[global] Hint Constructors generic_stmt_sem  : rac_hint.

#[global] Hint Constructors _gmp_exp_sem  : rac_hint.
#[global] Hint Constructors _gmp_stmt_sem  : rac_hint.


#[global] Hint Constructors param_env_partial_order : rac_hint.
#[global] Hint Constructors macro_sem : rac_hint.


Close Scope generic_sem_scope.