Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import ZArith.ZArith.
From Coq Require Import Strings.String.
Open Scope fsl_scope.
Open Scope Z_scope.
Open Scope mini_c_scope.


Inductive c_exp_sem (env : Ω) : c_exp -> Values -> Prop :=
| C_E_Int (z:Z) in_range: env ⊨ z => (Int.of_z z in_range)
| C_E_Var (x:V) z  : 
    (fst env)(x:string) = Some (Int z) -> 
    env ⊨ x => z
| C_E_BinOpInt e e' (z z':Z) op z_ir z'_ir 
    (H:Int.inRange (⋄ op z z')) :
    env ⊨ e =>  (Int.of_z z z_ir) ->
    env ⊨ e' =>  (Int.of_z z' z'_ir) ->
    env ⊨ BinOpInt e op e' => Int.of_z ((⋄ op) z z') H
| C_E_BinOpTrue e e' (z z' : Z) z_ir z'_ir op :
    env ⊨ e => (Int.of_z z z_ir) ->
    env ⊨ e' => (Int.of_z z z'_ir) ->
    ((◁ op) z z' -> True) ->
    env ⊨ BinOpBool e op e' => Int.of_z 1 oneinRange
| C_E_BinOpFalse e e' (z z' : Z) op z_ir z'_ir :
    env ⊨ e => (Int.of_z z z_ir) -> 
    env ⊨ e' => (Int.of_z z' z'_ir) -> 
    ((◁ op) z z' -> False) ->
    env ⊨ BinOpBool e op e' => Int.of_z 0 zeroinRange

where  "Ω '⊨' e => v" := (c_exp_sem Ω e v).


Inductive c_decl_sem (env:Ω) (mem:M) : c_decl -> Ω -> M -> Prop := 
    | Decl t x (u:Values) : 
        (* v x = ⊥ -> (env,mem ⊨ C_Decl t x => (v{x\u},l),mem) *)
        c_decl_sem  env mem (C_Decl t x) ((fst env){x\u}, snd env) mem 
  (* where 
  "Ω ',' M '⊨' d '=>' Ω' ',' M'" := (c_decl_sem d Ω M Ω' M')  *)
.


Inductive c_stmt_sem (env:Ω) (mem:M) : S -> Ω -> M -> Prop := 
    | S_skip  : c_stmt_sem env mem <{ skip }> env mem
    | S_Assign x z e : 
        (* in v x Int + Uint  *)
        env ⊨ e => z ->
        c_stmt_sem  env mem <{x := e}> ((fst env){x\z},snd env) mem
    | S_IfTrue env' mem' z e s s' :
        env ⊨ e => z ->
        z <>  Int.of_z 0 zeroinRange ->
        c_stmt_sem env mem s  env' mem' ->
        c_stmt_sem  env mem <{ if (e) s else s' }> env' mem' 
    | S_IfFalse env' mem' z e s s' :
        env ⊨ e => z ->
        z = Int.of_z 0 zeroinRange ->
        c_stmt_sem  env mem s' env' mem' ->
        c_stmt_sem  env mem <{ if (e) s else s' }> env' mem' 
    | S_While e s   env' mem' :
        c_stmt_sem  env mem (If e (Seq s (While e s)) Skip) env' mem' ->
        c_stmt_sem  env mem <{ while (e) s }> env' mem' 
    | S_Seq  env' mem' env'' mem'' s s' :
        c_stmt_sem  env mem s env' mem' -> 
        c_stmt_sem  env' mem' s' env'' mem'' ->
        c_stmt_sem env mem <{ s ; s' }>  env'' mem''
    | S_Assert  e z :
        env ⊨ e => z -> z <>  Int.of_z 0 zeroinRange ->
        c_stmt_sem env mem <{ assert (e) }> env mem

 (* where "Ω ',' M '⊨' s '=>' Ω' ',' M'" := (c_stmt_sem s Ω M Ω' M') *)
    .

(* TODO: finish mini-fsl semantic *)

Inductive fsl_term_sem (env:Ω) : LT -> Values -> Prop :=
| FSL_E_Int z : fsl_term_sem env z UMpz
| FSL_E_LVar x z : (snd env) x = Some z -> fsl_term_sem env x UMpz
| FSL_E_Var x v : (fst env) v = Some x ->  fsl_term_sem env v x
(* | FSL_E_BinOpInt t t' z zint z' z'int op :  
    values_int z = Some (Int zint) ->
    values_int z' = Some (Int z'int) ->
    fsl_term_sem env t z ->
    fsl_term_sem env t' z' ->
    ~ (op = FSL_Div /\ zint = (Int (Int.mkMI 0 zeroinRange))) ->
    fsl_term_sem env (T_BinOp t op t') ((fsl_binop_int_model op) zint z'int) *)
.


(* Inductive fsl_pred_sem : B -> Ω -> M -> Ω -> M -> Prop :=
| none
. *)

(* 
Inductive fsl_assert_sem : S -> Ω -> M -> Ω -> M -> Prop := 
| P_Assert env mem p :  env ⊨ p => Int.of_z 1 oneinRange -> 
    fsl_assert_sem (LAssert p) env mem env mem
. *)
