From Coq Require Import Strings.String ZArith.ZArith BinaryString.

From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax MiniC.Semantics.

Import RecordSetNotations FunctionalEnv.

#[local] Open Scope utils_scope.
#[local] Open Scope mini_c_scope.
#[local] Open Scope Z_scope.

Inductive fsl_term_sem (f: fsl_prog_fenv) (ev:Env) : ℨ -> Z -> Prop :=
    | S_T_Int z : fsl_term_sem f ev (T_Z z) z 
    
    | S_T_LVar x z : ev.(binds) x = Some z -> fsl_term_sem f ev (T_Id x FSL_Integer) z

    | S_T_Var x v : ev.(env) v = Some (Def (VInt x)) ->  fsl_term_sem f ev (T_Id v FSL_Int) x ̇ 

    | S_T_BinOpInt t t' z zint z' z'int op :  
        fsl_term_sem f ev t z ->
        fsl_term_sem f ev t' z' ->
        ~ (op = FSL_Div /\ z = 0) ->
        fsl_term_sem f ev (T_BinOp t op t') ((fsl_binop_int_model op) zint z'int)

    | S_T_CondTrue p t z t':
        fsl_pred_sem f ev p BTrue ->
        fsl_term_sem f ev t z ->
        fsl_term_sem f ev (T_Cond p t t') z

    |S_T_CondFalse p t t' z':
        fsl_pred_sem f ev p BFalse ->
        fsl_term_sem f ev t' z' ->
        fsl_term_sem f ev (T_Cond p t t') z'

    | S_T_Call fname b targs zargs z :
        @generic_call_sem _ _ f _ _ _ _ (fsl_term_sem f) (fsl_term_sem f) lfuns (set env ∘ set binds) ev empty_env z fname targs zargs b ->
        fsl_term_sem f ev (T_Call fname targs) z 


with fsl_pred_sem (f: fsl_prog_fenv) (ev:Env) :  𝔅 -> 𝔹 -> Prop :=
    | S_P_True : fsl_pred_sem f ev P_True BTrue
    | S_P_False : fsl_pred_sem f ev P_False BFalse

    | S_P_BinOpTrue t t' z z' (op:fsl_binop_bool): 
        fsl_term_sem f ev t z ->
        fsl_term_sem f ev t' z' ->
        (fsl_binop_bool_model op) z z' ->
        fsl_pred_sem f ev (P_BinOp t op t) BTrue

    | S_P_BinOpFalse t t' z z' (op:fsl_binop_bool): 
        fsl_term_sem f ev t z ->
        fsl_term_sem f ev t' z' ->
        ~ (fsl_binop_bool_model op) z z' ->
        fsl_pred_sem f ev (P_BinOp t op t) BFalse

    | S_P_NotTrue p : 
        fsl_pred_sem f ev p BTrue ->
        fsl_pred_sem f ev (P_Not p) BFalse

    | S_P_NotFalse p : 
        fsl_pred_sem f ev p BFalse ->
        fsl_pred_sem f ev (P_Not p) BTrue 

    | S_P_DisjLeftTrue p p' : 
        fsl_pred_sem f ev p BTrue ->
        fsl_pred_sem f ev (P_Disj p p') BTrue 

    | S_P_DisjLeftFalse p p' z : 
        fsl_pred_sem f ev p BFalse ->
        fsl_pred_sem f ev p' z ->
        fsl_pred_sem f ev (P_Disj p p') z
    
    | S_P_Call p b targs zargs z :
        @generic_call_sem _ _ f _ _ _ _ (fsl_term_sem f) (fsl_pred_sem f) preds (set env ∘ set binds) ev empty_env z p targs zargs b ->
        fsl_pred_sem f ev (P_Call p targs) z 
.

#[global] Hint Constructors fsl_term_sem : rac_hint.
#[global] Hint Constructors fsl_pred_sem : rac_hint.


Declare Scope fsl_tsem_scope.
Delimit Scope fsl_tsem_scope with fsltsem.
Notation "Ω '|=' t => v" := (fun f => fsl_term_sem f Ω t v) : fsl_tsem_scope.


Declare Scope fsl_psem_scope.
Delimit Scope fsl_psem_scope with fslpsem.

Notation "Ω '|=' t => v" := (fun f => fsl_pred_sem f Ω t v) : fsl_psem_scope.

(* todo: custom induction principle *)



(* in the article, logical assert is part of mini-c but because we make mini_c extendable,
 the logical assert is now in fsl semantics *)
Inductive _fsl_assert_sem  (f : fenv ) (ev:Env) : fsl_statement -> Env -> Prop :=
| FSL_Assert (p:𝔅) : 
    fsl_pred_sem f ev p BTrue ->
    _fsl_assert_sem f ev (LAssert p) ev
.

#[global] Hint Constructors _fsl_assert_sem : rac_hint.


Definition fsl_stmt_sem := @generic_stmt_sem _fsl_statement Empty_set _fsl_assert_sem _fsl_stmt_vars.

Declare Scope fsl_sem_scope.
Delimit Scope fsl_sem_scope with fslsem.

Notation "ev |= s => ev'"  := (fun f => fsl_stmt_sem f ev s ev') : fsl_sem_scope.


Definition fsl_pgrm_sem := 
    @generic_pgrm_sem _fsl_routine _fsl_statement Empty_set _fsl_assert_sem _fsl_stmt_vars (fun _ => Void)  build_fsl_fenv    . 


