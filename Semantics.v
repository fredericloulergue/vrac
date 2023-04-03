Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import ZArith.ZArith.
From Coq Require Import Strings.String.

Open Scope mini_c_scope.


Declare Scope mini_c_exp_scope.

Inductive c_exp_sem (env : Ω) : c_exp -> 𝕍 -> Prop :=
| C_E_Int (z:Z) irz : env |= z => Int.mkMI z irz
| C_E_Var (x:𝓥) z  : 
    (fst env)(x:string) = Some (VInt z) -> 
    env |= x => z
| C_E_BinOpInt e e' (z z':Z) op z_ir z'_ir 
    (H:Int.inRange (⋄ op z z')) :
    env |= e =>  (Int.mkMI z z_ir) ->
    env |= e' =>  (Int.mkMI z' z'_ir) ->
    env |= BinOpInt e op e' => Int.mkMI ((⋄ op) z z') H
| C_E_BinOpTrue e e' (z z' : Z) z_ir z'_ir op :
    env |= e => (Int.mkMI z z_ir) ->
    env |= e' => (Int.mkMI z' z'_ir) ->
    (◁ op) z z' = true ->
    env |= BinOpBool e op e' => one
| C_E_BinOpFalse e e' (z z' : Z) op z_ir z'_ir :
    env |= e => (Int.mkMI z z_ir) -> 
    env |= e' => (Int.mkMI z' z'_ir) -> 
    ((◁ op) z z' = false ) ->
    env |= BinOpBool e op e' => zero

where  "Ω '|=' e => v" := (c_exp_sem Ω e v) : mini_c_exp_scope.

Declare Scope mini_c_decl_scope.
Definition c_decl_sem (env env':Ω) (mem mem':𝓜) d : Prop := 
        forall x t u,
        (fst env) x  = None -> 
        (Uτ u) = Some t ->
        d = C_Decl t x -> env' = ((fst env){x\u},snd env) /\ mem = mem'.
        
Notation "Ω ⋅ M |= d => Ω' ⋅ M'"  := (c_decl_sem Ω Ω' M M' d) : mini_c_decl_scope.


Open Scope mini_c_exp_scope.
Declare Scope mini_c_stmt_scope.

Inductive c_stmt_sem (env:Ω) (mem:𝓜) : 𝐒 -> Ω -> 𝓜 -> Prop := 
    | S_skip  :  env ⋅ mem |= <{ skip }> => env ⋅ mem
    | S_Assign x z e : 
        type_of_value ((fst env) x) = Some C_Int ->
        env |= e => z ->
        env ⋅ mem |= <{x = e}> => ((fst env){x\z},snd env) ⋅ mem
    | S_IfTrue env' mem' z e s s' :
        env |= e => z ->
        z <>  Int.mkMI 0 zeroinRange ->
        env ⋅ mem  |= s => env' ⋅ mem' ->
        env ⋅ mem  |= <{ if e s else s'}> => env' ⋅ mem'
    | S_IfFalse env' mem' z e s s' :
        env |= e => z ->
        z = Int.mkMI 0 zeroinRange ->
        env ⋅ mem |= s' => env' ⋅ mem' ->
        env ⋅ mem |= <{ if e s else s'}> => env' ⋅ mem'
    | S_While e s   env' mem' :
         env ⋅ mem |= <{ if e s ; while e s else skip }> =>  env' ⋅ mem' ->
         env ⋅ mem |= <{ while e s }> =>  env' ⋅ mem' 
    | S_Seq  env' mem' env'' mem'' s s' :
        env ⋅ mem |= s => env' ⋅ mem' ->
        env' ⋅ mem' |= s' => env'' ⋅ mem''->
        env ⋅ mem |= <{ s ; s' }> =>  env'' ⋅ mem'' 

    | S_FCall (funs:𝓕) f b env' mem' c xargs eargs zargs resf z n : 
        List.length xargs = n /\ List.length eargs = n /\ List.length zargs = n ->
        funs f = Some (xargs,b) ->
        List.Forall2 (fun e z => env |= e => z) eargs zargs ->
         ((p_map_addall ⊥ xargs zargs),⊥) ⋅ mem |= b => env' ⋅ mem' ->
        (fst env') resf = Some z ->
         env ⋅ mem |= (FCall c f eargs) => ((fst env){c\z},(snd env)) ⋅ mem'

    | S_PCall (procs:𝓟) p b env' mem' xargs eargs zargs n : 
        List.length xargs = n /\ List.length eargs = n /\ List.length zargs = n ->
        procs p = Some (xargs,b) ->
        List.Forall2 (fun e z => env |= e => z) eargs zargs  ->
        ((p_map_addall ⊥ xargs zargs),⊥) ⋅ mem |= b => env'⋅ mem' ->
        env ⋅ mem |= PCall p eargs => env ⋅ mem'

    | S_Return e z resf : 
         env |= e => z -> 
         env ⋅ mem |= <{ return e }> =>  ((fst env){resf\z},snd env)⋅ mem

    | S_PAssert  e z :
        env |= e => z -> z <>  zero ->
        env ⋅ mem |= <{ assert e }> => env ⋅ mem 

    (* | S_LAssert p :
        env |= p => one -> (* must be fsl *)
        c_stmt_sem env mem <{ /*@ assert p */ }> env mem *)

where "Ω ⋅ M |= s => Ω' ⋅ M'"  := (c_stmt_sem Ω M s Ω' M') : mini_c_stmt_scope.



(* TODO: finish mini-fsl semantic *)

Inductive fsl_term_sem (env:Ω) : ℨ -> 𝕍 -> Prop :=
| FSL_E_Int z : fsl_term_sem env z UMpz
| FSL_E_LVar x z : (snd env) x = Some z -> fsl_term_sem env x UMpz
| FSL_E_Var x v : (fst env) v = Some x ->  fsl_term_sem env v x
(* | FSL_E_BinOpInt t t' z zint z' z'int op :  
    values_int z = Some (Int zint) ->
    values_int z' = Some (Int z'int) ->
    fsl_term_sem env t z ->
    fsl_term_sem env t' z' ->
    , (op = FSL_Div /\ zint = (Int (mkMI 0 zeroinRange))) ->
    fsl_term_sem env (T_BinOp t op t') ((fsl_binop_int_model op) zint z'int) *)
.

(* Inductive fsl_pred_sem : B -> Ω -> M -> Ω -> M -> Prop :=
| none
. *)

(* 
Inductive fsl_assert_sem : S -> Ω -> M -> Ω -> M -> Prop := 
| P_Assert env mem p :  env |= p => mkMI 1 oneinRange -> 
    fsl_assert_sem (LAssert p) env mem env mem
. *)


(* todo GMP semantics *)
