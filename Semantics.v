Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import ZArith.ZArith.
From Coq Require Import Strings.String.
Open Scope fsl_scope.
Open Scope Z_scope.


Inductive c_exp_sem : c_exp -> Ω -> Values -> Prop :=
| E_Int (z:Z) env in_range: env ⊨ z =>  (Int.of_z z in_range)
| E_Var (x:V) z (env:Ω) : 
    (fst env)(x:string) = Some (Int z) -> 
    env ⊨ x => z
| E_BinOpInt env e e' (z z':Z) op z_ir z'_ir 
    (H:Int.inRange (⋄ op z z')) :
    env ⊨ e =>  (Int.of_z z z_ir) ->
    env ⊨ e' =>  (Int.of_z z' z'_ir) ->
    env ⊨ BinOpInt e op e' => Int.of_z ((⋄ op) z z') H
| E_BinOpTrue env e e' (z z' : Z) z_ir z'_ir op :
    env ⊨ e => (Int.of_z z z_ir) ->
    env ⊨ e' => (Int.of_z z z'_ir) ->
    ((◁ op) z z' = True) ->
    env ⊨ BinOpBool e op e' => Int.of_z 1 oneinRange
| E_BinOpFalse env e e' (z z' : Z) op z_ir z'_ir :
    env ⊨ e => (Int.of_z z z_ir) -> 
    env ⊨ e' => (Int.of_z z' z'_ir) -> 
    ((◁ op) z z' = False) ->
    env ⊨ BinOpBool e op e' => Int.of_z 0 zeroinRange

where  "Ω '⊨' e => v" := (c_exp_sem e Ω v).


Inductive c_decl_sem : c_decl -> Ω -> M -> Ω -> M -> Prop := 
    | Decl (env:Ω) (v := fst env) (l := snd env) mem t x (u:Values) : 
        (* v x = ⊥ -> (env,mem ⊨ C_Decl t x => (v{x\u},l),mem) *)
        c_decl_sem (C_Decl t x) env mem (v{x\u}, l) mem 
  (* where 
  "Ω ',' M '⊨' d '=>' Ω' ',' M'" := (c_decl_sem d Ω M Ω' M')  *)
.


Inductive c_stmt_sem : S -> Ω -> M -> Ω -> M -> Prop := 
    | S_skip env mem : c_stmt_sem Skip env mem env mem
    | S_Assign (env:Ω) (v:= fst env) (l:= snd env) mem x z e : 
        (* in v x Int + Uint  *)
        env ⊨ e => z ->
        c_stmt_sem (Assign x e) env mem (v{x\z},l) mem
    | S_IfTrue (env env':Ω) mem mem' z e s s' :
        env ⊨ e => z ->
        z <>  Int.of_z 0 zeroinRange ->
        c_stmt_sem s env mem env' mem' ->
        c_stmt_sem (If e s s') env mem env' mem' 
    | S_IfFalse (env env':Ω) mem mem' z e s s' :
        env ⊨ e => z ->
        z = Int.of_z 0 zeroinRange ->
        c_stmt_sem s' env mem env' mem' ->
        c_stmt_sem (If e s s') env mem env' mem' 
    | S_While e s env mem env' mem' :
        c_stmt_sem (If e (Seq s (While e s)) Skip) env mem env' mem' ->
        c_stmt_sem (While e s) env mem env' mem' 
    | S_Seq env mem env' mem' env'' mem'' s s' :
        c_stmt_sem s env mem env' mem' -> 
        c_stmt_sem s' env' mem' env'' mem'' ->
        c_stmt_sem (Seq s s') env mem env'' mem''
    | S_Assert env mem e z :
        env ⊨ e => z -> z <>  Int.of_z 0 zeroinRange ->
        c_stmt_sem (PAssert e) env mem env mem

 (* where "Ω ',' M '⊨' s '=>' Ω' ',' M'" := (c_stmt_sem s Ω M Ω' M') *)
    .

(* TODO: mini-fsl *)