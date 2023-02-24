Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import ZArith.ZArith.
Open Scope fsl_scope.
Open Scope Z_scope.


Inductive mini_c_exp_sem : mini_c_exp -> Ω -> Values ->  Prop :=
| E_Int z env : env ⊨ (Zm z) => VInt (FSLZ z)
| E_Var (x:V) z (env:Ω) : 
    (fst env)(x) = Some z -> env ⊨ Id x => z
| E_BinOpInt env e e' z z' op :
    env ⊨ e => VInt (FSLZ z) ->
    env ⊨ e' => VInt (FSLZ z') ->
    m_int <= (⋄ op) z z' <= M_int ->
    env ⊨ BinOpInt  (Zm z) op (Zm z) => VInt (FSLZ ((⋄ op) z z'))
| E_BinOpTrue env e e' z z' op :
    env ⊨ e => VInt (FSLZ z) ->
    env ⊨ e' => VInt (FSLZ z') ->
    ((◁ op) z z' = True) ->
    env ⊨ BinOpBool (Zm z) op (Zm z) => VInt (FSLZ 1)
| E_BinOpFalse env e e' z z' op :
    env ⊨ e => VInt (FSLZ z) ->
    env ⊨ e' => VInt (FSLZ z') ->
    ((◁ op) z z' = False) ->
    env ⊨ BinOpBool (Zm z) op (Zm z) => VInt (FSLZ 0)

where  "Ω '⊨' e => v" := (mini_c_exp_sem e Ω v).


Inductive mini_c_decl_sem : p_decl -> Ω -> p_decl -> Ω -> p_decl -> Prop := 
    | Decl (env:Ω) (v := fst env) (l := snd env) mem t x (u:Values) : 
        v x = ⊥ -> 
        (* (env,mem ⊨ PDecl t x => (v{x\u},l),mem) *)
        mini_c_decl_sem (PDecl t x) env mem (v{x\u}, l) mem
  (* where 
  "Ω ',' M '⊨' d '=>' Ω' ',' M'" := (mini_c_decl_sem d Ω M Ω' M')  *)
.


Inductive mini_c_stmt_sem : S -> Ω -> M -> Ω -> M -> Prop := 
    | S_skip env mem : mini_c_stmt_sem Skip env mem env mem
    | S_Assign (env:Ω) (v:= fst env) (l:= snd env) mem x z e : 
        (* in v x Int + Uint  *)
        env ⊨ e => z ->
        mini_c_stmt_sem (Assign x e) env mem (v{x\z},l) mem
    | S_IfTrue (env env':Ω) mem mem' z e s s' :
        env ⊨ e => z ->
        z <> VInt (FSLZ 0) ->
        mini_c_stmt_sem s env mem env' mem' ->
        mini_c_stmt_sem (If e s s') env mem env' mem' 
    | S_IfFalse (env env':Ω) mem mem' z e s s' :
        env ⊨ e => z ->
        z = VInt (FSLZ 0) ->
        mini_c_stmt_sem s' env mem env' mem' ->
        mini_c_stmt_sem (If e s s') env mem env' mem' 
    | S_While e s env mem env' mem' :
        mini_c_stmt_sem (If e (Seq s (While e s)) Skip) env mem env' mem' ->
        mini_c_stmt_sem (While e s) env mem env' mem' 
    | S_Seq env mem env' mem' env'' mem'' s s' :
        mini_c_stmt_sem s env mem env' mem' -> 
        mini_c_stmt_sem s' env' mem' env'' mem'' ->
        mini_c_stmt_sem (Seq s s') env mem env'' mem''
    | S_Assert env mem e z :
        env ⊨ e => z -> z <> VInt (FSLZ 0) ->
        mini_c_stmt_sem (PAssert e) env mem env mem


 where "Ω ',' M '⊨' s '=>' Ω' ',' M'" := (mini_c_stmt_sem s Ω M Ω' M')
    .

(* TODO: mini-fsl *)