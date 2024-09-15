From Coq Require Import ZArith.ZArith String.
From RAC Require Import Utils.
From RAC.Languages Require Import MiniC.Syntax MiniGMP.Syntax.


Inductive fsl_type := FSL_Int (* machine integer *) | FSL_Integer. (* mathematical integer *)

Inductive fsl_binop_bool :=  FSL_Lt | FSL_Le | FSL_Gt | FSL_Ge | FSL_Eq | FSL_NEq.
Definition fsl_binop_bool_model (x:fsl_binop_bool) : Z -> Z -> Prop := match x with
    | FSL_Lt => Z.lt
    | FSL_Le => Z.le
    | FSL_Gt => Z.gt
    | FSL_Ge => Z.ge
    | FSL_Eq => Z.eq
    | FSL_NEq => fun x y => ~(Z.eq x y)
end.

Inductive fsl_binop_int := FSL_Add | FSL_Sub  | FSL_Mul  | FSL_Div.
Definition fsl_binop_int_model (x:fsl_binop_int) : Z -> Z -> Z := match x with
    | FSL_Add => Z.add
    | FSL_Sub => Z.sub
    | FSL_Mul => Z.mul
    | FSL_Div => Z.div
end.


Inductive fsl_decl : Set :=  FSL_Decl (τ:gmp_t) (name:id). (* logic declaration δ *)

Inductive predicate : Set :=
    | P_True | P_False (* truth values *)
    | P_BinOp (lt: fsl_term) (op:fsl_binop_bool) (rt : fsl_term)
    | P_Not (t:predicate)
    | P_Disj (lp:predicate) (rp:predicate)  (* disjunction *)
    | P_Call (name:string) (args:fsl_term*) (* predicate call *)
with fsl_term :=
    | T_Z (z:Z) :> fsl_term (* integer in Z *)
    | T_Id (name:id) (ty:fsl_type)  (* variable access, ty added to distinguish between program var and logic var *)
    | T_BinOp (lt : fsl_term) (op:fsl_binop_int) (rt : fsl_term)
    | T_Cond (cond:predicate) (_then:fsl_term) (_else:fsl_term) (* conditional term *)
    | T_Call (name:string) (args:fsl_term*) (* logic function call *)
.

Notation 𝔅 := predicate. (* predicates *)
Notation ℨ := fsl_term. (* logical terms *)


Definition 𝔉 : Type := StringMap.t (𝔏* ⨉ ℨ). (* logic functions *)
Definition 𝔓 : Type := StringMap.t (𝔏* ⨉  𝔅). (* predicates *)


Inductive _fsl_statement : Set := LAssert (p:predicate). (* logic assertion *)


Coercion fsl_binop_int_to_c (x:fsl_binop_int) : c_binop_int := match x with
    | FSL_Add => C_Add
    | FSL_Sub => C_Sub
    | FSL_Mul => C_Mul
    | FSL_Div => C_Div
end.
Notation "□" := fsl_binop_int_to_c.

Coercion fsl_binop_bool_to_c (x:fsl_binop_bool) : c_binop_bool := match x with
    | FSL_Lt => C_Lt
    | FSL_Le => C_Le 
    | FSL_Gt => C_Gt
    | FSL_Ge => C_Ge
    | FSL_Eq => C_Eq 
    | FSL_NEq => C_NEq
end.
Notation "◖" := fsl_binop_bool_to_c.

Inductive _fsl_routine : Set :=
| LFun (ret:fsl_type) (name:id) (args:fsl_decl*) (body:fsl_term) (* logic function *)
| Predicate (name:id) (args:fsl_decl*) (p:predicate) (* predicate *)
.

Definition fsl_routine := @_c_routine _fsl_routine _fsl_statement Empty_set.


Definition fsl_to_gmp_op (x:fsl_binop_int) :  id -> id -> id -> _gmp_statement  :=
match x with
| FSL_Add => GMP_Add
| FSL_Sub => GMP_Sub
| FSL_Mul => GMP_Mul
| FSL_Div => GMP_Div
end.

(***** Printing *****)

Notation "'/*@' 'logic' k id '(' x ',' .. ',' y ')' '=' t '*/'" := (F_Ext (LFun k id (cons x .. (cons y nil) ..) t)) (in custom c_decl at level 0): mini_c_scope.
Notation "'/*@' 'predicate' id '(' x ',' .. ',' y ')' '=' p '*/'" := (F_Ext (Predicate id (cons x .. (cons y nil) ..) p)) (p custom c_stmt, in custom c_decl at level 0): mini_c_scope.
Notation "'/*@' 'assert' p '*/'" := (S_Ext (LAssert p)) (in custom c_stmt at level 0) : mini_c_scope.