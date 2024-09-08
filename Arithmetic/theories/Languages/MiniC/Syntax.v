From Coq Require Import ZArith.ZArith Strings.String.
From RAC Require Import Utils.


Open Scope Z_scope.

Import FunctionalEnv.

Inductive _c_type {T:Set} := C_Int | Void | T_Ext (t:T).  (* program types τc *)

Inductive c_binop_bool :=  C_Lt | C_Le | C_Gt | C_Ge | C_Eq | C_NEq.
Definition c_binop_bool_model (x:c_binop_bool) : Z -> Z -> bool := match x with
    | C_Lt => Z.ltb
    | C_Le => Z.leb
    | C_Gt => Z.gtb
    | C_Ge => Z.geb
    | C_Eq => Z.eqb
    | C_NEq => fun b1 b2 => negb (b1 =? b2)
end.
Notation "◁" := c_binop_bool_model.

Inductive c_binop_int := C_Add | C_Sub | C_Mul | C_Div. 
Definition c_binop_int_model (x:c_binop_int) : Z -> Z -> Z := match x with
    | C_Add => Z.add
    | C_Sub => Z.sub
    | C_Mul => Z.mul
    | C_Div => Z.div
end.
Notation "⋄" := c_binop_int_model.

#[warnings="-uniform-inheritance"] 
Inductive _c_exp {T : Set}  :=
    | Zm (z : Z) :> _c_exp(* machine integer *) (* can only be of type int *)
    | C_Id (var : id) (ty : @_c_type T) (* variable access *) (* can be either int or mpz *)
    | BinOpInt (le : _c_exp) (op:c_binop_int) (re : _c_exp) (* can only be of type int *)
    | BinOpBool (le : _c_exp) (op:c_binop_bool) (re : _c_exp) (* can only be of type int *)
.
#[global] Hint Constructors _c_exp  : rac_hint.


#[warnings="-uniform-inheritance"] 
Inductive _c_statement {S T : Set} :=
    | Skip (* empty statement *)
    | Assign (var:id) (e: @_c_exp T) (* assignment *)
    | FCall (var:id) (fname:string) (args: @_c_exp T*) (* function call *)
    | PCall  (fname:string) (args: @_c_exp T*) (* procedure call *)
    | Seq (s1 : _c_statement) (s2 : _c_statement) (* sequence *)
    | If (cond:@_c_exp T) (_then:_c_statement) (_else:_c_statement) (* conditional *)
    | While (cond:@_c_exp T) (body:_c_statement) (* loop *) 
    | PAssert (e:@_c_exp T) (* program assertion *)
    | Return (e:@_c_exp T) 
    (* | Decl (d: @_c_decl T) :> _c_statement *)
    | S_Ext (stmt:S)
.
#[global] Hint Constructors _c_statement  : rac_hint.


Definition 𝓕 {S T : Set} := 𝓥 ⇀ (𝓥 * ⨉ @_c_statement S T). (* program functions *)
Definition 𝓟 {S T : Set} := 𝓥 ⇀ (𝓥 * ⨉ @_c_statement S T). (* program procedures *)



Inductive _c_decl {T:Set} :=  C_Decl (type: @_c_type T) (name:id). (* program declaration *)

Inductive _c_routine {F S T : Set} :=
| PFun (rtype: @_c_type T) (name:id) (args: @_c_decl T*) (b_decl: @_c_decl T*) (body: @_c_statement S T) (* program function *)
| F_Ext (f:F)
.

Definition _c_program {F S T : Set} : Type := @_c_decl T* ⨉ @_c_routine F S T*. 

Definition c_exp := @_c_exp Empty_set.


(***** Printing *****)

Declare Scope mini_c_scope.
Delimit Scope mini_c_scope with c.
Declare Custom Entry c_decl.
Declare Custom Entry c_stmt.
Declare Custom Entry c_exp.
Declare Custom Entry c_type.
Declare Custom Entry c_args.


Notation "<[ d ]>" := d (at level 0, d custom c_decl at level 99, format "<[ d ]>") : mini_c_scope.    
Notation "<{ s }>" := s (at level 0, s custom c_stmt at level 99, format "<{ s }>") : mini_c_scope.
Notation "( x )" := x (in custom c_exp, x at level 99) : mini_c_scope.

Notation " 'int' " := C_Int (in custom c_type) : mini_c_scope.
Notation " 'void' " := Void (in custom c_type) : mini_c_scope.
Notation "e" := e (in custom c_exp at level 0,  e constr at level 0) : mini_c_scope.
Notation "s" := s (in custom c_stmt at level 0, s constr at level 0) : mini_c_scope.
Notation "d" := d ( in custom c_decl at level 0, d constr at level 0) : mini_c_scope.

Notation "'(' x ',' .. ',' y ')'" := (cons x .. (cons y nil) ..) (in custom c_args at level 0, x custom c_exp, y custom c_exp) : mini_c_scope.

Notation "t id" := (C_Decl t id) (in custom c_decl at level 99, t custom c_type, id constr) : mini_c_scope.
Notation "'fun' t id '(' x ',' .. ',' y ')' '[' x' .. y' ';' s ']'" := (PFun t id (cons x .. (cons y nil) ..) (cons x' .. (cons y' nil) ..) s)
    (in custom c_decl at level 80, id at level 0, t custom c_type, s custom c_stmt, x custom c_decl, y custom c_decl, x' custom c_decl, y' custom c_decl) : mini_c_scope.


Notation "x + y"   := (BinOpInt x C_Add y) (in custom c_exp at level 50, left associativity) : mini_c_scope.
Notation "x - y"   := (BinOpInt x C_Sub y) (in custom c_exp at level 50, left associativity) : mini_c_scope.
Notation "x * y"   := (BinOpInt x C_Mul y) (in custom c_exp at level 40, left associativity) : mini_c_scope.
Notation "x / y"   := (BinOpInt x C_Div y) (in custom c_exp at level 40, left associativity) : mini_c_scope.
Notation "x == y"  := (BinOpBool x C_Eq y) (in custom c_exp at level 50, no associativity) : mini_c_scope.
Notation "x != y"  := (BinOpBool x C_NEq y) (in custom c_exp at level 50, no associativity) : mini_c_scope.
Notation "x < y"   := (BinOpBool x C_Lt y) (in custom c_exp at level 50, no associativity) : mini_c_scope.
Notation "x <= y"  := (BinOpBool x C_Le y) (in custom c_exp at level 50, no associativity) : mini_c_scope.
Notation "x > y"   := (BinOpBool x C_Gt y) (in custom c_exp at level 50, no associativity) : mini_c_scope.
Notation "x >= y"  := (BinOpBool x C_Ge y) (in custom c_exp at level 50, no associativity) : mini_c_scope.


Notation "'skip'" := Skip  (in custom c_stmt at level 99) : mini_c_scope.
Notation "'if' cond _then 'else' _else " := (If cond _then _else) 
    (in custom c_stmt at level 89, cond custom c_exp at level 99, _then custom c_stmt at level 99, _else custom c_stmt at level 99
    , format "'if'  cond '//' '[v '  _then ']' '//' 'else' '//' '[v '  _else ']'") : mini_c_scope.
Notation "s1 ';' s2" := (Seq s1 s2) (in custom c_stmt at level 90, right associativity, format "s1 ; '//' s2") : mini_c_scope.
Notation "x = y" := (Assign x y) (in custom c_stmt at level 0, x constr at level 0, y custom c_exp at level 85, no associativity) : mini_c_scope.
Notation "'assert' e" := (PAssert e) (in custom c_stmt at level 0, e custom c_exp at level 99) : mini_c_scope.
Notation "'while' e s" := (While e s) (in custom c_stmt at level 89, e custom c_exp at level 99, s at level 99) : mini_c_scope.
Notation "'return' e" := (Return e) (in custom c_stmt at level 0, e custom c_exp at level 99) : mini_c_scope.

Notation "f args" := (PCall f args) (in custom c_stmt at level 99, args custom c_args) : mini_c_scope.
Notation "c '<-' f args" := (FCall c f args) (in custom c_stmt at level 80, f at next level, args custom c_args) : mini_c_scope.