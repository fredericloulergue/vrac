From Coq Require Import ZArith.ZArith Strings.String.
From RAC Require Import Utils.



#[local] Open Scope Z_scope.

Import StringMap.

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

Section GenericSyntax.

    Context {F S T : Set} {Tdec : EqDec T}.
    

    Inductive c_type := C_Int | Void | T_Ext (t:T).  (* program types τc *)

    Equations Derive NoConfusion for c_type.
    Equations Derive EqDec for c_type.

    #[warnings="-uniform-inheritance"] 
    Inductive c_exp : Set :=
        | Zm (z : Z) :> c_exp (* machine integer *) (* can only be of type int *)
        | C_Id (var : id) (ty : @c_type) (* variable access *) (* can be either int or mpz *)
        | BinOpInt (le : c_exp) (op:c_binop_int) (re : c_exp) (* can only be of type int *)
        | BinOpBool (le : c_exp) (op:c_binop_bool) (re : c_exp) (* can only be of type int *)
    .


    Inductive c_decl :=  C_Decl (type: c_type) (name:id). (* program declaration *)

    (* Equations Derive NoConfusion for c_decl.
    Equations Derive EqDec for c_decl.
    Final Obligation. unfold dec_eq. repeat decide equality. Defined.  *)


    #[warnings="-uniform-inheritance"] 
    Inductive c_statement : Set :=
        | Skip (* empty statement *)
        | Assign (var:id) (e: c_exp) (* assignment *)
        | FCall (var:id) (fname:string) (args: c_exp★) (* function call *)
        | PCall  (fname:string) (args: c_exp★) (* procedure call *)
        | Seq (s1 : c_statement) (s2 : c_statement) (* sequence *)
        | If (cond:c_exp) (_then:c_statement) (_else:c_statement) (* conditional *)
        | While (cond:c_exp) (body:c_statement) (* loop *) 
        | PAssert (e: c_exp) (* program assertion *)
        | Return (e: c_exp) 
        | S_Ext (stmt:S)
    

        (* 
            simplified scope added ( only allow declarations at the start of the scope )
            because the translation creates a scope per translated assertion within which lies 
            the assertion and its required declarations. 
        *)
        (* | Decl (d: c_decl) *)
        | Scope (decls: list c_decl) (s: c_statement) 

    .


    Definition 𝓕 : Type := StringMap.t (𝓥★ ⨉ c_statement). (* program functions *)
    Definition 𝓟 : Type := StringMap.t (𝓥★ ⨉ c_statement). (* program procedures *)


    Inductive c_routine :=
    | PFun (rtype: c_type) (name:id) (args: c_decl★) (b_decl: c_decl★) (body: c_statement) (* program function *)
    | F_Ext (f:F)
    .

    Definition c_program : Type := c_decl★ ⨉ c_routine★. 

End GenericSyntax.


#[global] Hint Constructors c_exp  : rac_hint.
#[global] Hint Constructors c_statement  : rac_hint.


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
Notation "x := y" := (Assign x y) (in custom c_stmt at level 0, x constr at level 0, y custom c_exp at level 85, no associativity, only printing) : mini_c_scope.
Notation "'assert' e" := (PAssert e) (in custom c_stmt at level 0, e custom c_exp at level 99) : mini_c_scope.
Notation "'while' e s" := (While e s) (in custom c_stmt at level 89, e custom c_exp at level 99, s at level 99) : mini_c_scope.
Notation "'return' e" := (Return e) (in custom c_stmt at level 0, e custom c_exp at level 99) : mini_c_scope.

Notation "f args" := (PCall f args) (in custom c_stmt at level 99, args custom c_args) : mini_c_scope.
Notation "c '<-' f args" := (FCall c f args) (in custom c_stmt at level 80, f at next level, args custom c_args) : mini_c_scope.
