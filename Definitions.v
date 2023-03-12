From RAC Require Import Notations.
From RAC Require Import Utils.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Strings.String.
Open Scope Z_scope.
Open Scope fsl_scope.


Inductive c_type := C_Int | Void.  (* program types τc *)
Inductive gmp_t := Ctype (t:c_type) | String | Mpz. (* type extension τ *)

(* mini-FSL *)

Inductive fsl_decl :=  FSL_Decl (τ:gmp_t) (name:id). (* logic declaration δ *)
Inductive fsl_binop_bool :=  FSL_Lt | FSL_Le | FSL_Gt | FSL_Ge | FSL_Eq | FSL_NEq.
Inductive fsl_binop_int := FSL_Add | FSL_Min  | FSL_Mul  | FSL_Div.
Definition fsl_binop_int_model (x:fsl_binop_int) : Z -> Z -> Z := match x with
    | FSL_Add => Z.add
    | FSL_Min => Z.min
    | FSL_Mul => Z.mul
    | FSL_Div => Z.div
end.

Inductive predicate :=
    | P_True | P_False (* truth values *)
    | P_BinOp (lt: fsl_term) (op:fsl_binop_bool) (rt : fsl_term)
    | Not (t:fsl_term)
    | Disj (lp:predicate) (rp:predicate)  (* disjunction *)
    | Call (name:string) (args:fsl_decl^*) (* predicate call *)
with fsl_term :=
    | T_Z (z:Z) (* integer in Z *)
    | T_Id (name:id) (* variable access *)
    | T_BinOp (lt : fsl_term) (op:fsl_binop_int) (rt : fsl_term)
    | Conditional (cond:predicate) (_then:fsl_term) (_else:fsl_term) (* conditional term *)
.


Inductive fsl_type := FSL_Int | Integer. (* logic types *)
   

(* mini-C *)
Inductive c_decl :=  C_Decl (type:c_type) (name:id). (* program declaration *)

Inductive c_binop_bool :=  C_Lt | C_Le | C_Gt | C_Ge | C_Eq | C_NEq.
Definition c_binop_bool_model (x:c_binop_bool) : Z -> Z -> Prop := match x with
    | C_Lt => Z.lt
    | C_Le => Z.le
    | C_Gt => Z.gt
    | C_Ge => Z.ge
    | C_Eq => Z.eq
    | C_NEq => fun b1 b2 => ~ (Z.eq b1 b2)
end.
Notation "◁" := c_binop_bool_model.

Inductive c_binop_int := C_Add | C_Min | C_Mul | C_Div. 
Definition c_binop_int_model (x:c_binop_int) : Z -> Z -> Z := match x with
    | C_Add => Z.add
    | C_Min => Z.min
    | C_Mul => Z.mul
    | C_Div => Z.div
end.
Notation "⋄" := c_binop_int_model.


Inductive c_exp :=
    | Zm (z : Z) (* machine integer *)
    | C_Id (var : id) (* variable access *)
    | BinOpInt (le : c_exp) (op:c_binop_int) (re : c_exp)
    | BinOpBool (le : c_exp) (op:c_binop_bool) (re : c_exp)
    .

Inductive c_statement :=
| Skip (* empty statement *)
| Assign (var:id) (e: c_exp) (* assignment *)
| FCall (var:string) (fname:string) (args: c_exp^*) (* function call *)
| PCall  (fname:string) (args: c_exp^*) (* procedure call *)
| Seq (s1 : c_statement) (s2 : c_statement) (* sequence *)
| If (cond:c_exp) (_then:c_statement) (_else:c_statement) (* conditional *)
| While (cond:c_exp) (body:c_statement) (* loop *)
| PAssert (e:c_exp) (* program assertion *)
| LAssert (p:predicate) (* logic assertion *)
| Return (e:c_exp)
.

Inductive c_routines :=
| PFun (ret:c_type) (name:id) (args: c_decl^*) (b_decl: c_decl^* ) (body:c_statement) (* program function *)
| LFun (ret:fsl_type) (name:id) (args: fsl_decl^*) (body:fsl_term) (* logic function *)
| Predicate (name:id) (args: fsl_decl^*) (p:predicate) (* predicate *)
.

Inductive c_program := Program (decls: c_decl^*)  (routines: c_routines^*).  (* annotated program *)

     
(*  mini-GMP *)

Inductive gmp_statement := 
    | Init (name:id) (* mpz allocation *)
    | Set_i (name:id) (e:c_exp) (* assignment from an int *)
    | Set_s (name:id) (l:string) (* assignment from a string literal *)
    | Set_z (name z:id)(* assignment from a mpz *)
    | Clear (name:id) (* mpz de-allocation *)
    | GMP_Add (lid rid res :id)
    | GMP_Sub (lid rid res :id)
    | GMP_Mul (lid rid res :id)
    | GMP_Div (lid rid res :id)
    | Comp (res lid rid :id) (* mpz comparison *)
    | Coerc (name n : id) (* mpz coercion *)
    .

Inductive statement := S_G (s:gmp_statement) | S_C (c:c_statement). (* statement extension *)



Declare Scope mini_c_scope.

Declare Custom Entry mini_c.

Notation " 'int' " := C_Int (in custom mini_c).
Notation " 'void' " := Void (in custom mini_c).
Notation "d1 .. dn f1 .. fn" := (Program (cons d1 .. (cons dn nil) ..) (cons f1 .. (cons fn nil) ..)) (in custom mini_c at level 0).
Notation "t id" := (C_Decl t id) (in custom mini_c at level 0).
Notation "t id '(' x ',' .. ',' y ')' '{' x' .. y' ';' s '}'" := 
    (PFun t id (cons x .. (cons y nil) ..) (cons x' .. (cons y' nil) ..) s) (x' custom mini_c, y' custom mini_c, s custom mini_c, in custom mini_c at level 0).
Notation "'/*@' 'logic' k id '(' x ',' .. ',' y ')' '=' t" := (LFun k id (cons x .. (cons y nil) ..) t) (in custom mini_c at level 0).
Notation "'/*@' 'predicate' id '(' x ',' .. ',' y ')' '=' p" := (Predicate id (cons x .. (cons y nil) ..) p) (in custom mini_c at level 0).


Notation "<{ e }>" := e (at level 0, e custom mini_c at level 99) : mini_c_scope.
Notation "( x )" := x (in custom mini_c, x at level 99) : mini_c_scope.
Notation "x" := x (in custom mini_c at level 0, x constr at level 0) : mini_c_scope.
Notation "'skip'" := Skip  (in custom mini_c at level 0) : mini_c_scope.
Notation "'if' '(' cond ')'  _then  'else' _else " := (If cond _then _else) 
    (in custom mini_c at level 89, cond at level 99, _then at level 99, _else at level 99) : mini_c_scope.
Notation "x + y"   := (BinOpInt x C_Add y) (in custom mini_c at level 50, left associativity) : mini_c_scope.
Notation "x - y"   := (BinOpInt x C_Min y) (in custom mini_c at level 50, left associativity) : mini_c_scope.
Notation "x * y"   := (BinOpInt x C_Mul y) (in custom mini_c at level 50, left associativity) : mini_c_scope.
Notation "x / y"   := (BinOpInt x C_Div y) (in custom mini_c at level 50, left associativity) : mini_c_scope.
Notation "x == y"   := (BinOpBool x C_Eq y) (in custom mini_c at level 50, left associativity) : mini_c_scope.
Notation "x != y"   := (BinOpBool x C_NEq y) (in custom mini_c at level 50, left associativity) : mini_c_scope.
Notation "x < y"   := (BinOpBool x C_Lt y) (in custom mini_c at level 50, left associativity) : mini_c_scope.
Notation "x <= y"   := (BinOpBool x C_Le y) (in custom mini_c at level 50, left associativity) : mini_c_scope.
Notation "x > y"   := (BinOpBool x C_Gt y) (in custom mini_c at level 50, left associativity) : mini_c_scope.
Notation "x >= y"   := (BinOpBool x C_Ge y) (in custom mini_c at level 50, left associativity) : mini_c_scope.


Notation "s1 ';' s2" := (Seq s1 s2) (in custom mini_c at level 90, right associativity) : mini_c_scope.
Notation "x := y" := (Assign x y) (in custom mini_c at level 0, x constr at level 0, y at level 85, no associativity) : mini_c_scope.
Notation "'assert' '(' e ')'" := (PAssert e) (in custom mini_c at level 0) : mini_c_scope.
Notation "'/*@' 'assert' p '*/'" := (LAssert p) (in custom mini_c at level 0) : mini_c_scope.
Notation "'while' '(' e ')' s" := (While e s) (in custom mini_c at level 0) : mini_c_scope.
Notation "'return' '(' e ')'" := (Return e) (in custom mini_c at level 0) : mini_c_scope.
Notation "c '=' f '(' x ',' .. ',' y ')'" := (FCall c f (cons x .. (cons y nil) ..)) (in custom mini_c at level 0).
Notation "f '(' x ',' .. ',' y ')'" := (PCall f (cons x .. (cons y nil) ..)) (in custom mini_c at level 0).


     
Definition V : Set := id. (* program variables and routines *)
Definition L : Set := id. (* logic variables and routines *)


#[global] Instance eqdec_v : EqDec V := {eq_dec := string_dec}.

Definition S : Set := c_statement. (* program statements *)
Definition LT : Set := fsl_term. (* logical terms *)
Definition B : Set := predicate. (* predicates *)
Definition T : Set := gmp_t. (* minigmp types *)

(* ty the function that gives the type of a mini-GMP expression  -> where are the expressions defined ? *)

Definition F := V ⇀ (V^* * S). (* program functions *)
Definition P := V ⇀ (V^* * S). (* program procedures *)
Definition Fl :=  L ⇀ (L^* * Z). (* logic functions *)
Definition Bl :=  L ⇀ (L^* * B). (* predicates *)


Module Int16Bounds.
    Definition m_int := -32768.
    Definition M_int := 32767.
End Int16Bounds.

Module Int := MachineInteger Int16Bounds.

Fact zeroinRange : Int.inRange 0. now split. Qed.
Fact oneinRange : Int.inRange 1. now split. Qed.


Inductive Values := 
    | Int (n:Int.MI) (* set of type int, a machine integer (may overflow) *)
    | VMpz (n:nat)  (* memory location for values of type mpz *) 
    | UInt   (* set of undefined values of type int *) 
    | UMpz  . (* set of undefined values of type mpz *) 


Definition zero := Int (Int.of_z 0 zeroinRange).
Definition one := Int (Int.of_z 1 oneinRange).

Definition values_int (v:Values) : option Values := match v with
| Int n => Some (Int n)
| _ => None
end.


(* integer from value *)
Definition z_of_Int : Int.MI -> Z := Int.to_z.

(* fixme must be specialized for Values of type VMpz *)
Definition M := Values ⇀ Z. (* memory state, i.e. current mpz value of given mem loc*)


Definition Ωᵥ := V ⇀ Values.
Definition Ωₗ := L ⇀ Z.


(* todo: use a record with coercion to not having to deal with fst snd *)
Definition Ω := (Ωᵥ * Ωₗ)%type.

Definition Γ  := c_routines -> T. (* typing env *)

Record I := {min : Z; max : Z}. (* interval *)


Definition Γᵢ := L ⇀ I. (* typing env mapping logic binders to  intervals *)


Definition oracle := LT -> Γᵢ -> I.

Definition Θ :=  I -> T.

Definition Tr (o: oracle) (om:Θ) : LT -> Γᵢ -> T := fun lt env => om (o lt env). (* Θ ◦ oracle. *)




(* Module Todo.
Hypothesis type_soundness : forall (env:Ω) (t:Z), True.

Hypothesis convergence : forall (type_env:Γ) (r:mini_c_routines), 
    exists (t:T), type_env r = t.
End Todo. *)



Coercion C_Id : id >-> c_exp.
Coercion T_Id : id >-> fsl_term.
Coercion Zm : Z >-> c_exp.
Coercion T_Z : Z >-> fsl_term.

(* Coercion Int.of_z : Z >-> Int.MI. *)

Coercion Int : Int.MI >-> Values. 
Coercion VMpz : nat >-> Values.

Coercion LAssert : predicate >-> c_statement.



Definition same_values (v1 v2: option Values) : bool := match v1,v2 with
    | Some (Int n1), Some (Int n2) =>  Int.mi_eqb n1 n2
    | Some (VMpz n1), Some (VMpz n2) => (n1 =? n2)%nat
    | _,_ => false
end
.


Inductive env_partial_order (env:Ω) : Ω -> id -> Prop :=
| env_refl v : env_partial_order env env v
| sameInt env' n v: 
    (fst env) v = Some (Int n)
    -> (fst env') v = Some (Int n)
    -> env_partial_order env env' v
| sameMpz n env' v: 
    (fst env) v = Some (VMpz n)
    -> (fst env') v = Some (VMpz n)
    -> env_partial_order env env' v
| undefInt n env' v : (fst env) v = Some UInt
    -> (fst env') v = Some UInt \/ (fst env') v = Some (Int n)
    -> env_partial_order env env' v
| undefMpz n env' v: (fst env) v = Some UMpz
    -> (fst env') v = Some UMpz \/ (fst env') v = Some (VMpz n)
    -> env_partial_order env env' v
| none v env' : (fst env) v = None -> env_partial_order env env' v
.


Inductive mems_partial_order (mems:M) : M -> nat -> Prop := (* fixme: definition in paper ? *)
| mems_refl n : mems_partial_order mems mems n
| fixme  mems' n:  mems_partial_order mems mems' n 
.

Notation "e ⊑ e'" := (forall v, env_partial_order e e' v).

Notation "'[' ( e , m ) ']' ⊑ '[' ( e' , m' ) ']'" :=  (
    (forall v, env_partial_order e e' v)
    /\
    (forall n, mems_partial_order m m' n)

).



Definition VarNotInStmt (s:c_statement) (v:V) := True. (* todo *)

(* Lemma test_eq : forall (v v' : Ωᵥ) var z, v{var \ z} = v'{var \ z} <-> v = v'. Admitted.

Lemma test_eq2 : forall (v:Ωᵥ) x z var, v x = (v {var \ z}) x. Admitted.

Lemma env_partial_order_next :  forall x v v' l l' var z, 
    env_partial_order (v{var \ z},l) (v'{var \ z},l') x <-> 
    env_partial_order (v,l) (v',l') x.
Proof.
Admitted.
Lemma values_dec : forall x y : Values, {x = y} + {x <> y}. Admitted.

#[global] Instance v_eq_dec : EqDec Values := {eq_dec := values_dec}.


Inductive add_var (env : Ω) (mem_state : M) (t:gmp_t) (v:V) (z:Values) : Ω * M -> Prop :=
| typeInt n : 
    t = Ctype C_Int ->
    z = Int n \/ z = UInt ->
    add_var env mem_state t v z (((fst env){v\z}, snd env),mem_state)

| typeMpz x (n:Int.MI) :
    t = Mpz ->
    z = Int n \/ z = UInt ->
    add_var env mem_state t v z (((fst env){v\x}, snd env),mem_state{x\z_of_Int n})
.
 *)




