From RAC Require Import Notations.
From RAC Require Import Utils.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Strings.String.


Inductive c_type := C_Int | Void.  (* program types τc *)
Inductive gmp_t := Ctype (t:c_type) | String | Mpz. (* type extension τ *)

(* mini-FSL *)

Inductive fsl_decl :=  FSL_Decl (τ:gmp_t) (name:id). (* logic declaration δ *)
Inductive fsl_binop_bool :=  FSL_Lt | FSL_Le | FSL_Gt | FSL_Ge | FSL_Eq | FSL_NEq.
Inductive fsl_binop_int := FSL_Add | FSL_Sub  | FSL_Mul  | FSL_Div.
Definition fsl_binop_int_model (x:fsl_binop_int) : Z -> Z -> Z := match x with
    | FSL_Add => Z.add
    | FSL_Sub => Z.sub
    | FSL_Mul => Z.mul
    | FSL_Div => Z.div
end.

Inductive predicate :=
    | P_True | P_False (* truth values *)
    | P_BinOp (lt: fsl_term) (op:fsl_binop_bool) (rt : fsl_term)
    | Not (t:fsl_term)
    | Disj (lp:predicate) (rp:predicate)  (* disjunction *)
    | Call (name:string) (args:fsl_decl ⃰) (* predicate call *)
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


Inductive c_exp :=
    | Zm (z : Z) (* machine integer *)
    | C_Id (var : id) (* variable access *)
    | BinOpInt (le : c_exp) (op:c_binop_int) (re : c_exp)
    | BinOpBool (le : c_exp) (op:c_binop_bool) (re : c_exp)
    .

Inductive c_statement :=
| Skip (* empty statement *)
| Assign (var:id) (e: c_exp) (* assignment *)
| FCall (var:string) (fname:string) (args: c_exp ⃰) (* function call *)
| PCall  (fname:string) (args: c_exp ⃰) (* procedure call *)
| Seq (s1 : c_statement) (s2 : c_statement) (* sequence *)
| If (cond:c_exp) (_then:c_statement) (_else:c_statement) (* conditional *)
| While (cond:c_exp) (body:c_statement) (* loop *)
| PAssert (e:c_exp) (* program assertion *)
| LAssert (p:predicate) (* logic assertion *)
| Return (e:c_exp)
.

Inductive c_routine :=
| PFun (ret:c_type) (name:id) (args: c_decl ⃰) (b_decl: c_decl ⃰) (body:c_statement) (* program function *)
| LFun (ret:fsl_type) (name:id) (args: fsl_decl ⃰) (body:fsl_term) (* logic function *)
| Predicate (name:id) (args: fsl_decl ⃰) (p:predicate) (* predicate *)
.

Inductive c_program := Program (decls: c_decl ⃰)  (routines: c_routine ⃰).  (* annotated program *)

     
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
Declare Custom Entry c_decl.
Declare Custom Entry c_stmt.
Declare Custom Entry c_exp.
Declare Custom Entry c_type.
Declare Custom Entry c_args.

Notation "<[ d ]>" := d (at level 0, d custom c_decl at level 99) : mini_c_scope.
Notation "<{ s }>" := s (at level 0, s custom c_stmt at level 99) : mini_c_scope.
Notation "( x )" := x (in custom c_exp, x at level 99) : mini_c_scope.

Notation " 'int' " := C_Int (in custom c_type) : mini_c_scope.
Notation " 'void' " := Void (in custom c_type) : mini_c_scope.
Notation "e" := e (in custom c_exp at level 0,  e constr at level 0) : mini_c_scope.
Notation "s" := s (in custom c_stmt at level 0, s constr at level 0) : mini_c_scope.
Notation "d" := d ( in custom c_decl at level 0, d constr at level 0) : mini_c_scope.

Notation "'(' x ',' .. ',' y ')'" := (cons x .. (cons y nil) ..) (in custom c_args at level 0, x custom c_exp, y custom c_exp) : mini_c_scope.



Notation "t id" := (C_Decl t id) (in custom c_decl at level 0, t custom c_type) : mini_c_scope.
Notation "t id args '[' x' .. y' ';' s ']'" := (PFun t id args (cons x' .. (cons y' nil) ..) s)
    (in custom c_decl at level 0, args custom c_args, t custom c_type, s custom c_stmt) : mini_c_scope.


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


Notation "'/*@' 'logic' k id '(' x ',' .. ',' y ')' '=' t" := (LFun k id (cons x .. (cons y nil) ..) t) (in custom c_decl at level 0).
Notation "'/*@' 'predicate' id '(' x ',' .. ',' y ')' '=' p" := (Predicate id (cons x .. (cons y nil) ..) p) (p custom c_stmt, in custom c_decl at level 0).
Notation "'/*@' 'assert' p '*/'" := (LAssert p) (in custom c_stmt at level 0) : mini_c_scope.


Notation "'skip'" := Skip  (in custom c_stmt at level 99) : mini_c_scope.
Notation "'if' cond _then  'else' _else " := (If cond _then _else) 
    (in custom c_stmt at level 89, cond custom c_exp at level 99, _then custom c_stmt at level 99, _else custom c_stmt at level 99) : mini_c_scope.
Notation "s1 ';' s2" := (Seq s1 s2) (in custom c_stmt at level 90, right associativity) : mini_c_scope.
Notation "x = y" := (Assign x y) (in custom c_stmt at level 0, x constr at level 0, y custom c_exp at level 85, no associativity) : mini_c_scope.
Notation "'assert' e" := (PAssert e) (in custom c_stmt at level 0, e custom c_exp at level 99) : mini_c_scope.
Notation "'while' e s" := (While e s) (in custom c_stmt at level 89, e custom c_exp at level 99, s at level 99) : mini_c_scope.
Notation "'return' e" := (Return e) (in custom c_stmt at level 0, e custom c_exp at level 99) : mini_c_scope.

Notation "f args" := (PCall f args) (in custom c_stmt at level 99, args custom c_args) : mini_c_scope.
Notation "c '<-' f args" := (FCall c f args) (in custom c_stmt at level 80, f at next level, args custom c_args) : mini_c_scope.

    
Definition 𝓥 : Set := id. (* program variables and routines *)
Definition 𝔏 : Set := id. (* logic variables *)

Definition 𝐒 : Set := c_statement. (* program statements *)
Definition ℨ : Set := fsl_term. (* logical terms *)
Definition 𝔅 : Set := predicate. (* predicates *)
Definition 𝔗 : Set := gmp_t. (* minigmp types *)


#[global] Instance eqdec_v : EqDec 𝓥 := {eq_dec := string_dec}.



(* ty the function that gives the type of a mini-GMP expression  -> where are the expressions defined ? *)

Definition 𝓕 := 𝓥 ⇀ (𝓥 ⃰ ⨉ 𝐒). (* program functions *)
Definition 𝓟 := 𝓥 ⇀ (𝓥 ⃰ ⨉ 𝐒). (* program procedures *)
Definition 𝔉 :=  𝔏 ⇀ (𝔏 ⃰ ⨉ ℨ). (* logic functions *)
Definition 𝔓 :=  𝔏 ⇀ (𝔏 ⃰ ⨉ 𝔅). (* predicates *)


Module Int16Bounds.
    Definition m_int := -32768.
    Definition M_int := 32767.
End Int16Bounds.

Definition location := nat.
Module Int := MachineInteger Int16Bounds.

Notation "x  ̇ " := (Int.mkMI x) (at level 99).
Notation "n 'ⁱⁿᵗ'" := (Int.to_z n) (at level 99).

Fact zeroinRange : Int.inRange 0.  now split. Qed.
Fact oneinRange : Int.inRange 1. now split. Qed.


Inductive 𝕍 := 
    | VInt (n:Int.MI) (* set of type int, a machine integer (may overflow) *)
    | VMpz (n:location)  (* memory location for values of type mpz *) 
    | UInt   (* set of undefined values of type int *) 
    | UMpz  . (* set of undefined values of type mpz *) 


Definition type_of_value : option 𝕍 -> option 𝔗 := fun v => match v with
| Some (VInt _) | Some UInt => Some (Ctype C_Int)
| Some (VMpz _) | Some UMpz => Some Mpz
| None => None
end.


Definition 𝓜 := location ⇀ ℤ. 

From Coq Require Import Logic.FinFun.


Fact M_is_enumerable: Finite 𝓜.
Proof. unfold Finite. unfold Full. 
Admitted.


Definition Uτ (v:𝕍) : option c_type := match v with 
    | VInt _ => Some C_Int
    | _  => None
end
.


Definition inUτ v : bool := if Uτ v then true else false.

Definition zero := Int.mkMI 0 zeroinRange.
Definition one := Int.mkMI 1 oneinRange.

Definition values_int (v:𝕍) : option 𝕍 := match v with
| VInt n => Some (VInt n)
| _ => None
end.


(* integer from value *)
Definition z_of_Int : Int.MI -> Z := Int.to_z.


Definition Ωᵥ := 𝓥 ⇀ 𝕍.
Definition Ωₗ := 𝔏 ⇀ ℤ.
Definition Ω := Ωᵥ ⨉ Ωₗ.


Record 𝐼 := {min : Z; max : Z}. (* interval *)

(* Definition Γ  := c_routine -> T. (* typing env *) *)
Definition Γᵢ := 𝔏 ⇀ 𝐼. (* typing env mapping logic binders to  intervals *)


Definition 𝓘 := ℨ -> (𝔏 ⇀ 𝐼) -> 𝐼. (* oracle *)

Definition ϴ :=  𝐼 -> 𝔗.

Definition 𝚪 (o: 𝓘) (om:ϴ) : ℨ -> Γᵢ -> 𝔗 := fun lt env => om (o lt env). (* Θ ◦ oracle. *)




(* Module Todo.
Hypothesis type_soundness : forall (env:Ω) (t:Z), True.

Hypothesis convergence : forall (type_env:Γ) (r:mini_c(((((((((_routines), 
    exists (t:T), type_env r = t.
End Todo. *)



Coercion C_Id : id >-> c_exp.
Coercion T_Id : id >-> fsl_term.
Coercion Zm : Z >-> c_exp.
Coercion T_Z : Z >-> fsl_term.

Coercion VInt : Int.MI >-> 𝕍. 
(* Coercion VMpz : nat >-> Value. *)

Coercion LAssert : predicate >-> c_statement.



Definition same_values (v1 v2: option 𝕍) : bool := match v1,v2 with
    | Some (VInt n1), Some (VInt n2) => Int.mi_eqb n1 n2
    | Some (VMpz n1), Some (VMpz n2) => (n1 =? n2)%nat
    | _,_ => false
end
.


Inductive env_partial_order (env env':Ω) (var:𝓥) : Prop :=
| EsameInt n : 
    (fst env) var = Some (VInt n)
    -> (fst env') var = Some (VInt n)
    -> env_partial_order env env' var 
| EsameMpz n : 
    (fst env) var = Some (VMpz n)
    -> (fst env') var = Some (VMpz n)
    -> env_partial_order env env' var 
| EundefInt : (fst env) var = Some UInt
    -> (fst env') var = Some UInt \/  (exists n, (fst env') var = Some (VInt n))
    -> env_partial_order env env' var
| EundefMpz : (fst env) var = Some UMpz
    -> (fst env') var = Some UMpz \/  (exists n, (fst env') var = Some (VMpz n))
    -> env_partial_order env  env' var
| Enone : (fst env) var = None -> env_partial_order env env' var 
.

Inductive mems_partial_order (mem mem':𝓜) (n:nat) : Prop := 
| Msame i : mem n = Some i ->  mem' n = Some i -> mems_partial_order mem mem' n
| Mnone : mem n = None -> mems_partial_order mem mem' n
. 



Fact refl_env_partial_order : forall env v, env_partial_order env env v.
Proof.
    intros [v l] var. remember (v var) as res. destruct res as [val |]. induction val.
    - apply EsameInt with n; now rewrite Heqres.
    - apply EsameMpz with n; now rewrite Heqres.
    - apply EundefInt. now rewrite Heqres. left ; now rewrite Heqres.
    - apply EundefMpz. now rewrite Heqres. left ; now rewrite Heqres.
    - apply Enone. now rewrite Heqres.
Qed.


Fact trans_env_partial_order : forall env env' env'' v, 
    env_partial_order env env' v  /\ env_partial_order env' env'' v ->
    env_partial_order env env'' v.
Proof.
    intros [v l] [v' l'] [v'' l''] var [H1 H2]. 
Admitted.


Fact antisym_env_partial_order : forall env env' v, 
 env_partial_order env env' v /\ env_partial_order env' env v -> env = env'.
Proof.
    intros [v l] [v' l'] var [H1 H2].
Admitted.


Fact refl_mem_partial_order : forall env v, mems_partial_order env env v.
Proof.
Admitted.


Fact trans_mem_partial_order : forall env env' env'' v, 
    mems_partial_order env env' v  /\ mems_partial_order env' env'' v ->
    mems_partial_order env env'' v.
Proof.
Admitted.


Fact antisym_mem_partial_order : forall env env' v, 
    mems_partial_order env env' v /\ mems_partial_order env' env v -> env = env'.
Proof.
Admitted.


Notation "e ⊑ e'" := (forall v, env_partial_order e e' v) (at level 99) : utils_scope.

Notation "( e , m ) ⊑ ( e' , m' )" :=  (
    (forall v, env_partial_order e e' v)
    /\
    (forall n, mems_partial_order m m' n)

) : utils_scope.


Definition var_in_stmt (s:c_statement) (v:𝓥) := True. (* todo *)

(* Lemma test_eq : forall (v v' : Ωᵥ) var z, v{var \ z} = v'{var \ z} <-> v = v'. Admitted.

Lemma test_eq2 : forall (v:Ωᵥ) x z var, v x = (v {var \ z}) x. Admitted.

Lemma env_partial_order_next :  forall x v v' l l' var z, 
    env_partial_order (v{var \ z},l) (v'{var \ z},l') x <-> 
    env_partial_order (v,l) (v',l') x.
Proof.
Admitted.
Lemma values_dec : forall x y : Value, {x = y} + {x <> y}. Admitted.

#[global] Instance v_eq_dec : EqDec Value := {eq_dec := values_dec}.


Inductive add_var (env : Ω) (mem_state : M) (t:gmp_t) (v:V) (z:Value) : Ω * M -> Prop :=
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




