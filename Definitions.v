From RAC Require Import Notations.
From RAC Require Import Utils.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Strings.String.
Open Scope Z_scope.

Declare Scope definition_scope.
Open Scope definition_scope.

Inductive _c_type {T:Set} := C_Int | Void | T_Ext (t:T).  (* program types τc *)
Inductive _gmp_t := String | Mpz. 
Definition gmp_t := @_c_type _gmp_t.  (* type extension τ *)

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
    | Not (t:predicate)
    | Disj (lp:predicate) (rp:predicate)  (* disjunction *)
    | Call (name:string) (args:fsl_decl ⃰) (* predicate call *)
with fsl_term :=
    | T_Z (z:Z) (* integer in Z *)
    | T_Id (name:id) (* variable access *)
    | T_BinOp (lt : fsl_term) (op:fsl_binop_int) (rt : fsl_term)
    | Conditional (cond:predicate) (_then:fsl_term) (_else:fsl_term) (* conditional term *)
.


Inductive fsl_type := FSL_Int | Integer. (* logic types *)

Inductive mini_fsl := LAssert (p:predicate). (* logic assertion *)

   

(* mini-C *)
Inductive _c_decl (T:Set) :=  C_Decl (type: @_c_type T) (name:id). (* program declaration *)

Inductive c_binop_bool :=  C_Lt | C_Le | C_Gt | C_Ge | C_Eq | C_NEq.
Definition c_binop_bool_model (x:c_binop_bool) : Z -> Z -> bool := match x with
    | C_Lt => Z.ltb
    | C_Le => Z.leb
    | C_Gt => Z.gtb
    | C_Ge => Z.geb
    | C_Eq => Z.eqb
    | C_NEq => fun b1 b2 => negb (b1 =? b2)
end.
Notation "◁" := c_binop_bool_model : definition_scope.

Inductive c_binop_int := C_Add | C_Sub | C_Mul | C_Div. 
Definition c_binop_int_model (x:c_binop_int) : Z -> Z -> Z := match x with
    | C_Add => Z.add
    | C_Sub => Z.sub
    | C_Mul => Z.mul
    | C_Div => Z.div
end.
Notation "⋄" := c_binop_int_model.


Definition fsl_binop_int_to_c (x:fsl_binop_int) : c_binop_int := match x with
    | FSL_Add => C_Add
    | FSL_Sub => C_Sub
    | FSL_Mul => C_Mul
    | FSL_Div => C_Div
end.
Notation "□" := fsl_binop_int_to_c : definition_scope.

Definition fsl_binop_bool_to_c (x:fsl_binop_bool) : c_binop_bool := match x with
    | FSL_Lt => C_Lt
    | FSL_Le => C_Le 
    | FSL_Gt => C_Gt
    | FSL_Ge => C_Ge
    | FSL_Eq => C_Eq 
    | FSL_NEq => C_NEq
end.
Notation "◖" := fsl_binop_bool_to_c : definition_scope.


Inductive _c_exp {T : Set}  :=
    | Zm (z : Z) (* machine integer *) (* can only be of type int *)
    | C_Id (var : id) (ty : @_c_type T) (* variable access *) (* can be either int or mpz *)
    | BinOpInt (le : _c_exp) (op:c_binop_int) (re : _c_exp) (* can only be of type int *)
    | BinOpBool (le : _c_exp) (op:c_binop_bool) (re : _c_exp) (* can only be of type int *)
.


Inductive _c_statement {S T : Set} :=
| Skip (* empty statement *)
| Assign (var:id) (e: @_c_exp T) (* assignment *)
| FCall (var:string) (fname:string) (args: @_c_exp T ⃰) (* function call *)
| PCall  (fname:string) (args: @_c_exp T ⃰) (* procedure call *)
| Seq (s1 : _c_statement) (s2 : _c_statement) (* sequence *)
| If (cond:@_c_exp T) (_then:_c_statement) (_else:_c_statement) (* conditional *)
| While (cond:@_c_exp T) (body:_c_statement) (* loop *)
| PAssert (e:@_c_exp T) (* program assertion *)
| Return (e:@_c_exp T)
| Decl (d: @_c_decl T)
| S_Ext (stmt:S)
.

Inductive _c_routine {S T : Set} :=
| PFun (ret: @_c_type T) (name:id) (args: @_c_decl T ⃰) (b_decl: @_c_decl T ⃰) (body: @_c_statement T S) (* program function *)
| LFun (ret:fsl_type) (name:id) (args: fsl_decl ⃰) (body:fsl_term) (* logic function *)
| Predicate (name:id) (args: fsl_decl ⃰) (p:predicate) (* predicate *)
.

Record _c_program {S T : Set}:= mkPgrm { decls: @_c_decl T ⃰ ; routines: @_c_routine T S ⃰ }. 


     
(*  mini-GMP *)

Inductive _gmp_statement := 
    | Init (name:id) (* mpz allocation *)
    | Set_i (name:id) (i:@_c_exp _gmp_t) (* assignment from an int *)
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

Definition op (x:fsl_binop_int) : id -> id -> id -> _gmp_statement := match x with
    | FSL_Add => GMP_Add
    | FSL_Sub => GMP_Sub
    | FSL_Mul => GMP_Mul
    | FSL_Div => GMP_Div
end.






Definition c_exp := @_c_exp Empty_set.
Definition c_statement := @_c_statement Empty_set Empty_set.

Definition gmp_decl := @_c_decl _gmp_t.

Definition gmp_exp := @_c_exp _gmp_t.
Definition mini_c_fsl := @_c_statement mini_fsl _gmp_t.
Definition gmp_statement := @_c_statement _gmp_statement _gmp_t.


(* ty the function that gives the type of a mini-GMP expression *)
Definition ty (e: gmp_exp) : gmp_t := match e with 
    | Zm _  => C_Int
    | C_Id _ ty => ty
    | BinOpInt _ _ _  => C_Int
    | BinOpBool _ _ _ => C_Int
    end.

Declare Scope mini_c_scope.
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


Notation "'/*@' 'logic' k id '(' x ',' .. ',' y ')' '=' t" := (LFun k id (cons x .. (cons y nil) ..) t) (in custom c_decl at level 0): mini_c_scope.
Notation "'/*@' 'predicate' id '(' x ',' .. ',' y ')' '=' p" := (Predicate id (cons x .. (cons y nil) ..) p) (p custom c_stmt, in custom c_decl at level 0): mini_c_scope.
Notation "'/*@' 'assert' p '*/'" := (LAssert p) (in custom c_stmt at level 0) : mini_c_scope.


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


Declare Scope mini_gmp_scope.   
Declare Custom Entry gmp_stmt. 
Notation "e" := e (in custom gmp_stmt at level 0,  e constr at level 0) : mini_c_scope.
Notation "< s >" := s (at level 0, s custom gmp_stmt at level 99, format "< s >") : mini_gmp_scope.
Notation "'set_i' ( id , e )" := (Set_i id e) (in custom gmp_stmt) : mini_gmp_scope.
Notation "'set_s' ( id , l )" := (Set_s id l) (in custom gmp_stmt): mini_gmp_scope.
Notation "'set_z' ( id1 , id2 )" := (Set_z id1 id2) (in custom gmp_stmt): mini_gmp_scope.
Notation "'cl' ( id )" := (Clear id) (in custom gmp_stmt): mini_gmp_scope.
Notation "id = 'cmp' ( id1 , id2 )" := (Comp id id1 id2) (in custom gmp_stmt at level 99): mini_gmp_scope.
Notation "id = 'get_int' ( id1 )" := (Coerc id id1) (in custom gmp_stmt at level 99): mini_gmp_scope.
Notation "'init' ( id )" := (Init id) (in custom gmp_stmt) : mini_gmp_scope.
Notation "'add' ( id1 , id2 , id3 )" := (GMP_Add id1 id2 id3) (in custom gmp_stmt) : mini_gmp_scope.
Notation "'sub' ( id1 , id2 , id3 )" := (GMP_Sub id1 id2 id3) (in custom gmp_stmt) : mini_gmp_scope.
Notation "'mul' ( id1 , id2 , id3 )" := (GMP_Mul id1 id2 id3) (in custom gmp_stmt): mini_gmp_scope.
Notation "'div' ( id1 , id2 , id3 )" := (GMP_Div id1 id2 id3) (in custom gmp_stmt): mini_gmp_scope.

Definition 𝓥 := id. (* program variables and routines *)
Definition 𝔏 := id. (* logic variables *)

Definition 𝐒 := gmp_statement. (* program statements *)
Definition ℨ := fsl_term. (* logical terms *)
Definition 𝔅 := predicate. (* predicates *)
Definition 𝔗 := gmp_t. (* minigmp types *)


#[global] Instance eqdec_v : EqDec 𝓥 := {eq_dec := string_dec}.



Definition 𝓕 {S T : Set} := 𝓥 ⇀ (𝓥 ⃰ ⨉ @_c_statement S T). (* program functions *)
Definition 𝓟 {S T : Set} := 𝓥 ⇀ (𝓥 ⃰ ⨉ @_c_statement S T). (* program procedures *)
Definition 𝔉 :=  𝔏 ⇀ (𝔏 ⃰ ⨉ ℨ). (* logic functions *)
Definition 𝔓 :=  𝔏 ⇀ (𝔏 ⃰ ⨉ 𝔅). (* predicates *)


Module Int16Bounds.
    Definition m_int := -32768.
    Definition M_int := 32767.
End Int16Bounds.

Definition location := nat.
Module Int := MachineInteger Int16Bounds.


#[global] Instance location_eq_dec : EqDec location := {eq_dec := Nat.eq_dec}.

Fact zeroinRange : Int.inRange 0.  now split. Qed.
Fact oneinRange : Int.inRange 1. now split. Qed.
Fact suboneinRange : Int.inRange (-1). now split. Qed.

#[global] Hint Resolve zeroinRange: rac_hint.
#[global] Hint Resolve oneinRange: rac_hint.
#[global] Hint Resolve suboneinRange: rac_hint.



Inductive 𝕍 := 
    | VInt (n:Int.MI) (* set of type int, a machine integer (may overflow) *)
    | VMpz (n:location)  (* memory location for values of type mpz *) 
    | UInt   (* set of undefined values of type int *) 
    | UMpz  . (* set of undefined values of type mpz *) 


Notation "z ̇" := (Int.to_z z) (at level 0) : definition_scope.
Notation "z 'ⁱⁿᵗ' ir" := (Int.mkMI z ir) (at level 99) : definition_scope.


Fact x_of_z_to_z_is_x : forall x irx, (x ̇ ⁱⁿᵗ irx) = x.
Proof.
    intros. destruct x. simpl. f_equal. unfold Int.inRange in *. 
    simpl in *.  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.
    

Coercion Zm : Z >-> _c_exp.
Coercion Decl : _c_decl >-> _c_statement.
Coercion T_Id : id >-> fsl_term.
Coercion T_Z : Z >-> fsl_term.
Coercion VInt : Int.MI >-> 𝕍. 
Coercion VMpz : location >-> 𝕍.
Coercion gmp_s_ext (s:_gmp_statement) := S_Ext s (T:=_gmp_t).
Coercion fsl_s_ext (s:mini_fsl) := S_Ext s (T:=_gmp_t).
Coercion gmp_t_ext (t:_gmp_t) : _c_type := T_Ext t.


(* Coercion VMpz : nat >-> Value. *)
(* 
Definition same_values (v1 v2: option 𝕍) : bool := match v1,v2 with
    | Some (VInt n1), Some (VInt n2) => Int.mi_eqb n1 n2
    | Some (VMpz n1), Some (VMpz n2) => (n1 =? n2)%nat
    | _,_ => false
end
. *)

Definition type_of_value : option 𝕍 -> option 𝔗 := fun v => match v with
| Some (VInt _) | Some UInt => Some C_Int
| Some (VMpz _) | Some UMpz => Some (T_Ext Mpz)
| None => None
end.


Fixpoint vars {T:Set} (exp : @_c_exp T) : list id := match exp with 
| Zm z => nil
| C_Id v _ => v::nil
| BinOpInt le _ re | BinOpBool le _ re => (vars le) ++ (vars re)
end.


(* Inductive _c_exp {T : Set}  :=
    | Zm (z : Z) (* machine integer *) (* can only be of type int *)
    | C_Id (var : id) (ty : @_c_type T) (* variable access *) (* can be either int or mpz *)
    | BinOpInt (le : _c_exp) (op:c_binop_int) (re : _c_exp) (* can only be of type int *)
    | BinOpBool (le : _c_exp) (op:c_binop_bool) (re : _c_exp) (* can only be of type int *) *)
Definition 𝓜 := location ⇀ ℤ. 

From Coq Require Import Logic.FinFun.


Definition Uτ (v:𝕍) : option (@_c_type Empty_set) := match v with 
    | UInt => Some C_Int 
    | _ => None
end
.


Definition inUτ v : bool := if Uτ v then true else false.

Definition zero := Int.mkMI 0 zeroinRange.
Definition one := Int.mkMI 1 oneinRange.
Definition sub_one := Int.mkMI (-1) suboneinRange.


Definition values_int (v:𝕍) : option 𝕍 := match v with
| VInt n => Some (VInt n)
| _ => None
end.


(* integer from value *)
Definition z_of_Int : Int.MI -> Z := Int.to_z.


Definition Ωᵥ := 𝓥 ⇀ 𝕍.
Definition Ωₗ := 𝔏 ⇀ ℤ.
Definition Ω := Ωᵥ ⨉ Ωₗ.


Record 𝐼 := mkInterval {min : Z; max : Z}. (* interval *)

Definition 𝓘 := ℨ -> (𝔏 ⇀ 𝐼) -> 𝐼. (* oracle *)

Definition ϴ :=  𝐼 -> 𝔗.

Definition Γᵢ := 𝔏 ⇀ 𝐼. (* typing env mapping logic binders to intervals *)
Definition Γᵥ := 𝔏 ⇀ 𝓥 ⨉ 𝐼. (* environment for bindings :  variable and interval infered from it *)
Definition Γ := Γᵥ ⨉ Γᵢ.


Definition ψ := 𝔏 ⨉ (𝔏 ⇀ 𝐼) ⇀ 𝓥 . (* global definitions env *)


Notation "'Γ' '(' x ')' " := (Γᵥ x, Γᵢ x) : definition_scope.

Definition 𝚪 (oracle: 𝓘) (o:ϴ) := fun (t:ℨ) (τᵢ: Γᵢ) =>  o (oracle t τᵢ) : 𝔗. (* Θ ◦ oracle. *)

Record type_inf := { oracle : 𝓘 ; t_env : Γᵢ ; i_op : ϴ }.


(* Module Todo.
Hypothesis type_soundness : forall (env:Ω) (t:Z), True.

Hypothesis convergence : forall (type_env:Γ) (r:mini_c(((((((((_routines), 
    exists (t:T), type_env r = t.
End Todo. *)

Close Scope utils_scope.

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


Notation "e ⊑ e'" := (forall v, env_partial_order e e' v) (at level 99) : definition_scope.

Notation "( e , m ) ⊑ ( e' , m' )" :=  (
    (forall v, env_partial_order e e' v)
    /\
    (forall n, mems_partial_order m m' n)

) : definition_scope.



(* invariants for routine translation *)

(* notations *)
Inductive add_var (env : Ω) (mem_state : 𝓜) (τ:gmp_t) (v:id) (z:Z) : Ω * 𝓜 -> Prop :=
| typeInt irz : 
    τ = C_Int ->
    add_var env mem_state τ v z (((fst env){v\ z ⁱⁿᵗ irz :𝕍}, snd env),mem_state)%utils

| typeMpz x (n:Int.MI) :
    τ  = Mpz ->
    (forall v',  (fst env) v' <> Some (VMpz x) )->
    add_var env mem_state τ v z (((fst env){v\VMpz x}, snd env),mem_state{x\z_of_Int n})%utils
.



Definition 𝐴 := list (gmp_t * id * Z).

(* Fixpoint add_var_𝐴 (env : Ω) (mem_state : 𝓜) (A : 𝐴) : Ω * 𝓜 -> Prop := match A with 
    | nil => fun x => x
    | cons (t,v,z) tl => fun x => add_var env mem_state t v z (fst x, snd x)
end. *)


(*fixme fixpoint or List.fold *)
(*)
Definition add_var_𝐴 (env : Ω) (mem_state : 𝓜) (A : 𝐴) : Prop :=
    List.fold_left (
        fun (acc:Prop) (args:gmp_t * id * Z)  => 
            let '(t,id,z) := args in
            add_var env mem_state t id z  (env,mem_state) /\ acc 
    ) A (env,mem_state)
 . *)

Inductive add_var_𝐴 (env : Ω) (mem_state : 𝓜) : 𝐴 -> Ω * 𝓜 -> Prop := 
| add_var_nil : add_var_𝐴  env mem_state nil (env,mem_state)

| add_var_cons t v z A env' mem_state': 
    True -> 
    add_var env mem_state t v z (env',mem_state') -> 
    add_var_𝐴 env mem_state A (env',mem_state')
.

Open Scope utils_scope.


Example add_var_int : forall (ir3 :Int.inRange 3), add_var (⊥,⊥) ⊥ C_Int "y" 3  ((⊥{"y"\VInt (Int.mkMI 3 ir3)},⊥), ⊥).
Proof.
   now constructor.
Qed.

Example add_var_mpz : add_var (⊥,⊥) ⊥ Mpz "y" 3  ((⊥{"y"\VMpz 1%nat},⊥), ⊥{1%nat\3}).
Proof.
    assert (ir3: Int.inRange 3). easy.
    now apply (typeMpz (⊥,⊥) ⊥ Mpz "y" 3 1%nat (Int.mkMI 3 ir3)).
Qed.



Compute add_var_𝐴 (⊥,⊥) ⊥ nil.

Example envaddnil : add_var_𝐴 (⊥,⊥) ⊥ nil ((⊥,⊥), ⊥).
Proof.
 constructor.
Qed.

Open Scope list.

Example envaddone : add_var_𝐴 (⊥,⊥) ⊥ ((T_Ext Mpz, "y", 3)::nil) ((⊥{"y"\VMpz (S O)},⊥), ⊥{(S O)\3}).
Proof.
    assert (ir3: Int.inRange 3). easy.
    eapply add_var_cons with (t:=Mpz) (v:="y") (z:=3).
 - auto.
 - apply (typeMpz (⊥,⊥) ⊥ Mpz "y" 3 1%nat (Int.mkMI 3 ir3)).
    * reflexivity.
    * intro v. intro contra. inversion contra.
Qed.


(* synchronicity invariant *)
Definition I1 (env:Ω) (ienv:Γ) := ((dom (snd env)) = (dom (fst ienv) + dom (snd ienv)))%utils.

(* suitability invariant *)
Definition I2 (env:ψ) := True. (* todo *)


Inductive pgrm_var_representation (iop:ϴ) (env:Ω) (mem : 𝓜) (ienv:Γ) : (Ω * 𝓜) -> Prop :=
| empty ΩΓ 𝓜Γ :   
    I1 env ienv ->
    let A := nil  (* { (iop ((snd ienv) v), v, (snd env) v ) | v in dom ienv  } *)
    in
    add_var_𝐴 env mem A (ΩΓ,𝓜Γ) -> 
    pgrm_var_representation iop env mem ienv (ΩΓ,𝓜Γ)
.




