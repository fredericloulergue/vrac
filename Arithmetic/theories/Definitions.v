From RAC Require Import Notations.
From RAC Require Import Utils.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Strings.String.
From Coq Require Import Setoid.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.

Open Scope Z_scope.

Declare Scope definition_scope.
Open Scope definition_scope.
Delimit Scope definition_scope with def.

Inductive _c_type {T:Set} := C_Int | Void | T_Ext (t:T).  (* program types τc *)
Inductive _gmp_t := String | Mpz. 
Definition gmp_t := @_c_type _gmp_t.  (* type extension τ *)

(* mini-FSL *)

Inductive fsl_decl :=  FSL_Decl (τ:gmp_t) (name:id). (* logic declaration δ *)
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

Inductive predicate :=
    | P_True | P_False (* truth values *)
    | P_BinOp (lt: fsl_term) (op:fsl_binop_bool) (rt : fsl_term)
    | Not (t:predicate)
    | Disj (lp:predicate) (rp:predicate)  (* disjunction *)
    | Call (name:string) (args:fsl_decl ⃰) (* predicate call *)
with fsl_term :=
    | T_Z (z:Z) :> fsl_term (* integer in Z *)
    | T_Id (name:id) :> fsl_term (* variable access *)
    | T_BinOp (lt : fsl_term) (op:fsl_binop_int) (rt : fsl_term)
    | T_Cond (cond:predicate) (_then:fsl_term) (_else:fsl_term) (* conditional term *)
.


Inductive fsl_type := FSL_Int | Integer. (* logic types *)

Inductive _fsl_statement := LAssert (p:predicate). (* logic assertion *)


(* mini-C *)
Inductive _c_decl {T:Set} :=  C_Decl (type: @_c_type T) (name:id). (* program declaration *)

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
Notation "⋄" := c_binop_int_model : definition_scope.


Coercion fsl_binop_int_to_c (x:fsl_binop_int) : c_binop_int := match x with
    | FSL_Add => C_Add
    | FSL_Sub => C_Sub
    | FSL_Mul => C_Mul
    | FSL_Div => C_Div
end.
Notation "□" := fsl_binop_int_to_c : definition_scope.

Coercion fsl_binop_bool_to_c (x:fsl_binop_bool) : c_binop_bool := match x with
    | FSL_Lt => C_Lt
    | FSL_Le => C_Le 
    | FSL_Gt => C_Gt
    | FSL_Ge => C_Ge
    | FSL_Eq => C_Eq 
    | FSL_NEq => C_NEq
end.
Notation "◖" := fsl_binop_bool_to_c : definition_scope.

(* #[warnings="-uniform-inheritance"]  *)
Inductive _c_exp {T : Set}  :=
    | Zm (z : Z) :> _c_exp(* machine integer *) (* can only be of type int *)
    | C_Id (var : id) (ty : @_c_type T) (* variable access *) (* can be either int or mpz *)
    | BinOpInt (le : _c_exp) (op:c_binop_int) (re : _c_exp) (* can only be of type int *)
    | BinOpBool (le : _c_exp) (op:c_binop_bool) (re : _c_exp) (* can only be of type int *)
.
#[global] Hint Constructors _c_exp  : rac_hint.


(* #[warnings="-uniform-inheritance"]  *)
Inductive _c_statement {S T : Set} :=
    | Skip (* empty statement *)
    | Assign (var:id) (e: @_c_exp T) (* assignment *)
    | FCall (var:id) (fname:string) (args: @_c_exp T ⃰) (* function call *)
    | PCall  (fname:string) (args: @_c_exp T ⃰) (* procedure call *)
    | Seq (s1 : _c_statement) (s2 : _c_statement) (* sequence *)
    | If (cond:@_c_exp T) (_then:_c_statement) (_else:_c_statement) (* conditional *)
    | While (cond:@_c_exp T) (body:_c_statement) (* loop *) 
    | PAssert (e:@_c_exp T) (* program assertion *)
    | Return (e:@_c_exp T) 
    | Decl (d: @_c_decl T) :> _c_statement
    | S_Ext (stmt:S)
.

#[global] Hint Constructors _c_statement  : rac_hint.


Definition compiler_prefix : id := "_".
Definition comp_var x : id  := (compiler_prefix ++ x)%string.
Definition is_comp_var := String.prefix compiler_prefix.
Definition res_f : id := comp_var "res".

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
    | Coerc (name n : id)  (* mpz coercion *)
.

#[global] Hint Constructors _gmp_statement  : rac_hint.

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

Definition fsl_statement := @_c_statement _fsl_statement _gmp_t.
Definition gmp_statement := @_c_statement _gmp_statement _gmp_t.

Definition fsl_pgrm := @_c_program _fsl_statement _gmp_t.
Definition rac_pgrm := @_c_program _gmp_statement _gmp_t.






(* ty the function that gives the type of a mini-GMP expression *)
Definition ty (e: gmp_exp) : gmp_t := match e with 
    | Zm _  => C_Int
    | C_Id _ ty => ty
    | BinOpInt _ _ _  => C_Int
    | BinOpBool _ _ _ => C_Int
    end.

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
Delimit Scope mini_gmp_scope with gmp.
Declare Custom Entry gmp_stmt. 
Notation "e" := e (in custom gmp_stmt at level 0,  e constr at level 0) : mini_c_scope.
Notation "<( s )>" := s (at level 0, s custom gmp_stmt at level 99, format "<( s )>") : mini_gmp_scope.
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


Definition 𝓥 : Type := id. (* program variables and routines *)
Definition 𝔏 : Type := id. (* logic variables *)

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
Module Int := MachineInteger Int16Bounds.


Definition location := nat. 
#[global] Instance location_eq_dec : EqDec location := {eq_dec := Nat.eq_dec}.

Fact zeroinRange : Int.inRange 0.  now split. Qed.
Fact oneinRange : Int.inRange 1. now split. Qed.
Fact suboneinRange : Int.inRange (-1). now split. Qed.

#[global] Hint Resolve zeroinRange: rac_hint.
#[global] Hint Resolve oneinRange: rac_hint.
#[global] Hint Resolve suboneinRange: rac_hint.

Inductive value := 
    | VInt (n:Int.MI) :> value (* set of type int, a machine integer (may overflow) *)
    | VMpz (l:option location) (* memory location for values of type mpz, none is a null pointer *) 
.

Inductive undef := 
    | UInt (n:Int.MI) (* set of undefined values of type int *) 
    | UMpz (l:option location) (* set of undefined values of type mpz *) 
.

Inductive 𝕍 :=  Def (v : value) :> 𝕍 | Undef (uv : undef) :> 𝕍.

Inductive 𝔹 := BTrue | BFalse.

Notation "z ̇" := (proj1_sig z) (at level 0) : definition_scope.
Notation "z 'ⁱⁿᵗ'" := (exist Int.inRange z) (at level 99) : definition_scope.


Fact x_of_z_to_z_is_x : forall x irx, (x ̇ ⁱⁿᵗ irx) = x.
Proof.
    intros. destruct x. simpl. f_equal. unfold Int.inRange in *. 
    simpl in *.  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.
    

Inductive mpz_val := Defined (z:Z) :> mpz_val | Undefined (z:Z).


(* Coercion ir_z (x:Z) ir : 𝕍 := VInt (x ⁱⁿᵗ ir). *)
Coercion int_option_loc (l:nat) :=  Some l.
Coercion v_int (mi:Int.MI) : 𝕍 := Def (VInt mi). 
Coercion def_v_mpz (l:nat) : 𝕍 := Def (VMpz (Some l)). 
Coercion mpz_loc (l:location) : 𝕍 := VMpz (Some l).
Coercion gmp_s_ext (s:_gmp_statement) := S_Ext s (T:=_gmp_t).
Coercion fsl_s_ext (s:_fsl_statement) := S_Ext s (T:=_gmp_t).
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
| Some (VInt _) | Some (UInt _)  => Some C_Int
| Some (VMpz _) | Some (UMpz _) => Some (T_Ext Mpz)
| None => None
end.


Fixpoint exp_vars {T:Set} (exp : @_c_exp T) : list id := match exp with 
| Zm z => nil
| C_Id v _ => v::nil
| BinOpInt le _ re | BinOpBool le _ re => exp_vars le ++ exp_vars re
end.

Fixpoint stmt_vars {T S:Set} (stmt : @_c_statement T S) : list id := match stmt with 
| Skip => nil 
| Assign var e => var::exp_vars e
| FCall var f args => var::List.flat_map exp_vars args
| PCall f args => List.flat_map exp_vars args
| Seq s1 s2 =>  stmt_vars s1 ++ stmt_vars s2
| If cond then_ else_ =>  exp_vars cond ++ stmt_vars then_ ++ stmt_vars else_
| While cond s => exp_vars cond ++ stmt_vars s 
| PAssert e => exp_vars e
| Return e  => exp_vars e 
| Decl (C_Decl ty id) => id::nil
| S_Ext s => nil
end.


Definition 𝓜 := location ⇀ mpz_val. 
Definition Ωᵥ : Type := 𝓥 ⇀ 𝕍.
Definition Ωₗ : Type := 𝔏 ⇀ ℤ.

Record Ω := mkΩ {vars :> Ωᵥ ;  binds :> Ωₗ}.
Definition empty_Ω  : Ω := {|vars:=⊥;binds:=⊥|}.
#[export] Instance etaΩ : Settable _ := settable! mkΩ <vars ; binds>.

Record Env := mkEnv {env :> Ω ;  mstate :> 𝓜}.
Definition empty_env : Env := {|env:=empty_Ω;mstate:=⊥|}.
#[export] Instance etaEnv : Settable _ := settable! mkEnv <env ; mstate>.

Fact abcd {A B : Type} (proj : Env -> (A ⇀ B) ) `{EqDec A} `{Setter Env (A ⇀ B) proj} (ev : Env) (v : A) : forall (x1 x2 : A) (y1 y2 : B), 
    (ev <| proj ::= {{x1\y1}} |> <| proj ::= {{x2\y2}} |> ).(proj) v 
    = 
    (ev <|  proj ::= {{x1\y1,x2\y2}} |>).(proj) v.
Proof. 
intros. compute. destruct H. admit.
Admitted. 

Definition apply_env (a : Ω) (v : 𝓥) : option 𝕍 := a.(vars) v.
Coercion apply_env : Ω >-> Funclass.

Definition apply_mem (a : Ω) (l : 𝔏) : option Z := a.(binds) l.
(* Coercion apply_mem : Ω >-> Funclass. *) (* can't use same coercion path *)

Fact type_of_value_env : forall (env:Ω) (var:𝓥), type_of_value (env var) <> None -> env var <> None.
Proof.
    intros env var Hty. now destruct (env var) as [v|].
Qed.



(* the first mpz location is 0 and is then incremented by one *)
Inductive fresh_location (mem : 𝓜)  : location -> Prop :=  
    | First : 
        (forall l, mem l = None) -> 
        fresh_location mem O

    | New (max:location) : 
        max ∈ mem ->
        (forall l, mem l <> None -> max >= l)%nat ->
        fresh_location mem (max+1)%nat
. 

Fact fresh_location_deterministic : forall mem l l', 
    fresh_location mem l /\ fresh_location mem l' ->
    l = l'.
Proof.
    intros mem l l' [Hfl Hfl']. inversion Hfl ; inversion Hfl'. 
    - easy.
    - subst. destruct H1.  specialize H with max. congruence. 
    - subst. destruct H.  specialize H0 with max. congruence. 
    - clear Hfl Hfl'. subst. f_equal. inversion H. inversion H2. 
        specialize H3 with max. specialize H0 with max0.
        assert (mem max0 <> None) by congruence. assert (mem max <> None) by congruence.
        apply H0 in H5. apply H3 in H6. now apply Nat.le_antisymm. 
Qed.

Fact fresh_location_no_alias : forall mem l , 
    fresh_location mem l -> mem l = None.
Proof.
intros. destruct mem eqn:X.
    - inversion H.
        + specialize H0 with O. congruence.
        + exfalso. destruct H0. specialize H1 with (max + 1)%nat.
            assert (Hsome: mem (max + 1)%nat <> None) by congruence. apply H1 in Hsome. auto with zarith. 
    - easy.
Qed.


Definition Uτ (v:𝕍) : option (@_c_type Empty_set) := match v with 
    | UInt _ => Some C_Int 
    | _ => None
end
.


Definition inUτ v : bool := if Uτ v then true else false.

Definition zero :=  0ⁱⁿᵗ zeroinRange.
Definition one := 1ⁱⁿᵗ oneinRange.
Definition sub_one := (-1)ⁱⁿᵗ suboneinRange.



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


Inductive param_env_partial_order (var: 𝓥) (env env':Ω) : Prop :=
| EsameInt n : 
    env var = Some (Def (VInt n))
    ->  env' var = Some (Def (VInt n))
    -> param_env_partial_order var env env'
| EsameMpz l : 
    env var = Some (Def (VMpz l))
    -> env' var = Some (Def (VMpz l))
    -> param_env_partial_order var env env'
| EundefInt n: env var = Some (Undef (UInt n))
    -> env' var = Some (Undef (UInt n)) \/  (exists n, env' var = Some (Def (VInt n)))
    -> param_env_partial_order var env env'
| EundefMpz n : env var = Some (Undef (UMpz n))
    -> env' var = Some (Undef (UMpz n)) \/  (exists n, env' var = Some (Def (VMpz n)))
    -> param_env_partial_order var env env'
| Enone : env var = None -> param_env_partial_order var env env'
.

#[global] Hint Constructors param_env_partial_order : rac_hint.


Definition env_partial_order env env' := forall v, param_env_partial_order v env env'.

Definition mems_partial_order (mem mem':𝓜) : Prop := forall l i, mem l = Some i ->  mem' l = Some i.

Declare Scope env_scope.
Delimit Scope env_scope with env.
Declare Scope mem_scope.
Delimit Scope mem_scope with mem.
Declare Scope env_mem_scope.
Delimit Scope env_mem_scope with envmem.


Infix "⊑" := env_partial_order : env_scope.

Infix "⊑" := mems_partial_order : mem_scope.

Infix "⊑" :=  ( fun e e' => (e.(env) ⊑ e'.(env))%env /\ (e.(mstate) ⊑ e'.(mstate))%mem) : env_mem_scope.

Fact refl_env_partial_order : reflexive Ω env_partial_order.
Proof.
    intros [v l] var. destruct (v var) as [val |] eqn:res. induction val.
    - destruct v0.
        * now apply EsameInt with n.
        * now apply EsameMpz with l0. 
    - destruct uv.
        * apply EundefInt with n; auto.
        * apply EundefMpz with l0; auto.
    - apply Enone ; auto.
Qed.


Fact trans_env_partial_order : transitive Ω env_partial_order.
Proof.
    intros  [v l] [v' l'] [v'' l'']  H1 H2 var. destruct H1 with var ; specialize (H2 var).
    * apply EsameInt with n. easy. inversion H2 ; congruence.
    * apply EsameMpz with l0 ; inversion H2; congruence.
    * apply EundefInt with n.
        + assumption.
        + inversion H2 ; destruct H0 ; eauto ; try congruence ; try (destruct H0 ; congruence).
    * apply EundefMpz with n. easy. inversion H2; destruct H0; try congruence || (destruct H0 ; congruence). right. now exists l0.
    * now apply Enone.
Qed.

Fact antisym_env_partial_order : forall env env',
    env_partial_order env' env /\ env_partial_order env env' -> forall v, env v = env' v.

Proof.
    intros env env' [H1 H2] v. specialize (H1 v). inversion H1 ; try congruence.
    - destruct H0 ; destruct H0;  destruct H2 with v; congruence.
    - destruct H0 ; destruct H0;  destruct H2 with v; congruence.
    - destruct H2 with v; destruct H0 ; try congruence  || (destruct H3; destruct H0 ; congruence).
Qed.



#[global] Add Relation Ω env_partial_order
    reflexivity proved by refl_env_partial_order
    transitivity proved by trans_env_partial_order as Renv.


Fact refl_mem_partial_order : reflexive 𝓜 mems_partial_order.
Proof.
    intros mem l. trivial. 
Qed.    

Fact trans_mem_partial_order : transitive 𝓜 mems_partial_order.
Proof.
    intros mem mem' mem'' H1 H2 l. destruct (mem l) eqn:L.
    - erewrite H2 ; eauto. 
    - discriminate.
Qed.


Fact antisym_mem_partial_order : forall mem mem', 
    mems_partial_order mem mem' /\ mems_partial_order mem' mem -> forall l, mem l = mem' l.
Proof.
    intros mem mem' [H1 H2] l. destruct (mem l) eqn:Heqn.
    - now apply H1 in Heqn.
    - destruct (mem' l) eqn:Heqn'. apply H2 in Heqn'.
        + congruence.
        + easy.
Qed.


#[global] Add Relation 𝓜 mems_partial_order
    reflexivity proved by refl_mem_partial_order 
    transitivity proved by trans_mem_partial_order as mem.

    
Fact refl_env_mem_partial_order : forall ev, (ev ⊑ ev)%envmem.
Proof.
    intros. split.
    - pose refl_env_partial_order as r. now unfold reflexive in r.
    - pose refl_mem_partial_order as r. now unfold reflexive in r.
Qed.

Open Scope utils_scope.
(* invariants for routine translation *)

(* notations *)
Inductive add_var (e : Env) (τ:gmp_t) (v:id) (z:Z) : Env -> Prop :=
| typeInt irz : 
    τ = C_Int ->
    add_var e τ v z (e <| env ; vars ::= {{v\(VInt (z ⁱⁿᵗ irz)) :𝕍}} |>)%utils

| typeMpz x (n:Int.MI) :
    τ  = Mpz ->
    (forall v',  e v' <> Some (Def (VMpz (Some x))) )->
    add_var e τ v z 
    ( e 
    <| env ; vars ::= {{ v\Def (VMpz (Some x)) }} |>
    <| mstate ::= {{x\Defined (proj1_sig n)}} |> 
    )
.

Example add_var_int : forall (ir3 :Int.inRange 3),
add_var empty_env C_Int "y" 3 (empty_env  <| env ; vars := ⊥{"y"\Def (VInt ( 3ⁱⁿᵗ ir3))} |>).
Proof. now constructor. Qed.

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

Inductive add_var_𝐴 (e : Env) : 𝐴 -> Env -> Prop := 
| add_var_nil : add_var_𝐴  e nil e

| add_var_cons t v z A e': 
    True -> 
    add_var e t v z e' -> 
    add_var_𝐴 e A e'
.



Example add_var_mpz  : 
add_var empty_env Mpz "y" 3  
    ( empty_env 
        <| env ; vars := ⊥{"y"\Def 1%nat} |>
        <| mstate := ⊥{(1%nat)\(Defined 3)} |>
    )
.
Proof.
    assert (ir3: Int.inRange 3). easy.
    now apply (typeMpz empty_env Mpz "y" 3 1%nat (3ⁱⁿᵗ ir3)).
Qed.



(* Compute add_var_𝐴 (⊥,⊥) ⊥ nil. *)

Example envaddnil : add_var_𝐴 empty_env nil empty_env.
Proof.
 constructor.
Qed.

Open Scope list.

Example envaddone : add_var_𝐴 empty_env  ((T_Ext Mpz, "y", 3)::nil) 
    (empty_env 
        <| env ; vars := ⊥{"y"\Def (VMpz 1%nat)} |>
        <| mstate := ⊥{1%nat\(Defined 3)} |>
    )
.
Proof.
    assert (ir3: Int.inRange 3). easy.
    eapply add_var_cons with (t:=Mpz) (v:="y") (z:=3).
 - auto.
 - apply (typeMpz empty_env Mpz "y" 3 1%nat (3ⁱⁿᵗ ir3)).
    * reflexivity.
    * intro v. intro contra. inversion contra.
Qed.


(* synchronicity invariant *)
Definition I1 (env:Ω) (ienv:Γ) := ((dom env.(binds)) = (dom (fst ienv) + dom (snd ienv)))%utils.

(* suitability invariant *)
Definition I2 (env:ψ) := True. (* todo *)


Inductive pgrm_var_representation (iop:ϴ) (e : Env) (ienv:Γ) : Env -> Prop :=
| empty ΩΓ 𝓜Γ :   
    I1 e ienv ->
    let A := nil  (* { (iop ((snd ienv) v), v, (snd env) v ) | v in dom ienv  } *)
    in
    add_var_𝐴 e A {|env:=ΩΓ; mstate:=𝓜Γ|} -> 
    pgrm_var_representation iop e ienv{|env:=ΩΓ; mstate:=𝓜Γ|}
.

(* Definition well_formed_program :=
    - all variables declared before usage
    - all functions defined before called
    - well typed
*)
