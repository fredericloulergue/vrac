From RAC Require Import Notations.
From RAC Require Import Utils.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Strings.String.
Open Scope Z_scope.
Open Scope fsl_scope.

Inductive p_type := PInt | Void.
Inductive l_type := LInt | Integer.

Inductive c_binop_int := Add | Min | Mul | Div.
Inductive c_binop_bool :=  Lt | Le | Gt | Ge | Eq | NEq.

Inductive fsl_binop_bool :=  FSLLt | FSLLe | FSLGt | FSLGe | FSLEq | FSLNEq.
Inductive fsl_binop_int := FSLAdd | FSLMin  | FSLMul  | FSLDiv.


Definition c_binop_bool_model (x:c_binop_bool) : Z -> Z -> Prop := match x with
    | Lt => Z.lt
    | Le => Z.le
    | Gt => Z.gt
    | Ge => Z.ge
    | Eq => Z.eq
    | NEq => fun b1 b2 => ~ (Z.eq b1 b2)
end.
Notation "◁" := c_binop_bool_model.

Definition c_binop_int_model (x:c_binop_int) : Z -> Z -> Z := match x with
    | Add => Z.add
    | Min => Z.min
    | Mul => Z.mul
    | Div => Z.div
end.
Notation "⋄" := c_binop_int_model.

Notation id := string.

Inductive mini_c_exp :=
    | Zm (z : Z)
    | Id (id : string)
    | BinOpInt (exp : mini_c_exp) (op:c_binop_int) (exp : mini_c_exp)
    | BinOpBool (exp : mini_c_exp) (op:c_binop_bool) (exp : mini_c_exp)
    .

     Inductive mini_fsl.
     
     Inductive c_statement :=
         | Skip
         | Assign (vname:id) (exp: mini_c_exp)
         | FCall (var:id) (fname:id) (args: list mini_c_exp)
         | PCall  (pname:id) (args: list mini_c_exp)
         | Seq (s1 : c_statement) (s2 : c_statement)
         | If (cond:mini_c_exp) (_then:c_statement) (_else:c_statement)
         | While (cond:mini_c_exp) (body:c_statement)
         | PAssert (e:mini_c_exp)
         | LAssert (a:mini_fsl)
         | Return (e:mini_c_exp)
         .
     
     
     (* begin mini-GMP *)
     Inductive t_ext := Ptype (t:p_type) | String | tMpz.
     
     Inductive g_statement := 
         | Init (id:id)
         | Set_i (id:id) (e:mini_c_exp)
         | Set_s (id:id) (l:string)
         | Set_z (lid rid:id)
         | Clear (id:id)
         | GAdd (lid rid res :id)
         | GSub (lid rid res :id)
         | GMul (lid rid res :id)
         | GDiv (lid rid res :id)
         | Comp (res lid rid :id) 
         | Coerc (res n : id)
         .
     
     Inductive statement := SMpz (s:g_statement) | SCommand (c:c_statement).
     
     (* end mini-GMP *)
     
     
     
     Inductive p_decl :=  PDecl (ty:p_type) (id:id).
     Inductive l_decl :=  LDecl (ty:t_ext) (id:id).
     
     
     Inductive predicate :=
         | FSLTrue
         | FSLFalse
         | Not (t:mini_fsl_term)
         | Disj (p1:predicate) (p2:predicate)
         | FSLPCall (name:id) (args:list l_decl)
         | FSLBinOpBool (t1: mini_fsl_term) (op:fsl_binop_bool) (t2 : mini_fsl_term)
     
     with mini_fsl_term :=
         | FSLZ (n:Z)
         | FSLId (id:string)
         | FSLBinOpInt (t1 : mini_fsl_term) (op:fsl_binop_int) (t2 : mini_fsl_term)
         | Conditional (cond:predicate) (_then:mini_fsl_term) (_else:mini_fsl_term)
         .
     
     
     Inductive mini_c_routines :=
         | PFun (rt:p_type) (name:id) (args: list p_decl) (decl: list p_decl ) (body:statement)
         | LFun (rt:l_type) (name:id) (args:list l_decl)
         | Predicate (name:id) (p:mini_fsl_term)
         .
     
     Inductive mini_c := Program (decls: list p_decl)  (routines: list mini_c_routines).
     

Definition V : Set := id. (* program variables *)

#[global] Instance eqdec_v : EqDec V := {eq_dec := string_dec}.

Definition S : Set := c_statement. (* program statements *)
Definition L : Set := l_decl. (* logic variables *)
Definition Z : Set := mini_fsl_term. (* logical terms *)
Definition B : Set := predicate. (* predicates *)
Definition T : Set := t_ext. (* minigmp types *)

Definition F : V ⇀ (V^* -> S). Admitted. (* program functions *)
Definition P : V ⇀ (V^* -> S). Admitted. (* program procedures *)
Definition Fl :  L ⇀ (L^* -> Z). Admitted. (* logic functions *)
Definition Bl :  L ⇀ (L^* -> B). Admitted. (* predicates *)


(*

m_int M_int : lower and upper bounds of type int 
*)

Definition m_int : BinNums.Z := -10.
Definition M_int : BinNums.Z := 10.


Definition Int : Set := Z. (* set of type int, a machine integer (may overflow) *)


Definition Mpz  : Set :=  Empty_set.  (* memory location for value of type mpz *) 

Definition Uint  : Set := Empty_set. (* set of undefined values of type int *) 
Definition Umpz  : Set :=  Empty_set.  (* set of undefined values of type mpz *) 

(* Infix  "⊎" := Sets.Ensembles.Union (at level 10). *) 

(*set of values an expression may evaluate to *)
(* Definition Values : (Int * Mpz * Uint * Umpz)%type. *)

(* Inductive Values : Set := Int (n:Z) | Mpz (n:option Z) | Uint | Umpz.  *)

Inductive Values := VInt (n:Int) | VMpz (n:Mpz) | VUint (n:Uint) | VUMpz (n:Umpz) .

(*
(* integer from value *)
Definition z_of_Int : Int -> Z := fun x => match x with Int => 0 end.
*)

Definition M := Mpz ⇀ Z. (* memory state, i.e. current mpz value of given mem loc*)


Definition Ωᵥ := V ⇀ Values.
Definition Ωₗ := L ⇀ Values.

Definition Ω := (Ωᵥ * Ωₗ)%type. (* semantic env *)

Definition Γ  := mini_c_routines -> T. (* typing env *)


(* Module Todo.
Hypothesis type_soundness : forall (env:Ω) (t:Z), True.

Hypothesis convergence : forall (type_env:Γ) (r:mini_c_routines), 
    exists (t:T), type_env r = t.
End Todo. *)



