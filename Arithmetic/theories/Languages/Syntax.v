From Coq Require Import Strings.String.
From RAC.Languages Require Export MiniC.Syntax MiniGMP.Syntax MiniFSL.Syntax.
From RAC Require Import Utils.



Import FunctionalEnv.

Definition c_statement := @_c_statement Empty_set Empty_set.

Definition fsl_statement := @_c_statement _fsl_statement Empty_set.
Coercion fsl_s_ext (s:_fsl_statement) : fsl_statement := S_Ext s (T:=Empty_set).


Definition gmp_statement := @_c_statement _gmp_statement _gmp_t. 
Notation 𝐒 := gmp_statement. (* program statements *)
Coercion gmp_s_ext (s:_gmp_statement) : 𝐒 := S_Ext s (T:=_gmp_t).


Definition c_decl := @_c_decl Empty_set.
(* fsl_decl defined earlier *)


Definition fsl_pgrm := @_c_program _fsl_routine _fsl_statement Empty_set.
Definition rac_pgrm := @_c_program Empty_set _gmp_statement _gmp_t.



Definition 𝔉 : Type :=  𝔏 ⇀ (𝔏* ⨉ ℨ). (* logic functions *)
Definition 𝔓 : Type :=  𝔏 ⇀ (𝔏* ⨉  𝔅). (* predicates *)



(****************** Expression Typing ******************)


(* 
    ty the function that gives the type of an expression :
    - it must recursively evaluate to the same type for binary operators 
    - if this is not the case, void type is used to notify of an error

    requires 
*)
Fixpoint ty {T : Set} (e: @_c_exp T) : @_c_type T := 
    match e with 
    | Zm _  => C_Int
    | C_Id _ t => t
    | BinOpInt l _ r  | BinOpBool l _ r => 
        match (ty l, ty r) with
        | (C_Int,C_Int) => C_Int
        | _ => Void
        end
    end
.

(* Fact eq_dec_ty {T: Set} (t1 t2 : @_c_type T) {H : EqDec T} : {t1 = t2} + {t1 <> t2}. inversion H. decide equality. Qed.
Fact eq_dec__gmp_t (x y : _gmp_t) : {x = y} + {x <> y}. decide equality.  Qed.
Fact eq_dec_gmp_t (x y : gmp_t) : {x = y} + {x <> y}. decide equality. apply eq_dec__gmp_t. Qed.
#[global] Instance eqdec_gmp_t: EqDec gmp_t := {eq_dec := eq_dec_gmp_t}. *)


Fact mpz_exp_is_var : forall (e:_c_exp), ty e = T_Ext Mpz ->  exists x, (e = C_Id x (T_Ext Mpz))%type.
Proof. 
    intros. destruct e eqn:E.
    3,4: simpl in H ; destruct (ty _c1); try congruence; destruct (ty _c2); congruence.  
    - now exists EmptyString. 
    - exists var. unfold ty in H. now rewrite H. 
Qed.



Fixpoint exp_vars {T:Set} (exp : @_c_exp T) : list id := match exp with 
| Zm z => nil
| C_Id v _ => v::nil
| BinOpInt le _ re | BinOpBool le _ re => exp_vars le ++ exp_vars re
end.

Fixpoint stmt_vars {T S:Set} (stmt : @_c_statement T S) (ext_stmt_vars: T -> list id) : list id := match stmt with 
| Skip => nil 
| Assign var e => var::exp_vars e
| FCall var f args => var::List.flat_map exp_vars args
| PCall f args => List.flat_map exp_vars args
| Seq s1 s2 =>  stmt_vars s1 ext_stmt_vars ++ stmt_vars s2 ext_stmt_vars
| If cond then_ else_ =>  exp_vars cond ++ stmt_vars then_ ext_stmt_vars ++ stmt_vars else_ ext_stmt_vars
| While cond s => exp_vars cond ++ stmt_vars s ext_stmt_vars
| PAssert e | Return e => exp_vars e
| S_Ext s => ext_stmt_vars s
end.


Unset Guard Checking. (* fixme *)
Fixpoint _gmp_stmt_vars (stmt:_gmp_statement) : list id := match stmt with 
| GMP_Scope _ s => stmt_vars s _gmp_stmt_vars
| Init z | Set_s z _  | Clear z  => z::nil
| Set_i z e  => z::exp_vars e
| Set_z z1 z2 | Coerc z1 z2 => z1::z2::nil
| GMP_Add l r res | GMP_Sub l r res | GMP_Mul l r res | GMP_Div l r res | Comp res l r => l::r::res::nil
end.

Set Guard Checking.

Definition _fsl_stmt_vars (stmt:_fsl_statement) : list id := 
  let _stmt_vars:= fix predicate_vars (p:predicate) : list id := match p with
    | P_True | P_False => nil
    | P_BinOp t1 _ t2 => (term_vars t1 ++ term_vars t2)%list
    | P_Not p => predicate_vars p
    | P_Disj p1 p2 => (predicate_vars p1 ++ predicate_vars p2)%list
    | P_Call _ args => List.flat_map term_vars args
    end
  with term_vars (t:fsl_term) : list id := match t with
    | T_Z _ => nil
    | T_Id x _ => (x::nil)%list
    | T_BinOp t1 _ t2 => (term_vars t1 ++ term_vars t2)%list
    | T_Cond p t1 t2 => (predicate_vars p ++ term_vars t1 ++ term_vars t2)%list
    | T_Call _ targs => List.flat_map term_vars targs
    end
  for predicate_vars
  in
  match stmt with 
  | LAssert p => _stmt_vars p
 end.


Definition Empty_ext_stmt_vars {T} : T -> list id := fun _ => nil.


Definition c_stmt_vars s := stmt_vars (T:=Empty_set) (S:=Empty_set) s Empty_ext_stmt_vars.


Definition gmp_stmt_vars s := stmt_vars (T:=_gmp_statement) (S:=_gmp_t) s _gmp_stmt_vars.


(****************** Convertion ********************)



Definition c_t_to_gmp_t (t:@_c_type Empty_set) : gmp_t := match t with
    | C_Int => C_Int
    | Void => Void
    | T_Ext False => Void (* not possible *)
    end
.

(* returns empty string if not an mpz var *)
Definition gmp_ty_mpz_to_var (e: gmp_exp) : Notations.id := match e with
    | C_Id var t =>  match t with T_Ext Mpz => var | _ => "" end
    | _ => ""
end.


Fixpoint c_exp_to_gmp_int_exp (e: c_exp) : gmp_exp := match e with
| Zm z => Zm z
| C_Id v t => match t with 
    | Void => C_Id v Void 
    | C_Int => C_Id v C_Int
    | T_Ext False => C_Id v Void 
    end
| BinOpInt l op r => let (l',r') := (c_exp_to_gmp_int_exp l,c_exp_to_gmp_int_exp r) in BinOpInt l' op r'
| BinOpBool l op r => let (l',r') := (c_exp_to_gmp_int_exp l,c_exp_to_gmp_int_exp r) in BinOpBool l' op r'
end.



(* returns C_id void if not convertible *)
Fixpoint gmp_exp_to_c_exp  (e:gmp_exp) : c_exp := match e with
    | Zm z => Zm z
    | C_Id var t =>  match t with C_Int => C_Id var C_Int | _ => C_Id var Void end
    | BinOpInt le op re => 
    let (le,re) := (gmp_exp_to_c_exp le,gmp_exp_to_c_exp re) in
    BinOpInt le op re
    | BinOpBool le op re => 
    let (le,re) := (gmp_exp_to_c_exp le,gmp_exp_to_c_exp re) in
    BinOpBool le op re
end.

Fact gmp_exp_c_exp_same_exp_vars e : exp_vars (gmp_exp_to_c_exp e) = exp_vars e.
Proof. 
    induction e.
    - reflexivity.
    - destruct ty0 ;  reflexivity.
    - simpl. rewrite IHe1,IHe2. reflexivity.
    - simpl. rewrite IHe1,IHe2. reflexivity.
Qed.

