From RAC.Languages Require Export MiniC.Syntax MiniGMP.Syntax MiniFSL.Syntax.
From RAC Require Import Utils.
From Coq Require Import Strings.String.


Definition c_statement := @_c_statement Empty_set Empty_set.

Definition fsl_statement := @_c_statement _fsl_statement Empty_set.
Coercion fsl_s_ext (s:_fsl_statement) : fsl_statement := S_Ext s (T:=Empty_set).


Definition gmp_statement := @_c_statement _gmp_statement _gmp_t. 
Notation 𝐒 := gmp_statement. (* program statements *)
Coercion gmp_s_ext (s:_gmp_statement) : 𝐒 := S_Ext s (T:=_gmp_t).


Definition c_decl := @_c_decl Empty_set.
Definition gmp_decl := @_c_decl _gmp_t.
(* fsl_decl defined earlier *)


Definition fsl_pgrm := @_c_program _fsl_routine _fsl_statement Empty_set.
Definition rac_pgrm := @_c_program Empty_set _gmp_statement _gmp_t.



Definition 𝔉 : Type :=  𝔏 ⇀ (𝔏 ⃰ ⨉ ℨ). (* logic functions *)
Definition 𝔓 : Type :=  𝔏 ⇀ (𝔏 ⃰ ⨉ 𝔅). (* predicates *)





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
    - now exists "". 
    - exists var. unfold ty in H. now rewrite H. 
Qed.



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
| S_Ext s => nil
end.


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

