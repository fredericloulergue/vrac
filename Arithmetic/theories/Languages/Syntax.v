From Coq Require Import Strings.String.
From RAC.Languages Require Export MiniC.Syntax MiniGMP.Syntax MiniFSL.Syntax.
From RAC Require Import Utils.

Import FunctionalEnv.

#[local] Open Scope list.


Definition fsl_statement := @c_statement _fsl_statement Empty_set.
Coercion fsl_s_ext (s:_fsl_statement) : fsl_statement := S_Ext s (T:=Empty_set).


Definition gmp_statement := @c_statement _gmp_statement _gmp_t. 
Notation 𝐒 := gmp_statement. (* program statements *)
Coercion gmp_s_ext (s:_gmp_statement) : 𝐒 := S_Ext s (T:=_gmp_t).


Definition fsl_pgrm := @c_program _fsl_routine _fsl_statement Empty_set.
Definition rac_pgrm := @c_program Empty_set _gmp_statement _gmp_t.


Definition 𝔉 : Type :=  𝔏 ⇀ (𝔏★ ⨉ ℨ). (* logic functions *)
Definition 𝔓 : Type :=  𝔏 ⇀ (𝔏★ ⨉  𝔅). (* predicates *)



(****************** Expression Typing ******************)


(* 
    ty the function that gives the type of an expression :
    - it must recursively evaluate to the same type for binary operators 
    - if this is not the case, void type is used to notify of an error

    requires 
*)
Fixpoint ty {T : Set} (e: @c_exp T) : @c_type T := 
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

Fact eq_dec_ty {T: Set}  {H : EqDec T} : EqDec (@c_type T). red. decide equality. Qed.
Fact eq_dec__gmp_t  : EqDec _gmp_t. red. decide equality.  Qed.
Fact eq_dec_gmp_t : EqDec gmp_t. red. decide equality. apply eq_dec__gmp_t. Qed.
#[global] Instance eqdec_gmp_t: EqDec gmp_t := {eq_dec := eq_dec_gmp_t}.

Section Vars.

    Context {F S T : Set}.
    Variables (ext_used_stmt_vars: S -> StringSet.t) (ext_used_fun_vars: F -> StringSet.t).

    Fixpoint used_exp_vars (exp : @c_exp T) : StringSet.t := match exp with 
    | Zm z => StringSet.empty
    | C_Id v _ => StringSet.singleton v
    | BinOpInt le _ re | BinOpBool le _ re => StringSet.union (used_exp_vars le) (used_exp_vars re)
    end.


    Fixpoint used_stmt_vars (stmt : @c_statement S T)  : StringSet.t  := match stmt with 
    | Skip => StringSet.empty 
    | Assign var e => StringSet.add var (used_exp_vars e)
    | FCall var f args => StringSet.add var (StringSet.union_list (List.map used_exp_vars args))
    | PCall f args => StringSet.union_list (List.map used_exp_vars args)
    | Seq s1 s2 =>  StringSet.union (used_stmt_vars s1) (used_stmt_vars s2)
    | If cond then_ else_ =>  StringSet.union (StringSet.union (used_exp_vars cond) (used_stmt_vars then_)) (used_stmt_vars else_)
    | While cond s => StringSet.union (used_exp_vars cond) (used_stmt_vars s)
    | PAssert e | Return e => used_exp_vars e
    | Scope _ s => used_stmt_vars s
    | S_Ext s => ext_used_stmt_vars s
    end.

    Definition used_fun_vars(r : @c_routine F S T) : StringSet.t := match r with
    | PFun _ _ _ _ b => used_stmt_vars b
    | F_Ext f => ext_used_fun_vars f
    end.

    Definition used_pgrm_vars (P : @c_program F S T) : StringSet.t := 
        StringSet.union_list (List.map used_fun_vars (snd P))
    .

End Vars.


Definition _gmp_used_stmt_vars (stmt:_gmp_statement) : StringSet.t := match stmt with 
| Init z | Set_s z _  | Clear z  => StringSet.singleton z
| Set_i z e  => StringSet.add z (used_exp_vars e)
| Set_z z1 z2 | Coerc z1 z2 => StringSet.union (StringSet.singleton z1) (StringSet.singleton z2)
| GMP_Add l r res | GMP_Sub l r res | GMP_Mul l r res | GMP_Div l r res | Comp res l r => 
    StringSet.union (StringSet.union (StringSet.singleton l) (StringSet.singleton r)) (StringSet.singleton res)
end.

Fixpoint fsl_used_term_vars (t: fsl_term) : StringSet.t := match t with
    | T_Z _ => StringSet.empty
    | T_Id x _ => StringSet.singleton x
    | T_BinOp t1 _ t2 => StringSet.union (fsl_used_term_vars t1) (fsl_used_term_vars t2)
    | T_Cond p t1 t2 => StringSet.union (StringSet.union (fsl_used_predicate_vars p) (fsl_used_term_vars t1)) (fsl_used_term_vars t2)
    | T_Call _ targs => (StringSet.union_list (List.map fsl_used_term_vars targs))
    end
with fsl_used_predicate_vars (p:predicate) : StringSet.t := match p with
        | P_True | P_False => StringSet.empty
        | P_BinOp t1 _ t2 => StringSet.union (fsl_used_term_vars t1) (fsl_used_term_vars t2)
        | P_Not p => fsl_used_predicate_vars p
        | P_Disj p1 p2 => StringSet.union (fsl_used_predicate_vars p1) (fsl_used_predicate_vars p2)
        | P_Call _ args => (StringSet.union_list (List.map fsl_used_term_vars args))
end.


Definition _fsl_used_stmt_vars '(LAssert p:_fsl_statement) : StringSet.t := fsl_used_predicate_vars p.


Definition _fsl_used_fun_vars (f:_fsl_routine) : StringSet.t := match f with 
| LFun _ _ _ b => fsl_used_term_vars b
|Predicate _ _ b => fsl_used_predicate_vars b
end.



Definition Empty_ext_used {T} : T -> StringSet.t  := fun _ => StringSet.empty.


Definition c_used_stmt_vars := @used_stmt_vars Empty_set Empty_set Empty_ext_used.
Definition gmp_used_stmt_vars := @used_stmt_vars _gmp_statement _gmp_t _gmp_used_stmt_vars.
Definition gmp_used_prgrm_vars := @used_pgrm_vars Empty_set _gmp_statement _gmp_t  _gmp_used_stmt_vars Empty_ext_used.
Definition fsl_used_stmt_vars := @used_stmt_vars _fsl_statement Empty_set _fsl_used_stmt_vars.
Definition fsl_used_prgrm_vars := @used_pgrm_vars _fsl_routine _fsl_statement Empty_set  _fsl_used_stmt_vars _fsl_used_fun_vars.


(****************** Convertion ********************)



Definition c_t_to_gmp_t (t:@c_type Empty_set) : gmp_t := match t with
    | C_Int => C_Int
    | Void => Void
    | T_Ext False => Void (* not possible *)
    end
.

(* returns empty string if not an mpz var *)
Definition gmp_ty_mpz_to_var (e: gmp_exp) : Prelude.id := match e with
    | C_Id var t =>  match t with T_Ext Mpz => var | _ => "" end
    | _ => ""
end.


(* Fact gmp_ty_mpz_to_var_spec : ty e = Mpz ->  gmp_ty_mpz_to_var e =  *)

Fixpoint c_exp_to_gmp_int_exp {T} (e: @c_exp T) : gmp_exp := match e with
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
Fixpoint gmp_exp_to_c_exp {T} (e:gmp_exp) : @c_exp T := match e with
    | Zm z => Zm z
    | C_Id var t =>  match t with C_Int => C_Id var C_Int | _ => C_Id var Void end
    | BinOpInt le op re => 
    let (le,re) := (gmp_exp_to_c_exp le,gmp_exp_to_c_exp re) in
    BinOpInt le op re
    | BinOpBool le op re => 
    let (le,re) := (gmp_exp_to_c_exp le,gmp_exp_to_c_exp re) in
    BinOpBool le op re
end.


Definition c_decl_to_gmp_decl (d:@c_decl Empty_set) : gmp_decl := 
    let '(C_Decl t id) := d in C_Decl (c_t_to_gmp_t t) id
.

Fixpoint c_exp_to_gmp_exp (e:c_exp) : gmp_exp := match e with
    | Zm z => Zm z
    | C_Id var t => C_Id var (c_t_to_gmp_t t) 
    | BinOpInt le op re => 
        let (le,re) := (c_exp_to_gmp_exp le,c_exp_to_gmp_exp re) in
        BinOpInt le op re
    | BinOpBool le op re => 
        let (le,re) := (c_exp_to_gmp_exp le,c_exp_to_gmp_exp re) in
        BinOpBool le op re
    end
.

Definition extract_c_args {T} : @c_decl T★ -> 𝓥★ := List.map (fun d => let 'C_Decl _ x := d in x).
Definition extract_fsl_args : fsl_decl★ -> 𝓥★ := List.map (fun d => let 'FSL_Decl _ x := d in x).