Require Import Coq.Program.Equality. (* axiom eq_rect_eq *)
From RAC.Languages Require Import Syntax.
From RAC.Languages Require Export MiniC.Semantics MiniGMP.Semantics MiniFSL.Semantics.

Open Scope c_sem_scope.



Fact ty_int_gmp_c_exp_equiv {ext_exp} (e:gmp_exp): forall env v, 
    ty e = C_Int -> 
    (env |= gmp_exp_to_c_exp e => v)%csem <-> generic_exp_sem env e v (ext_exp:=ext_exp).
Proof with eauto with rac_hint.
    intros env v Hint. split; intro H.
    - dependent induction H; destruct e eqn:E; simpl in *; subst; try congruence; injection x as Hz; subst.
        1,2: now constructor.
        1,2,3: destruct (ty g1) eqn:TG1; try discriminate ; destruct (ty g2) eqn:TG2; try discriminate...
    - induction H ; simpl in *.
        1,2: now repeat constructor.
        1,2,3: destruct (ty e) eqn:TE1; try discriminate ; destruct (ty e') eqn:TE2; try discriminate; econstructor.
        1,3,6: now apply IHgeneric_exp_sem1.
        1,2,4: now apply IHgeneric_exp_sem2.
        1,2: assumption.
Qed.



Definition c_decl_to_gmp_decl (d:@_c_decl Empty_set) : gmp_decl := 
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




