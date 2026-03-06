From Coq Require Import Strings.String.
From RAC Require Import Utils.
From RAC.Languages Require Import Syntax Semantics.  
From RAC.Languages Require Export MiniC.Facts MiniC.Lemmas MiniGMP.Facts MiniGMP.Lemmas.




(* Additionnal facts *)

Fact mpz_exp_is_var : forall (e:c_exp), ty e = T_Ext Mpz ->  exists x, e = C_Id x (T_Ext Mpz).
Proof. 
    intros. destruct e eqn:E.
    3,4: simpl in H ; destruct (ty c1); try congruence; destruct (ty c2); congruence.  
    - now exists EmptyString. 
    - exists var. unfold Syntax.ty in H. now rewrite H. 
Qed.


From Coq Require Import Program.Equality. (* axiom eq_rect_eq *)


Fact ty_int_gmp_c_exp_equiv (e:gmp_exp): forall env v, 
    ty e = C_Int -> 
    (env |= gmp_exp_to_c_exp e => v)%csem <-> generic_exp_sem env e v.
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


Fact flatten_noseq_noskip {S T} s : List.Forall (fun i => i <> Skip /\ forall s1 s2, i <> @Seq S T s1 s2) (@flatten S T s).
Admitted.

(* Fact flatten_unflatten {S T} {ext_exp} {ext_stmt} {ext_used_stmt_vars} : forall f e e' s, 
    @generic_stmt_sem S T ext_exp ext_stmt ext_used_stmt_vars f e s e' ->
    @generic_stmt_sem S T ext_exp ext_stmt ext_used_stmt_vars f e (unflatten (flatten s)) e.
Admitted. 

Fact flatten_unique {S T} {ext_exp} {ext_stmt} {ext_used_stmt_vars} : forall s s' f e e', 
    flatten s = flatten s' ->
    @generic_stmt_sem S T ext_exp ext_stmt ext_used_stmt_vars f e s e' ->
    @generic_stmt_sem S T ext_exp ext_stmt ext_used_stmt_vars f e s' e'.
Proof.
Admitted.
*)


Fact gmp_exp_c_exp_same_used_exp_vars e {T} : @used_exp_vars T (gmp_exp_to_c_exp e) = used_exp_vars e.
Proof. 
    induction e.
    - reflexivity.
    - destruct ty ;  reflexivity.
    - simpl. rewrite IHe1,IHe2. reflexivity.
    - simpl. rewrite IHe1,IHe2. reflexivity.
Qed.
