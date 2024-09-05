From RAC Require Export Notations.
From Coq Require Import Strings.String ZArith.ZArith Setoids.Setoid Eqdep_dec Logic.FinFun.

Open Scope string_scope.
Open Scope Z_scope.
Open Scope utils_scope.
Create HintDb rac_hint.



Definition partial_function (X Y : Type) : Type := X -> option Y.
Definition empty_p {X Y:Type} := fun (_:X) => (None: option Y).

Infix "⨉" := prod (at level 99) : type_scope.
Infix "⇀" := partial_function : type_scope.
Notation "⊥" := empty_p : type_scope.
Notation "'ℤ'" := Z (at level 99) : type_scope.

Class EqDecC X := {eq_dec : EqDec X }.



Fact dec_neq_out_neq_in {X T : Type } `{EqDecC X}: forall (f : X -> T) (x x' : X)  , f x <> f x' -> x <> x'.
Proof.
    intros. destruct H as [eq_dec]; destruct (eq_dec x x') ; subst ; easy.
Qed.


#[global] Instance z_eq_dec : EqDecC Z := {eq_dec := Z.eq_dec}.
#[global] Instance eqdec_v : EqDecC 𝓥 := {eq_dec := string_dec}.
#[global] Instance eqdec_l : EqDecC 𝔏 := {eq_dec := string_dec}.

Definition p_map_front {X Y : Type} `{EqDecC X}  (f: X -> option Y) (xy:X * Y)   : X -> option Y :=
    fun i => if eq_dec (fst xy) i then Some (snd xy) else f i.

Definition p_map_back {X Y : Type} `{EqDecC X}  (xy:X * Y) (f: X -> option Y)  : X -> option Y :=
    p_map_front f xy.

#[global] Hint Unfold p_map_back : rac_hint.


Notation "f { xy , .. , xy' }" :=  (p_map_front .. (p_map_front f xy') .. xy ) : utils_scope.
Notation "'{{' xy , .. , xy' '}}'" := (fun f => p_map_back xy' .. (p_map_back xy f) .. ) : utils_scope. (* fixme: make same as the other*)

Fact p_map_single_back_front_eq {X Y : Type} `{EqDecC X} : 
    forall f x (y:Y) z , f{x\y} z = {{x\y}}f z.
Proof. auto. Qed.


Definition p_map_addall_front {X Y: Type} `{EqDecC X} env (lx:list X) (ly : list Y) :=
    List.fold_left (fun f xy => f {(fst xy) \ (snd xy)}) (List.combine lx ly) env
.

Definition p_map_addall_back {X Y: Type} `{EqDecC X} (lx:list X) (ly : list Y) env :=
    p_map_addall_front env lx ly
.

#[global] Hint Unfold p_map_addall_back : rac_hint.


Fact p_map_not_same {X T : Type } `{EqDecC X}: forall f (x x' : X) (v : T), x <> x' -> f{x'\v} x = f x.
Proof.
    intros. unfold p_map_front. simpl. destruct eq_dec.
    - now destruct H0. 
    - easy.
Qed.

#[global] Hint Resolve p_map_not_same : rac_hint.


Corollary p_map_not_same_eq {X T : Type } `{EqDecC X}: forall f (x x' : X) (v : T) (res : option T), x <> x' -> f{x'\v} x = res <-> f x = res.
Proof.
    split. 
    - intro H1. now rewrite p_map_not_same in H1.
    - intro H1.  erewrite <- p_map_not_same in H1.
        + apply H1.
        + assumption.
Qed.

#[global] Hint Resolve p_map_not_same_eq : rac_hint.


Fact p_map_same {X T : Type } `{EqDecC X}: forall f (x : X) (v : T), f{x\v} x = Some v.
Proof.
    intros. unfold p_map_front. simpl. now destruct eq_dec.
Qed.

#[global] Hint Resolve p_map_same : rac_hint.


Fixpoint fold_left2 {Acc A B : Type} (f : Acc -> A -> B -> Acc) (acc:Acc) (l1 : list A) (l2 : list B) : Acc := 
    match l1,l2 with
      | nil,nil => acc
      | cons b1 t1,cons b2 t2 => fold_left2 f (f acc b1 b2) t1 t2
      | _,_ => acc (* both lists must have the same length,
       otherwise computation will be interrupted when one of the list is empty but not the other *)
end.


Fact p_map_apply {X T T' : Type } `{EqDecC X} : forall env (x :X)  (v : T) (f : option T -> T'),  f (env{x\v} x)  = f (Some v).
Proof.
    intros env x v f. f_equal. apply p_map_same.
Qed.

Fact p_map_domain {X Y : Type } `{EqDecC X} (env : X -> option Y) (z : X) :
    forall x x' y z, env{x\y} x' = Some z -> x' = x \/ env x' = Some z.
Proof.
    intros. destruct (eq_dec x' x).
        + now left.
        +  rewrite p_map_not_same in H0 ; auto.
Qed.


Fact list_map_id_eq {A B} (f : A -> B): forall x x', 
    Injective f ->
    List.map f x = List.map f x' <-> x  = x'.
Proof.
    split; intros; subst; auto. generalize dependent x'. induction x.
    -  simpl. intros x'. destruct x'; [trivial|].  intros. simpl in H0. inversion H0.
    - intros. destruct x'; simpl in *; [inversion H0|]. inversion H0. f_equal; auto. 
Qed. 



Lemma bijective_injective {A B : Type} (f : A -> B) :
    Bijective f -> Injective f.
Proof.
    intros [g [H H']] x y e.
    rewrite <- (H x), <- (H y).
    now rewrite e.
Qed.

Lemma bijective_surjective {A B : Type} (f : A -> B) :
    Bijective f -> Surjective f.
Proof.
    intros [g [H H']] y. now exists (g y).
Qed.


Definition in_domain { X Y : Type} (f: X ⇀ Y) (x:X) := exists y, f x = Some y.
Definition not_in_domain { X Y : Type} (f: X ⇀ Y) (x:X) := f x = None.
Definition in_codomain { X Y : Type} (f: X ⇀ Y) (y:Y) := exists x, f x = Some y.
Definition not_in_codomain { X Y : Type} (f: X ⇀ Y) (y:Y) := forall x, f x <> Some y.


Notation "'dom' f" := (in_domain f) : utils_scope.

#[global] Hint Unfold in_domain : rac_hint.


Notation "x ∈ E" := (in_domain E x) (at level 99) : utils_scope.
Notation "x ∉ E" := (not_in_domain E x) (at level 99) : utils_scope.



Fact not_in_equiv { X Y : Type} (f: X ⇀ Y) (x:X) : (x ∉ f) <-> ~(x ∈ f).
Proof. 
    split; intros H.
    -intros contra. inversion H.  inversion contra. now rewrite H0 in H1.
    -destruct (f x) eqn:Fx.
        +  exfalso.  apply H. now exists y.
        + assumption.
Qed. 



Fact in_domain_dec { X Y : Type} (f: X ⇀ Y) (x:X) : Decidable.decidable (x ∈ f). 
Proof. 
    destruct (f x) eqn:Fx.
    -  left. now exists y.
    - right.  intros contra. destruct contra. now rewrite H in Fx.
Qed. 




Definition domain_incl_prop { X : Type} (dom1: X -> Prop) (dom2: X -> Prop) := forall (x:X), (dom1 x -> dom2 x).
Infix "⊂" := domain_incl_prop (at level 99) : utils_scope.
#[global] Hint Unfold domain_incl_prop : rac_hint.

Definition eq_domain_prop { X : Type} (dom1: X -> Prop) (dom2: X -> Prop) := (dom1 ⊂ dom2) /\ (dom2 ⊂ dom1).
Infix "=" := eq_domain_prop : utils_scope.
#[global] Hint Unfold eq_domain_prop : rac_hint.


Definition sub_domain_prop { X : Type} (dom1: X -> Prop) (dom2: X -> Prop) (x:X) := dom1 x /\ ~ dom2 x.
Infix "-" := sub_domain_prop : utils_scope.
#[global] Hint Unfold sub_domain_prop : rac_hint.


Fact not_in_sub_domain_prop { X : Type} (x: X) (dom1: X -> Prop) (dom2: X -> Prop): 
    Decidable.decidable (dom1 x) -> 
    Decidable.decidable (dom2 x) -> 
    ~ ((dom1 - dom2) x) -> dom2 x \/ ~ dom1 x.
Proof.
    intros Hdec1 Hdec2 H. autounfold with rac_hint in H. apply Decidable.not_and in H;[|trivial]. destruct H.
    - now right.
    - apply Decidable.not_not in H;[|trivial]. now left.
Qed.

Definition add_domain { X : Type} (dom1: X -> Prop) (dom2: X -> Prop) (x:X) := dom1 x \/ dom2 x.
Infix "+" := add_domain : utils_scope.
#[global] Hint Unfold add_domain : rac_hint.

Fact not_in_diff {X Y : Type} : forall (x y:X) (f : (X ⇀ Y)), f y <> None -> x ∉ f -> y <> x.
Proof.
    intros x y f H H0 Hnot. subst. destruct (f x) eqn:F.
    * destruct H0. auto.
    * contradiction.
Qed.

Fact d_sub_d_empty {X Y : Type} : forall (f : (X ⇀ Y)),
    ~ exists n, (dom f - dom f) n.
Proof.
    intros f contra. inversion contra. inversion H. destruct H1. assumption.
Qed.


Module Type Bounds.
    Parameter m_int : Z.
    Parameter M_int : Z.
End Bounds.


(* simplified from compcert.lib.Integers *)
Module MachineInteger(B:Bounds).
    Open Scope bool_scope.
    Definition inRange n : Prop := (B.m_int <? n) && (n <? B.M_int) = true.

    Definition MI := sig inRange.

    Lemma mi_eq : forall (x y : MI), x = y <-> proj1_sig x = proj1_sig y.
    Proof.
        intros x y. split ; intros EQ.
        - destruct x,y. simpl. now inversion EQ.
        - destruct x,y. simpl in EQ. subst. f_equal. unfold inRange in *. now pose proof (Eqdep_dec.UIP_dec Bool.bool_dec).
    Qed.

    Definition to_mi x (H: inRange x) : MI := exist inRange x H.

    Definition of_mi (mi: MI) : Z := proj1_sig mi.


    Fact x_of_mi_to_mi_x : forall x irx, (to_mi (of_mi x) irx) = x.
    Proof.
        intros. unfold to_mi, of_mi. destruct x. simpl. f_equal. unfold inRange in *. 
        simpl in *.  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
    Qed.
End MachineInteger.





Close Scope Z_scope.

(* modified from http://poleiro.info/posts/2013-03-31-reading-and-writing-numbers-in-coq.html *)
Definition string_of_nat (n : nat) : string :=
    let fix aux (time n : nat) (acc : string) : string :=
    let acc' := String (Ascii.ascii_of_nat ((n mod 10) + 48)) acc in
    match time with
      | 0 => acc'
      | S time' =>
        match n / 10 with
          | 0 => acc'
          | n' => aux time' n' acc'
        end
    end in
    aux n n "".



    Module CounterMonad.

    Definition state {T : Type} : Type := nat -> T * nat.


    Definition ret {A : Type} (a : A) : state (T:=A) := fun c => (a, c).
    
    Definition bind {A B : Type} (m : state (T:=A)) (f : A -> state (T:=B)) : state (T:=B) :=
        let f' := fun c => 
            let (a, c') := m c in f a c' 
        in f'.
    
    Notation "x <- f ;; c" := (bind f (fun x => c)) (f at next level, at level 61, right associativity) .
    Notation "x <- f ;;; c" := (bind f (fun x => ret c)) (f at next level, at level 61, right associativity) .
    Notation "f ;; c" := (bind f (fun _ => c)) ( at level 61, right associativity).
    Notation "f ;;; c" := (bind f (fun _ => ret c)) ( at level 61, right associativity).
    
    Definition tick : state := fun c => (tt, S c).
    Definition getTick : state := fun c => (c, c).
    Definition fresh := n <- getTick ;; tick ;;; n.
    Definition exec {A:Type} (m: state (T:=A)) := fst (m 0).

  End CounterMonad.

Close Scope utils_scope.