From RAC Require Import Notations.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Eqdep_dec. 
From Coq Require Import Strings.String.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope utils_scope.

Definition partial_function {X Y : Type} := X -> option Y.
Definition empty_p {X Y:Type} := fun (_:X) => (None: option Y).

Infix "⨉" := prod (at level 99).
Notation "⊥" := empty_p : utils_scope.
Notation "'ℤ'" := Z (at level 99).

Class EqDec X :=
{
  eq_dec : forall (x y : X), {x = y} + {x <> y}
}.

#[global] Instance z_eq_dec : EqDec Z := {eq_dec := Z.eq_dec}.

Definition p_map {X Y : Type} `{EqDec X}  (f: X -> option Y) (xy:X * Y) : X -> option Y :=
    fun i => if eq_dec (fst xy) i then Some (snd xy) else f i.

Notation "f { xy , .. , xy' }" :=  (p_map .. (p_map f xy') .. xy ) : utils_scope.


Definition p_map_addall {X Y: Type} `{EqDec X} env (lx:list X) (ly : list Y) :=
    List.fold_left (fun f xy => f {(fst xy) \ (snd xy)}) (List.combine lx ly) env
.

Definition in_domain { X Y : Type} (f: X ⇀ Y) (x:X) := (exists y, (f x) = Some y).

(* fixme domain def here *)

Notation "'dom' f" := (in_domain f) : utils_scope.
Notation "x ∈ E" := (in_domain E x) (at level 99) : utils_scope.
Notation "x ∉ E" := (~ in_domain E x) (at level 99) : utils_scope.

Definition min_domain { X : Type} (dom1: X -> Prop) (dom2: X -> Prop) (x:X) := dom1 x /\ ~ dom2 x.
Infix "-" := min_domain : utils_scope.


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
    Definition inRange n :=B.m_int < n < B.M_int.

    Record MI := mkMI {val : Z; in_range : inRange val}.
    
    Definition to_z (i:MI) : Z := i.(val).
    Definition mi_eqb m1 m2 := val m1 =? val m2.
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