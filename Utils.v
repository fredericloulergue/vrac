From RAC Require Import Notations.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Eqdep_dec. 

Open Scope Z_scope.


Definition partial_function {X Y : Type} := X -> option Y.
Definition empty_p {X:Type} := (None: option X).

Notation "⊥" := empty_p : fsl_scope.

Class EqDec X :=
{
  eq_dec : forall (x y : X), {x = y} + {x <> y}
}.

#[global] Instance z_eq_dec : EqDec Z := {eq_dec := Z.eq_dec}.

Definition p_map {X Y : Type} `{EqDec X}  (f: X -> option Y) (x:X) (y:Y) : X -> option Y :=
    fun i => if eq_dec x i then Some y else f i.

Notation "f { x \ y }" := (p_map f x y): fsl_scope.


Inductive domain { X Y : Type} (f: X ⇀ Y) (y:Y) := 
    | exist : (exists x, (f x) = Some y) -> 
        domain f y
    .
Notation "'dom' f" := (domain f) : fsl_scope.


Module Type Bounds.
    Parameter m_int : Z.
    Parameter M_int : Z.
End Bounds.

(* simplified from compcert.lib.Integers *)
Module MachineInteger(B:Bounds).
    Definition inRange n :=B.m_int < n < B.M_int.

    Record MI := mkMI {val : Z; in_range : inRange val}.
    
    Definition to_z (i:MI) : Z := i.(val).
    Definition of_z (val:Z) H : MI := mkMI val H.
    Definition mi_eqb m1 m2 := val m1 =? val m2.
End MachineInteger.


