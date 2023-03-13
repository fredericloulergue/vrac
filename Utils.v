From RAC Require Import Notations.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Eqdep_dec. 
Open Scope Z_scope.
Open Scope utils_scope.

Definition partial_function {X Y : Type} := X -> option Y.
Definition empty_p {X Y:Type} := fun (_:X) => (None: option Y).

Notation "⊥" := empty_p : utils_scope.

Class EqDec X :=
{
  eq_dec : forall (x y : X), {x = y} + {x <> y}
}.

#[global] Instance z_eq_dec : EqDec Z := {eq_dec := Z.eq_dec}.

Definition p_map {X Y : Type} `{EqDec X}  (f: X -> option Y) (xy:X * Y) : X -> option Y :=
    fun i => if eq_dec (fst xy) i then Some (snd xy) else f i.

Notation "f { xy , .. , xy' }" :=  (p_map .. (p_map f xy') .. xy ) : utils_scope.


Definition p_map_addall {X Y: Type} `{EqDec X} env (l:list (X*Y)) :=
    List.fold_left (fun f (xy:X*Y) => let (x,y) := xy in f {x \ y}) l env
.


Definition domain { X Y : Type} (f: X ⇀ Y) (x:X) := (exists y, (f x) = Some y) 
.
Notation "'dom' f" := (domain f) : utils_scope.


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


