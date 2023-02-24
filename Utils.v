From RAC Require Import Notations.
From Coq Require Import ZArith.ZArith.
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

Notation "f { x \ y }" := (p_map f x y) : fsl_scope.


Inductive domain { X Y : Type} (f: X ⇀ Y) (y:Y) := 
    | exist : (exists x, (f x) = Some y) -> 
        domain f y
    .
Notation "'dom' f" := (domain f) : fsl_scope.



(*

 Inductive p_map {X Y : Type} (f: X ⇀ Y) (x:X) (y:Y) : X -> option Y -> Prop := 
    | is_x : f { x \ y } x (Some y)
    | is_not_x : 
        forall (i:X), i <> x -> 
        forall (o: option Y), (f i) = o -> 
        f { x \ y } i o

 where "f { x \ y }" := (p_map f x y). 
 *)

