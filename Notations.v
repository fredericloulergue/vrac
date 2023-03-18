From Coq Require Import ZArith.ZArith.
From Coq Require Import ZArith.Znat.
From Coq Require Import Lists.List. 
From Coq Require Import Strings.String.


Declare Scope utils_scope.
Delimit Scope utils_scope with utils.

Notation "X ⇀ Y" :=  (X -> option Y) (at level 100): type_scope.
Notation "A ⃰" := (list A) (at level 20) : type_scope.

Declare Custom Entry pmap.
Reserved Notation "⊥".
Reserved Notation "'dom' f" (at level 10).
Notation "x '\' y" := (x,y) (in custom pmap at level 0, x constr, y constr) : utils_scope.
Reserved Notation "f { xy , .. , xy' }" (xy custom pmap, xy' custom pmap, at level 0).


Notation id := string.


(* Declare Custom Entry exp.
Declare Custom Entry term.
Delimit Scope exp_scope with exp. *)


Reserved Notation "Ω |= e => v" (at level 90). (* semantic of expressions, v ∈ Value *)
Reserved Notation " [ Ω ~ M ]  |= s => [ Ω' ~ M' ]" (at level 200).  (* semantic of statements *) 


Reserved Notation "e ⊑ e'" ( e  constr, e'  constr, at level 99).

Reserved Notation "( e , m ) ⊑ ( e' , m' )".

