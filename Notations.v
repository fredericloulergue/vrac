From Coq Require Import ZArith.ZArith.
From Coq Require Import ZArith.Znat.
From Coq Require Import Lists.List. 
From Coq Require Import Strings.String.
Open Scope Z_scope.


Declare Scope fsl_scope.
Delimit Scope fsl_scope with fsl.

Notation "X ⇀ Y" :=  (X -> option Y) (at level 100): type_scope.
Notation "A '^*'" := (list A) (at level 20) : type_scope.

Reserved Notation "⊥".
Reserved Notation "f { x \ y }" (at level 10).
Reserved Notation "'dom' f" (at level 10).

Notation id := string.


(* Declare Custom Entry exp.
Declare Custom Entry term.
Delimit Scope exp_scope with exp. *)

Reserved Notation "Ω ⊨ e => v" (at level 90). (* semantic of expressions, v ∈ Values *)
(* Reserved Notation "Ω ⊨ t => z" (at level 200).  semantic of terms z ∈ Z*)
(* Reserved Notation "Ω ⊨ p => b" (at level 200).  semantic of predicates b ∈ Bools *)

(* Reserved Notation "Ω , M ⊨ s => Ω' , M'" (at level 200).  (* semantic of statements *) *)


Reserved Notation "e ⊑ e'" (at level 99).