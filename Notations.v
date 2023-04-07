From Coq Require Import ZArith.ZArith.
From Coq Require Import ZArith.Znat.
From Coq Require Import Lists.List. 
From Coq Require Import Strings.String.


Declare Scope utils_scope.
Delimit Scope utils_scope with utils.

Declare Custom Entry pmap.

Notation "X ⇀ Y" :=  (X -> option Y) (at level 100): type_scope.
Notation "A ⃰" := (list A) (at level 20) : type_scope.
Notation "x '\' y" := (x,y) (in custom pmap at level 0, x constr, y constr) : utils_scope.
Notation id := string.

Reserved Notation "⊥".
Reserved Notation "'dom' f" (at level 10).
Reserved Notation "f { xy , .. , xy' }" (xy custom pmap, xy' custom pmap, at level 0).
Reserved Notation "Ω |= e => v" (at level 70). (* semantic of expressions, v ∈ Value *)
Reserved Notation "Ω ⋅ M |= e => v" (at level 70,  M at next level).  (* semantic of gmp expressions *) 
Reserved Notation "Ω ⋅ M |= s => Ω' ⋅  M'" (at level 70,  M at next level, Ω' at next level).  (* semantic of statements *) 
Reserved Notation "e ⊑ e'" ( e  constr, e'  constr, at level 99).
Reserved Notation "( e , m ) ⊑ ( e' , m' )".

