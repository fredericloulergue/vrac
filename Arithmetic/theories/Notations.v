From Coq.ZArith Require Import ZArith Znat.
From Coq Require Import Lists.List  Strings.String.


Declare Scope utils_scope.
Delimit Scope utils_scope with utils.

Declare Custom Entry pmap.

Reserved Notation "X ⇀ Y"  (at level 100).
Notation "A ⃰" := (list A) (at level 20) : type_scope.
Notation "x '\' y" := (x,y) (in custom pmap at level 0, x constr, y constr) : utils_scope.

Notation id := string.

Definition 𝓥 : Type := id. (* program variables and routines *)
Definition 𝔏 : Type := id. (* logic variables *)
Reserved Notation "⊥".
Reserved Notation "'dom' f" (at level 10).
Reserved Notation "f { xy , .. , xy' }" (xy custom pmap, xy' custom pmap, at level 0).
Reserved Notation "{{ xy , .. , xy' }}" (xy custom pmap, xy' custom pmap, at level 0).
Reserved Notation "env |= e => v" (at level 70). (* semantic of expressions, v ∈ Value *)
Reserved Notation "env |= s => env'" (at level 70,  env' at next level).  (* semantic of statements *) 
Reserved Notation "env '|=' e ⇝ z" (at level 70).
Reserved Notation "e ⊑ e'" ( e  constr, e'  constr, at level 99).
Reserved Notation "( e , m ) ⊑ ( e' , m' )".
Reserved Notation "e ⊑ e'" (at level 99).
