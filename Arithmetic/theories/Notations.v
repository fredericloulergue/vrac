From Coq Require Import Strings.String ZArith.

Declare Custom Entry pmap.

Notation id := Strings.String.string.
Notation ℤ := Z.
Notation "A *" := (list A) (at level 20) : type_scope.
Infix "⨉" := prod (at level 99) : type_scope. 

Definition 𝓥 : Type := id. (* program variables and routines *)
Definition 𝔏 : Type := id. (* logic variables *)

Reserved Notation "X ⇀ Y"  (at level 100).
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
