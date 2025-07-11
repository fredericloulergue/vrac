From Ltac2 Require Import Ltac2.
From Coq Require Import Strings.String ZArith.ZArith.
From Coq Require Export Program.Basics.
From Equations Require Export Equations.


From RecordUpdate Require Export RecordUpdate.

#[export] Set Printing Projections. (* use r.(Field) notation for record projection *)
(* #[export] Set Loose Hint Behavior "Strict". don't allow not imported hint to be used *)
#[export] Set Default Proof Using "Type". (* Enable async proof-checking of sections. *)
(* #[export] Set Suggest Proof Using. *) (* suggest using annotation if none provided *)
#[export] Set Default Goal Selector "!". (* enforce proof structure *)

Open Scope program_scope.


(* some notations *)
Declare Custom Entry pmap.

Notation id := Strings.String.string.

Implicit Type v : id.

Notation ℤ := Z.
Notation "A ★" := (list A) (at level 20) : type_scope.
Infix "⨉" := prod (at level 99) : type_scope. 

Notation 𝓥 := id. (* program variables and routines *)
Notation 𝔏 := id. (* logic variables *)

Reserved Notation "X ⇀ Y"  (at level 100).
Reserved Notation "⊥".
Reserved Notation "'dom' f" (at level 10).
Reserved Notation "f { xy , .. , xy' }" (xy custom pmap, xy' custom pmap, at level 1).
Reserved Notation "{{ xy , .. , xy' }}" (xy custom pmap, xy' custom pmap, at level 0).
Reserved Notation "env |= e => v" (at level 70). (* semantic of expressions, v ∈ Value *)
Reserved Notation "env |= s => env'" (at level 70,  env' at next level).  (* semantic of statements *) 
Reserved Notation "env '|=' e ⇝ z" (at level 70).
Reserved Notation "e ⊑ e'" ( e  constr, e'  constr, at level 99).
Reserved Notation "( e , m ) ⊑ ( e' , m' )".
Reserved Notation "e ⊑ e'" (at level 99).
