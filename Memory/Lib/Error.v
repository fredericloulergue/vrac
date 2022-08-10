(************************************************************************)
(* VRAC: Verified Runtime Assertion Checker                             *)
(* Copyright Université d'Orléans                                       *)
(* Coq code by Frédéric Loulergue                                       *)
(*   based on the VRAC project by                                       *)
(*   Dara Ly, Nikolai Kosmatov, Frédéric Loulergue, Julien Signoles     *)
(* This file is distributed under the terms of the                      *)
(*   Université d'Orléans Non-Commercial License Agreement              *)
(* (see LICENSE file for the text of the license)                       *) 
(************************************************************************)

Require Import String.

Declare Scope error_monad_scope.

Set Implicit Arguments.

Generalizable All Variables.

(** Error Monad *)

Inductive result (A: Type) : Type :=
| Ok: A -> result A
| Error: string -> result A.

Arguments Error [A].

Definition bind `(f: result A) `(g: A -> result B) : result B :=
  match f with
  | Ok x => g x
  | Error msg => Error msg
  end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
 (at level 200, X name, A at level 100, B at level 200)
 : error_monad_scope.

Close Scope string_scope.
