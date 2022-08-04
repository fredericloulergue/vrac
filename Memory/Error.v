Require Import String.

Close Scope string_scope.

Declare Scope error_monad_scope.

Set Implicit Arguments.

(** Error Monad *)

Inductive result (A: Type) : Type :=
| Ok: A -> result A
| Error: string -> result A.

Arguments Error [A].

Definition bind (A B: Type) (f: result A) (g: A -> result B) : result B :=
  match f with
  | Ok x => g x
  | Error msg => Error msg
  end.

Definition bind2 (A B C: Type) (f: result (A*B)) (g: A->B->result C) : result C :=
  match f with
  | Ok (x, y) => g x y
  | Error msg => Error msg
  end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
 (at level 200, X name, A at level 100, B at level 200)
 : error_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
 (at level 200, X name, Y name, A at level 100, B at level 200)
 : error_monad_scope.

Definition lift (A B: Type)(f:A->B): result A -> result B :=
  fun x => bind x (fun v => Ok (f v)).
