Notation "'⎣' v '⎦'" := (Some v).
Notation "'ϵ'" := (None).

Declare Scope option_monad_scope.

Definition is_ϵ {A} (v: option A) :=
  match v with
  | ϵ => true
  | _ => false
  end.

Set Implicit Arguments.

Definition bind (A B: Type) (f: option A) (g: A -> option B) : option B :=
  match f with
  | Some x => g x
  | None => None
  end.

Definition bind2 (A B C: Type) (f: option (A*B)) (g: A->B->option C) : option C :=
  match f with
  | Some (x, y) => g x y
  | None => None
  end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
 (at level 200, X name, A at level 100, B at level 200)
 : option_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
 (at level 200, X name, Y name, A at level 100, B at level 200)
 : option_monad_scope.

Definition lift (A B: Type)(f:A->B): option A -> option B :=
  fun x => bind x (fun v => Some (f v)).
