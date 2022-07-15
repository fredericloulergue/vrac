Notation "'⎣' v '⎦'" := (Some v).
Notation "'ϵ'" := (None).

Definition is_ϵ {A} (v: option A) :=
  match v with
  | ϵ => true
  | _ => false
  end.
