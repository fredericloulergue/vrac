Require Import Arith ZArith.
From Vrac.Lib Require Import Tactics Eqb.

Inductive mtyp := i8 | i16 | i32 | i64.

Module BaseMtyp.

  Definition t := mtyp.

  Definition eqb κ κ' :=
    match (κ, κ') with
    | (i8, i8) => true
    | (i16, i16) => true
    | (i32, i32) => true
    | (i64, i64) => true
    | _ => false
    end.

  Lemma eqb_eq:
    forall κ κ', eqb κ κ' = true <-> κ = κ'.
  Proof.
    intros κ κ'.
    now destruct κ, κ'.
  Qed.
    
End BaseMtyp.

Module Mtyp := (Full BaseMtyp).
 
Definition sizeof: mtyp -> Z :=
  fun type => match type with
           | i8 => 1%Z
           | i16 => 2%Z
           | i32 => 4%Z
           | i64 => 8%Z
           end.

Lemma sizeof_pos:
  forall κ, (0 <= sizeof κ)%Z.
Proof.
  now destruct κ.
Qed.

Definition max: mtyp -> mtyp -> mtyp :=
  fun κ1 κ2 => if (sizeof κ1 <=? sizeof κ2)%Z
            then κ2
            else κ1.

Definition min_int (sz:Z) : Z := ( - 2 ^ (8*sz-1) )%Z.

Definition max_int (sz:Z) : Z := ( 2 ^ (8*sz-1) - 1 )%Z.

Ltac simpl_mtyp_eqb :=
  simpl_generic_eqb Mtyp.eqb Mtyp.eqb_refl Mtyp.eqb_sym Mtyp.eqb_eq Mtyp.eqb_neq.
