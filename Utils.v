From RAC Require Import Notations.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Setoids.Setoid.

Open Scope Z_scope.


Definition partial_function {X Y : Type} := X -> option Y.
Definition empty_p {X:Type} := (None: option X).

Notation "⊥" := empty_p : fsl_scope.

Class EqDec X :=
{
  eq_dec : forall (x y : X), {x = y} + {x <> y}
}.

#[global] Instance z_eq_dec : EqDec Z := {eq_dec := Z.eq_dec}.

Definition p_map {X Y : Type} `{EqDec X}  (f: X -> option Y) (x:X) (y:Y) : X -> option Y :=
    fun i => if eq_dec x i then Some y else f i.

Notation "f { x \ y }" := (p_map f x y): fsl_scope.


Inductive domain { X Y : Type} (f: X ⇀ Y) (y:Y) := 
    | exist : (exists x, (f x) = Some y) -> 
        domain f y
    .
Notation "'dom' f" := (domain f) : fsl_scope.


Module Type Bounds.
    Parameter m_int : Z.
    Parameter M_int : Z.
End Bounds.

(* simplified from compcert.lib.Integers *)
Module MachineInteger(B:Bounds).
    Definition inRange n :=B.m_int < n < B.M_int.

    Record MI := mkMI {val : Z; in_range : inRange val}.
    
    Definition to_z (i:MI) : Z := i.(val).
    Definition of_z (val:Z) H : MI := mkMI val H.
    Definition mi_eq m1 m2 := val m1 =? val m2.
    Axiom eq : forall m1 m2, val m1 = val m2 <-> m1 = m2.

    Lemma mi_eq_iff : forall m1 m2, mi_eq m1 m2 = true <-> m1 = m2.
    Proof.
      intros m1 m2. split.
      - intros H. unfold mi_eq in H. apply Z.eqb_eq in H. apply eq in H. apply H.
      - intro H. rewrite H. apply Z.eqb_refl.
    Qed.
   (* Definition eq m1 m2 := Z.eq_dec (val m1)  (val m2).


   Lemma mkint_eq:
   forall x y Px Py, x = y -> mkMI x Px = mkMI y Py.
 Proof.
   intros. subst y.
   assert (forall (n m: Z) (P1 P2: n < m), P1 = P2).
   {
     unfold Z.lt; intros.
     apply Eqdep_dec.eq_proofs_unicity.
     intros c1 c2. destruct c1; destruct c2; (left; reflexivity) || (right; congruence).
   }
   destruct Px as [Px1 Px2]. destruct Py as [Py1 Py2].
   rewrite (H _ _ Px1 Py1).
   rewrite (H _ _ Px2 Py2).
   reflexivity.
 Qed.

   Lemma eq_dec: forall (x y: MI), {x = y} + {x <> y}.
    Proof.
    intros. destruct x; destruct y. destruct (Z.eq_dec val0 val1).
    left. apply mkint_eq. auto.
    right. red; intro. injection H. exact n.
    Qed.

    Lemma zeq_true:
    forall (A: Type) (x: Z) (a b: A), (if Z.eq_dec x x then a else b) = a.
  Proof.
    intros. case (Z.eq_dec x x); intros.
    auto.
    elim n; auto.
  Qed.

  Lemma zeq_false:
  forall (A: Type) (x y: Z) (a b: A), x <> y -> (if Z.eq_dec x y then a else b) = b.
Proof.
  intros. case (Z.eq_dec x y); intros.
  auto.
  elim H; auto. auto.
Qed.


Theorem eq_spec: forall (m1 m2: MI), if eq m1 m2 then m1 = m2 else m1 <> m2.
Proof.
    intros; unfold eq. case (eq_dec m1 m2); intro.
    subst m2. rewrite zeq_true. auto.
    rewrite zeq_false. auto.
    destruct m1; destruct m2.
    simpl. red; intro. elim n. apply mkint_eq. auto.
Qed. *)

End MachineInteger.


