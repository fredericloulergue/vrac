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

Require Import List Arith Lia. Import ListNotations.

Fixpoint maximum support :=
  match support with
  | [] => 0%nat
  | h::t => Nat.max h (maximum t)
  end.
  
Lemma maximum_lt :
  forall l x, In x l -> (x <= maximum l)%nat.
Proof.
  induction l as [ | h t IH ].
  - intros x H. firstorder.
  - intros x H. simpl in *.
    destruct H as [H | H].
    + subst. lia.
    + specialize (IH _ H). lia.
Qed.

Lemma S_maximum_not_in:
  forall l, not(In (S(maximum l)) l).
Proof.
  induction l as [ | h t IH ].
  - auto.
  - contradict IH.
    simpl in IH.
    destruct IH as [ Heq | Hin ].
    + rewrite Nat.succ_max_distr in Heq; lia.
    + apply maximum_lt in Hin; lia.
Qed.
