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

Require Import Arith ZArith List Bool.

Ltac destruct_and_hyp := 
  match goal with
  | [ H : (_ && _)%bool = true |- _ ] =>
      apply andb_prop in H;
      let H1 := fresh H in
      let H2 := fresh H in 
      destruct H as [H1 H2]
  | [ H : (_ && _)%bool = false |- _ ] =>
      apply Bool.andb_false_iff in H;
      let HH := fresh H in
      destruct H as [HH | HH]
  | [ H : _ /\ _ |- _ ] =>
      let H1 := fresh H in
      let H2 := fresh H in 
      destruct H as [H1 H2]
  end.

Ltac destruct_or_hyp := 
  match goal with
  | [ H : (_ || _)%bool = true |- _ ] =>
      apply orb_prop in H;
      destruct H as [H | H]
  | [ H : (_ || _)%bool = false |- _ ] =>
      apply Bool.orb_false_iff in H;
      let HH := fresh H in
      destruct H as [H1 H2]
  | [ H : _ \/ _ |- _ ] =>
      destruct H as [H|H]
  end.

Ltac destruct_and_goal :=
  match goal with 
  | [ |- (_ && _)%bool = true ] =>
        apply andb_true_intro; split
  | [ |- _ /\ _ ] => split 
  end.

Ltac Zleb :=
  match goal with
  | [ H: (_ <=? _) = true |- _ ] => apply Z.leb_le in H
  | [ H: (_ <=? _) = false |- _ ] => apply Z.leb_nle in H
  | [ |- (_ <=? _) = true ] => apply Z.leb_le 
  | [ |- (_ <=? _) = false ] => apply Z.leb_nle 
  end.
      
Ltac Zltb :=
  match goal with
  | [ H: (_ <? _) = true |- _ ] => apply Z.ltb_lt in H
  | [ H: (_ <? _) = false |- _ ] => apply Z.ltb_nlt in H
  | [ |- (_ <? _) = true ] => apply Z.ltb_lt
  | [ |- (_ <? _) = false ] => apply Z.ltb_nlt 
  end.

Ltac leb :=
  match goal with
  | [ H: (_ <=? _)%nat = true |- _ ] => apply Nat.leb_le in H
  | [ H: (_ <=? _)%nat = false |- _ ] => apply Nat.leb_nle in H
  | [ |- (_ <=? _)%nat = true ] => apply Nat.leb_le 
  | [ |- (_ <=? _)%nat = false ] => apply Nat.leb_nle 
  end.

Ltac ltb :=
  match goal with
  | [ H: (_ <? _)%nat = true |- _ ] => apply Nat.ltb_lt in H
  | [ H: (_ <? _)%nat = false |- _ ] => apply Nat.ltb_nlt in H
  | [ |- (_ <? _)%nat = true ] => apply Nat.ltb_lt
  | [ |- (_ <? _)%nat = false ] => apply Nat.ltb_nlt 
  end.

Ltac negb :=
  match goal with
  | [ H: negb _ = true |- _ ] => apply Bool.negb_true_iff in H
  | [ H: negb _ = false |- _ ] => apply Bool.negb_false_iff in H
  | [ |- negb _ = true ] => apply Bool.negb_true_iff
  | [ |- negb _ = false ] => apply Bool.negb_false_iff
  end.

Ltac imp :=
  match goal with
  | [ |- _ <-> _ ] => split; let H := fresh "H" in intro H
  end.

Ltac simpl_generic_eqb eqb eqb_refl eqb_sym eqb_eq eqb_neq :=
  match goal with
  | [ |- context [ eqb ?x ?x ] ] =>
      rewrite eqb_refl; simpl
  | [ H: context [ eqb ?x ?x ] |- _ ] =>
      rewrite eqb_refl in H; simpl in H
  | [ H: eqb ?x ?y = true |- _ ] =>
      rewrite eqb_eq in H; subst
  | [ H: eqb ?x ?y = false |- ?x <> ?y ] =>
      apply eqb_neq; auto
  | [ H: eqb ?y ?x = false |- ?x <> ?y ] =>
      apply eqb_neq; rewrite eqb_sym; auto
  | [ H: context [ eqb ?x ?x ] |- _ ] =>
      rewrite eqb_refl in H; simpl in H
  | [ H: eqb ?x ?y = true |- _ ] =>
      apply eqb_eq in H; try subst 
  | [ Hn: ?x = ?y, He: eqb ?x ?y = false |- _ ] => 
      apply eqb_neq in He; rewrite Hn in He; simpl
  | [ Hn: ?y = ?x, He: eqb ?x ?y = false |- _ ] =>
      apply eqb_neq in He; rewrite Hn in He; simpl
  | [ Hn: ?x <> ?y, H: context [ eqb ?x ?y ] |- _ ] =>
      apply eqb_neq in Hn; rewrite Hn in H; simpl in H
  | [ Hn: ?x <> ?y |- context [ eqb ?x ?y ] ] =>
      apply eqb_neq in Hn; rewrite Hn; simpl
  | [ Hn: ?x <> ?y, H: context [ eqb ?x ?y ] |- _ ] =>
      apply eqb_neq in Hn; rewrite Hn in H; simpl in H
  | [ Hn: ?y <> ?x |- context [ eqb ?x ?y ] ] =>
      apply eqb_neq in Hn; rewrite eqb_sym in Hn; rewrite Hn;
      apply eqb_neq in Hn; simpl
  | [ Hn: ?y <> ?x, H: context [ eqb ?x ?y ] |- _ ] =>
      apply eqb_neq in Hn; rewrite eqb_sym in Hn; rewrite Hn in H;
      apply eqb_neq in Hn; simpl in H
  end; simpl in *.

Ltac simpl_nat_eqb :=
  simpl_generic_eqb Nat.eqb Nat.eqb_refl Nat.eqb_sym Nat.eqb_eq Nat.eqb_neq.

Ltac simpl_Z_eqb :=
  simpl_generic_eqb Z.eqb Z.eqb_refl Z.eqb_sym Z.eqb_eq Z.eqb_neq.

Ltac simpl_if :=
  match goal with
  | [ Hcond: ?cond = true, 
        H: context [if ?cond then _ else _] |- _] =>
      rewrite Hcond in H; simpl in H
  | [ Hcond: ?cond = false, 
        H: context [if ?cond then _ else _] |- _] =>
      rewrite Hcond in H; simpl in H
  | [ Hcond: true = ?cond, 
        H: context [if ?cond then _ else _] |- _] =>
      rewrite Hcond in H; simpl in H
  | [ Hcond: false = ?cond, 
        H: context [if ?cond then _ else _] |- _] =>
      rewrite Hcond in H; simpl in H
  | [ Hcond: ?cond = true |-  
        context [if ?cond then _ else _] ] =>
      rewrite Hcond; simpl
  | [ Hcond: ?cond = false |-
        context [if ?cond then _ else _] ] =>
      rewrite Hcond; simpl
  | [ Hcond: true = ?cond |-
        context [if ?cond then _ else _] ] =>
      rewrite Hcond; simpl
  | [ Hcond: false = ?cond |- 
        context [if ?cond then _ else _] ] =>
      rewrite Hcond; simpl
  | [ H: context [if ?cond then _ else _] |- _] =>
      case_eq(cond);
      let HH := fresh "H" in intro HH; rewrite HH in H; simpl in *
  | [ |- context [if ?cond then _ else _] ] =>
      case_eq(cond);
      let HH := fresh "H" in intro HH; try rewrite HH; simpl in *
  end.

Ltac clean_inv H :=
  inversion H; subst; clear H; simpl in *.

Ltac existsb_true :=
  match goal with
  | [ H: existsb (Nat.eqb _) _ = true |- _ ] =>
      apply existsb_exists in H;
      let x := fresh "x" in
      let Hin := fresh "Hin" in
      let Heq := fresh "Heq" in 
      destruct H as [x [Hin Heq]]
  | [ H: In ?x ?l |- existsb (Nat.eqb _) ?l = true ] => 
      apply existsb_exists;
      exists x; split; auto; now simpl_nat_eqb
  end.

Ltac existsb_false :=
  match goal with
  | [ H : existsb (Nat.eqb ?x) ?l = false |- not(In ?x ?l) ] =>
      apply Bool.not_true_iff_false in H;
      contradict H;
      existsb_true
  | [ H : not(In ?x ?l) |- existsb (Nat.eqb ?x) ?l = false ] =>
      apply Bool.not_true_iff_false;
      contradict H;
      existsb_true; now simpl_nat_eqb
  end.

Ltac by_contradiction :=
  match goal with
  | [ H: ?hyp, H': ~?hyp |- _ ] => now contradict H
  | [ H: ~(?x = ?x)  |- _ ] => now contradict H
  | [ H: ?x = true, H': ?x = false  |- _ ] =>
      rewrite H in H'; discriminate
  | [ H: ?x = ?y, H': ?y <> ?x  |- _ ] =>
      rewrite H in H'; now contradict H'
  | [ H1: In ?x ?l, H2: existsb (Nat.eqb ?x) ?l = false |- _ ] =>
      apply Bool.not_true_iff_false in H2;
      contradict H2; existsb_true
  end.
