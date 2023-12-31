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

Require Import ZArith Arith Lia.
Require Import List. Import ListNotations.

From Vrac.Lib Require Import Option Tactics.
From Vrac.Memory Require Import MemoryType ObservationMemoryModel.

Open Scope Z_scope.

Module Implementation : ObservationMemoryModel Nat.

  Definition block := nat.
  
  Record Memory :=
    {
      allocated: block -> bool;
      size: block -> Z;
      initialized : block -> Z -> mtyp -> bool;
    }.
  
  Definition obs := Memory.

  Definition empty :=
    {|
      allocated := fun b => false;
      size := fun b => 0;
      initialized := fun b δ κ => false;
    |}.


  Definition store_block: obs * block * nat -> obs :=    
    fun argument =>
      match argument with 
      | (M, b, n) => 
          {|
            allocated := fun b' => if (Nat.eqb b b')
                                then true
                                else M.(allocated) b';
            size := fun b' => if (Nat.eqb b b')
                           then Z.of_nat n
                           else M.(size) b';
            initialized := fun b' => if (Nat.eqb b b')
                                  then fun δ κ => false
                                  else M.(initialized) b';
          |}
      end.

  Definition delete_block: obs * block -> obs :=
    fun argument =>
      let (M, b) := argument in
      {|
        allocated := fun b' => if (Nat.eqb b b')
                            then false
                            else M.(allocated) b';
            size := fun b' => if (Nat.eqb b b')
                           then 0
                           else M.(size) b';
            initialized := fun b' => if (Nat.eqb b b')
                                  then fun δ κ => false
                                  else M.(initialized) b' ;
      |}.

  Definition is_valid : obs * block -> bool :=
    fun argument => allocated (fst argument) (snd argument).

  Definition length: obs * block -> Z :=
    fun argument =>
      let (M, b) := argument in
      M.(size) b.

  Definition is_valid_access (arg: mtyp * obs * block * Z) : bool := 
    match arg with
      | (κ, M, b, δ) =>
          (is_valid(M, b) && (0 <=? δ) && (δ + sizeof κ <=? length(M,b)))%bool
    end.

  Definition initialize: mtyp * obs * block * Z -> obs :=
    fun argument =>
      match argument with
      | (κ, M, b, δ) =>
          {|
            allocated := M.(allocated);
            size := M.(size);
            initialized :=
              fun b' δ' κ' => if ((Nat.eqb b b') && (δ =? δ')&& (Mtyp.eqb κ κ'))%bool    
                           then true
                           else
                             if ((Nat.eqb b b') &&
                                   ((δ =? δ')&&(negb(Mtyp.eqb κ κ'))||(negb(δ=? δ')))
                                 && (0 <=? δ')
                                 && (δ'<? δ+sizeof κ)
                                 && (δ<? δ'+sizeof κ') && (0 <=? δ')
                                 && (δ' + sizeof κ' <=? length(M, b)))%bool
                             then false
                             else M.(initialized) b' δ' κ'
          |}
      end.

  Definition is_initialized : mtyp * obs * block * Z -> bool :=
    fun argument =>
      match argument with
      | (κ, M, b, δ) => M.(initialized) b δ κ
      end.
  
  #[local] Hint Unfold is_valid is_valid_access store_block empty delete_block initialize is_initialized length : local.

  Ltac simpl_eqb :=
    repeat(simpl_nat_eqb||simpl_Z_eqb||simpl_mtyp_eqb).
  
  Ltac mauto :=
    intros; autounfold with local in *;
    try destruct_and_hyp;
    match goal with
    | [ H : _ = _  |- _ ] =>
        clean_inv H;
        try now simpl_eqb
    end;
    auto.
  
  Lemma storeblock_validblock_same: forall M1 M2 n b,
      store_block(M1, b, n) = M2 ->
      is_valid(M2, b) = true.
  Proof. mauto. Qed.
  
  Lemma storeblock_validblock_other: forall M1 M2 b b' n,
      (b <> b' /\ store_block(M1, b, n) = M2) ->
      is_valid(M2, b') = is_valid(M1, b').
  Proof. mauto. Qed.

  Lemma deleteblock_validblock_same: forall M1 M2 b,
      delete_block(M1, b) = M2 -> is_valid(M2, b) = false.
  Proof. mauto. Qed.
    
  Lemma deleteblock_validblock_other: forall M1 M2 b b',
      b <> b' /\ delete_block(M1, b) = M2 ->
      is_valid(M2, b') = is_valid(M1, b').
  Proof. mauto. Qed.

  Lemma initialize_validblock: forall M1 M2 b b' κ δ,
      initialize(κ, M1, b, δ) = M2 ->
      is_valid(M2, b') = is_valid(M1, b').
  Proof. mauto. Qed.
  
  Lemma storeblock_isinit_same: forall M1 M2 b δ κ n,
      store_block(M1, b, n) = M2 ->
      is_initialized(κ, M2, b, δ) = false.
  Proof. mauto. Qed.
    
  Lemma storeblock_isinit_other: forall M1 M2 b b' n δ κ,
      b <> b' /\ store_block(M1, b, n) = M2 ->
      is_initialized(κ, M2, b', δ) = is_initialized(κ, M1, b', δ).
  Proof. mauto. Qed.

  Lemma deleteblock_isinit_other: forall M1 M2 b b' δ κ,
      b <> b' /\ delete_block(M1, b) = M2 ->
      is_initialized(κ, M2, b', δ) = is_initialized(κ, M1, b', δ).
  Proof. mauto. Qed.

  Lemma initialize_isinit_same: forall M1 M2 b δ κ,
      initialize(κ, M1, b, δ) = M2 ->
      is_initialized(κ, M2, b, δ) = true.
  Proof.
    intros M1 M2 b δ κ H.
    autounfold with local in *. simpl in *.
    clean_inv H. clear  H0.
    simpl_if.
    - trivial.
    - assert(0 < sizeof κ) by now destruct κ.
      match goal with
      | [ H : ?condition = false |- _ ] =>
          assert(Ht: condition = true) by
          (now repeat (simpl_mtyp_eqb; simpl_eqb))
      end.
      now rewrite Ht in H.
  Qed.

  Lemma initialize_isinit_other: forall M1 M2 b b' δ δ' κ κ',
      initialize(κ, M1, b, δ) = M2 /\
      (b <> b' \/ δ + sizeof(κ) <= δ' \/ δ' + sizeof(κ') <= δ) ->
      is_initialized(κ', M2, b', δ') = is_initialized(κ', M1, b', δ').
  Proof.
    intros M1 M2 b b' δ δ' κ κ' H.
    autounfold with local in *.
    repeat destruct_and_hyp.
    clean_inv H0.  clear H.
    assert(0 < sizeof κ) by now destruct κ.
    assert(0 < sizeof κ') by now destruct κ'.
    simpl_if; repeat destruct_or_hyp.
    - repeat destruct_and_hyp. simpl_eqb. by_contradiction.
    - repeat destruct_and_hyp. assert(δ<>δ') by lia. simpl_eqb. by_contradiction.
    - repeat destruct_and_hyp. assert(δ<>δ') by lia. simpl_eqb. by_contradiction.
    - simpl_eqb. now rewrite H1.
    - assert(HH:(δ' <? δ + sizeof κ)=false) by lia. rewrite HH. 
      now rewrite Bool.andb_false_r.
    - assert(HH:(δ <? δ' + sizeof κ')=false) by lia. rewrite HH. 
      now rewrite Bool.andb_false_r.
  Qed.

  Lemma initialize_isinit_overlap: forall M1 M2 b δ δ' κ κ',
      initialize(κ, M1, b, δ) = M2 /\ ((δ=δ'/\ κ<>κ') \/ δ <> δ') /\
      δ' < δ + sizeof(κ) /\ δ < δ' + sizeof(κ') /\
      0 <= δ' /\ δ' + sizeof(κ') <= length(M2, b) ->
      is_initialized(κ', M2, b, δ') = false.
  Proof.
    unfold initialize.
    intros M1 [alloc sz init] b δ δ' κ κ' H.
    simpl in *.
    destruct H as [Hinit [H1 [H2 [H3 [H4 H5]]]]].
    inversion Hinit; clear Hinit.
    destruct H1 as [ [Hsameδ Hdiffκ] | Hdiffδ ];
      try subst; repeat simpl_eqb;
      match goal with
      | [ |- context [ if ?cond then _ else _ ] ] =>
          assert(HH: cond = true) by
          (repeat destruct_and_goal; lia)
      end;
      now rewrite HH.
  Qed.

  Lemma storeblock_length_same: forall M1 M2 b n,
      store_block(M1, b, n) = M2 ->
      length(M2, b) = Z.of_nat n.
  Proof. mauto. Qed.
    
  Lemma storeblock_length_other: forall M1 M2 b b' n,
      b <> b' /\ store_block(M1, b, n) = M2 ->
      length(M2, b') = length(M1, b').
  Proof. mauto. Qed.
    
  Lemma initialize_length: forall M1 M2 b b' δ κ,
      initialize(κ, M1, b, δ) = M2 ->
      length(M2, b') = length(M1, b').
  Proof. mauto. Qed.

  Lemma deleteblock_length_other_: forall M1 M2 b b',
      b <> b' /\ delete_block(M1, b) = M2 ->
      length(M2, b') = length(M1, b').
  Proof. mauto. Qed.

  Lemma empty_isvalid: forall b,
      is_valid(empty, b) = false.
  Proof. 
    intros; now autounfold with local in *.
  Qed.

  Lemma empty_isinit: forall κ b δ,
      is_initialized(κ, empty, b, δ) = false.
  Proof.
    intros; now autounfold with local in *.
  Qed.
      
End Implementation.

Close Scope Z_scope.
