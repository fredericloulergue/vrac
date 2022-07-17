Require Import ZArith Arith Lia.
Require Import List. Import ListNotations.

Require Import Vrac.Option Vrac.Tactics Vrac.MemoryType.

Open Scope Z_scope.

Module Type ObservationMemoryModel.
   
  Parameter obs : Type.

  Parameter block : Type.
  Parameters eqb : block -> block -> bool.
  Axiom eqb_eq: forall b b', eqb b b' = true <-> b = b'.

  Parameter empty: obs.
  Parameter store_block: obs * block * nat -> obs.
  Parameter delete_block: obs * block -> obs. 
  Parameter initialize: mtyp * obs * block * Z -> obs.
  Parameter is_valid: obs * block ->bool.
  Parameter is_initialized: mtyp * obs * block * Z -> bool.
  Parameter length: obs * block -> Z.
  
  Definition is_valid_access (M: obs) (κ: mtyp) (b:block) (δ: Z) : bool :=
    (is_valid(M, b) && (0 <=? δ) && (δ + sizeof κ <=? length(M,b)))%bool.

  Axiom storeblock_validblock_same: forall M1 M2 n b,
      store_block(M1, b, n) = M2 ->
      is_valid(M2, b) = true.

  Axiom storeblock_validblock_other: forall M1 M2 b b' n,
      (b <> b' /\ store_block(M1, b, n) = M2) ->
      is_valid(M2, b') = is_valid(M1, b').

  Axiom deleteblock_validblock_same: forall M1 M2 b,
      delete_block(M1, b) = M2 -> is_valid(M2, b) = false.
    
  Axiom deleteblock_validblock_other: forall M1 M2 b b',
      b <> b' /\ delete_block(M1, b) = M2 ->
      is_valid(M2, b') = is_valid(M1, b').

  Axiom initialize_validblock: forall M1 M2 b b' κ δ,
      initialize(κ, M1, b, δ) = M2 ->
      is_valid(M2, b') = is_valid(M1, b').
  
  Axiom storeblock_isinit_same: forall M1 M2 b δ κ n,
      store_block(M1, b, n) = M2 ->
      is_initialized(κ, M2, b, δ) = false.

  Axiom storeblock_isinit_other: forall M1 M2 b b' n δ κ,
      b <> b' /\ store_block(M1, b, n) = M2 ->
      is_initialized(κ, M2, b', δ) = is_initialized(κ, M1, b', δ).

  Axiom deleteblock_isinit_other: forall M1 M2 b b' δ κ,
      b <> b' /\ delete_block(M1, b) = M2 ->
      is_initialized(κ, M2, b', δ) = is_initialized(κ, M1, b', δ).
  
  Axiom initialize_isinit_same: forall M1 M2 b δ κ,
      initialize(κ, M1, b, δ) = M2 ->
      is_initialized(κ, M2, b, δ) = true.

  Axiom initialize_isinit_other: forall M1 M2 b b' δ δ' κ κ',
      initialize(κ, M1, b, δ) = M2 /\
      (b <> b' \/ δ + sizeof(κ) <= δ' \/ δ' + sizeof(κ') <= δ) ->
      is_initialized(κ', M2, b', δ') = is_initialized(κ', M1, b', δ').

  Axiom storeblock_length_same: forall M1 M2 b n,
      store_block(M1, b, n) = M2 ->
      length(M2, b) = Z.of_nat n.

  Axiom storeblock_length_other: forall M1 M2 b b' n,
      b <> b' /\ store_block(M1, b, n) = M2 ->
      length(M2, b') = length(M1, b').

  Axiom initialize_length: forall M1 M2 b b' δ κ,
      initialize(κ, M1, b, δ) = M2 ->
      length(M2, b') = length(M1, b').

  Axiom deleteblock_length_other_: forall M1 M2 b b',
      b <> b' /\ delete_block(M1, b) = M2 ->
      length(M2, b') = length(M1, b').

  Axiom empty_isvalid: forall b,
    is_valid(empty, b) = false.

  Axiom empty_isinit: forall κ b δ,
    is_initialized(κ, empty, b, δ) = false.
      
End ObservationMemoryModel.

Close Scope Z_scope.
