Require Import ZArith Arith Lia.
Require Import List. Import ListNotations.

Require Import Vrac.Option Vrac.Tactics Vrac.MemoryType.

Open Scope Z_scope.

Module Type ExecutionMemoryModel.
   
  Parameter mem : Type.
  Parameter block : Type.
  
  Inductive value :=
  | Int : Z -> value
  | Ptr : block * Z -> value
  | Undef.
  
  Parameter machine_word_size : Z.
  Parameter alloc: mem * nat -> block * mem.
  Parameter free: mem * block -> option mem. 
  Parameter store: mtyp * mem * block * Z * value -> option mem.
  Parameter load: mtyp * mem * block * Z -> option value.
  Parameter valid_block: mem -> block -> Prop.
  Parameter length: mem * block -> Z.
  Parameter convert: value * mtyp * mtyp -> value. 
  
  Infix "⊨" := valid_block (at level 70).
  
  Definition storable : value -> mtyp -> bool :=
    fun v κ =>
      match (v, κ) with
      | (Int n, i8) => (-128 <=? n) && (n <=? 127)
      | (Int n, i16) => (-32768 <=? n) && (n <=? 32767)
      | (Int n, i32) => (-2147483648 <=? n) && (n <=? 2147483647)
      | (Int n, i64) => (-9223372036854775808 <=? n)
                       && (n <=? 9223372036854775807)
      | (Ptr _, κ) => sizeof κ =? machine_word_size
      | _ => false
      end%bool.
  
  Definition valid_access (M: mem) (κ: mtyp) (b:block) (δ: Z) :=
    M ⊨ b /\ 0 <= δ /\ δ + sizeof κ <= length(M,b).

  Notation "M '⫢' κ '@' b ',' δ" := (valid_access M κ b δ) (at level 70).
  
  Axiom convert_storable :
    forall v κ, storable v κ = true -> convert(v, κ, κ) = v.

  Axiom convert_different_mtyp_undef :
    forall v κ κ', κ <> κ' -> convert(v, κ, κ') = Undef.

  Axiom convert_not_storable_undef :
    forall v κ κ', storable v κ = false -> convert(v, κ, κ') = Undef.
  
  Inductive in_supp (b: block) (M: mem) : Prop :=
  | in_supp_valid : M ⊨ b -> in_supp b M
  | in_supp_loadable : forall b' δ δ' κ,
      load(κ, M, b', δ') = Some(Ptr(b, δ)) ->
      in_supp b M.

  Notation "b '∈' 'supp' '(' M ')'" := (in_supp b M) (at level 70).

  Axiom valid_after_alloc_same: forall M1 M2 n b,
      alloc(M1, n) = (b, M2) ->
      M2 ⊨ b.

  Axiom valid_after_alloc_other: forall M1 M2 b b' n,
      (b <> b' /\ alloc(M1, n) = (b, M2)) ->
      (M2 ⊨ b' <-> M1 ⊨ b').

  Axiom invalid_after_free: forall M1 M2 b,
      free(M1, b) = ⎣M2⎦ -> not(M2 ⊨ b).   
    
  Axiom valid_after_free: forall M1 M2 b b',
      b <> b' /\ free(M1, b) = ⎣M2⎦ ->
      (M2 ⊨ b' <-> M1 ⊨ b').

  Axiom valid_after_store: forall M1 M2 b b' κ δ v,
      store(κ, M1, b, δ, v) = ⎣M2⎦ ->
      (M2 ⊨ b' <-> M1 ⊨ b').

  Axiom alloc_undef: forall M1 M2 b δ κ n,
      alloc(M1, n) = (b, M2) /\
      0 <= δ /\ δ + sizeof(κ) <= Z.of_nat n ->
      load(κ, M2, b, δ) = ⎣Undef⎦.

  Axiom load_after_alloc: forall M1 M2 b b' n δ κ,
      b <> b' /\ alloc(M1, n) = (b, M2) ->
      load(κ, M2, b', δ) = load(κ, M1, b', δ).

  Axiom load_after_store_same: forall M1 M2 b δ v κ κ',
      store(κ, M1, b, δ, v) = ⎣M2⎦ /\
      0 <= δ /\ δ + sizeof(κ') <= length(M2, b) ->
      load(κ', M2, b, δ) = ⎣convert(v, κ, κ')⎦.

  Axiom load_after_store_overlap: forall M1 M2 b δ δ' κ κ' v,
      store(κ, M1, b, δ, v) = ⎣M2⎦ /\ δ <> δ' /\
      δ' < δ + sizeof(κ) /\ δ < δ' + sizeof(κ') /\
      0 <= δ' /\ δ' + sizeof(κ') <= length(M2, b) ->
      load(κ', M2, b, δ') = ⎣Undef⎦.

  Axiom load_after_store_other: forall M1 M2 b b' δ δ' κ κ' v,
      store(κ, M1, b, δ, v) = ⎣M2⎦ /\
      (b <> b' \/ δ + sizeof(κ) <= δ' \/ δ' + sizeof(κ') <= δ) ->
      load(κ', M2, b', δ') = load(κ', M1, b', δ').

  Axiom length_after_alloc_same: forall M1 M2 b n,
      alloc(M1, n) = (b, M2) ->
      length(M2, b) = Z.of_nat n.

  Axiom length_after_alloc_other: forall M1 M2 b b' n,
      b <> b' /\ alloc(M1, n) = (b, M2) ->
      length(M2, b') = length(M1, b').

  Axiom length_after_store: forall M1 M2 b b' δ κ v,
      store(κ, M1, b, δ, v) = ⎣M2⎦ ->
      length(M2, b') = length(M1, b').

  Axiom length_after_free: forall M1 M2 b b',
      b <> b' /\ free(M1, b) = ⎣M2⎦ ->
      length(M2, b') = length(M1, b').
  
  Axiom alloc_freshness: forall M1 M2 n b,
      alloc(M1, n) = (b, M2) ->
      not(b ∈ supp(M1)).

  Axiom validaccess_store: forall M1 b κ δ v,
      M1 ⫢ κ @ b,δ <-> exists M2, store(κ, M1, b, δ, v) = ⎣M2⎦.

  Axiom validaccess_load: forall M1 b κ δ,
      M1 ⫢ κ @ b,δ <-> exists v, load(κ, M1, b, δ) = ⎣v⎦.
    
  Axiom valid_implies_freeable: forall M1 b,
      M1 ⊨ b <-> exists M2, free(M1, b) = ⎣M2⎦.
    
End ExecutionMemoryModel.

Close Scope Z_scope.
