Require Import ZArith Arith Lia.
Require Import List. Import ListNotations.

From Vrac.Lib Require Import Option Tactics.
From Vrac.Memory Require Import MemoryType ExecutionMemoryModel.

Open Scope Z_scope.

Module Implementation: ExecutionMemoryModel Nat.

  Definition block := nat.
  
  Inductive value :=
  | Int : Z -> value
  | Ptr : block * Z -> value
  | Undef.

  Record Memory :=
    {
      allocated : list block;
      forbidden : list block;
      size: block -> Z;
      is_deallocated: block -> bool;
      content : block -> Z -> option(mtyp * value);
      invariant1: forall b, In b forbidden -> not(In b allocated);
      invariant2: forall b b' δ δ' κ,
        content b δ = ⎣(κ, Ptr(b',δ'))⎦ ->
        In b' allocated \/ In b' forbidden;
      invariant3: forall b,
        not(In b allocated) \/ is_deallocated b = true -> size b = 0%Z
    }.

  Definition mem := Memory.

  Definition is_valid (M: mem) (b: block) : bool :=
    (    existsb (Nat.eqb b) M.(allocated)
      && negb(M.(is_deallocated) b) )%bool.
  
  Inductive valid (M : mem) : block -> Prop :=
  | valid_definition : forall b,
      In b M.(allocated) -> 
      not(In b M.(forbidden)) ->
      M.(is_deallocated) b = false ->
      valid M b.

  Definition valid_block := valid.

  Infix "⊨" := valid_block (at level 70).
  
  
  Definition machine_word := i64.

  Lemma invariant1_empty:
    forall (b:nat), In b [] -> not(In b []).
  Proof.
    intros b H. inversion H.
  Qed.

  Lemma invariant2_empty:
    forall (b b':block) (δ δ':Z) (κ:mtyp),
      ϵ = ⎣ (κ, Ptr (b', δ')) ⎦ ->
      In b' [] \/ In b' [].
  Proof.
    intros; discriminate.
  Qed.

  Lemma invariant3_empty:
    forall b,
      not(In b []) \/ (fun b:block => false) b = true ->
      (fun b:block => 0) b = 0%Z.
  Proof. now intro. Qed.

  
  Definition empty :=
    {|
      allocated := [];
      forbidden  := [];
      size := fun b => 0;
      is_deallocated := fun b => false;
      content := fun b δ => ϵ;
      invariant1:= invariant1_empty;
      invariant2 := invariant2_empty;
      invariant3 := invariant3_empty
    |}.
   
  Definition is_valid_access (M: mem)(κ: mtyp)(b: block)(δ: Z) : bool :=
    (is_valid M b && (0 <=? δ) && (δ + sizeof κ <=? M.(size) b))%bool.

  Definition valid_access (M: mem) (κ: mtyp) (b:block) (δ: Z) :=
    M ⊨ b /\ 0 <= δ /\ δ + sizeof κ <= M.(size) b.

  Notation "M '⫢' κ '@' b ',' δ" := (valid_access M κ b δ) (at level 70).

  #[local] Hint Unfold is_valid valid_access is_valid_access : local.
  
  Ltac valid_block_and_access :=
    match goal with
    | [ H : valid_access _ _ _ _ |- _ ] =>
        inversion H; subst; clear H
    | [ H : valid_block _ _  |- _ ] =>
        inversion H; subst; clear H
    | [ |- valid_block _ _  ] => constructor
    end.

  Ltac by_invariant := 
    match goal with
    | [ H: In ?x (allocated ?M)  |- not(In ?x (forbidden ?M)) ] =>
        let HH := fresh "HH" in
        intro HH; apply (invariant1 M) in HH;
        now contradict HH
    | [ H: In ?x (allocated ?M), H': In ?x (forbidden ?M) |- _ ] =>
        let HH := fresh "HH" in
        apply (invariant1 M) in H';
        by_contradiction
    end.

  Ltac simpl_eqb :=
    repeat simpl_nat_eqb;
    repeat simpl_Z_eqb;
    repeat simpl_mtyp_eqb.
  
  Ltac reflect :=
    intros; 
    repeat(repeat(autounfold with local in *;
                  repeat destruct_and_hyp;
                  repeat destruct_or_hyp;
                  repeat negb;
                  repeat leb;
                  repeat Zleb;
                  repeat ltb;
                  repeat Zltb;
                  repeat valid_block_and_access;
                  repeat existsb_true;
                  repeat existsb_false);
           repeat imp;
           repeat destruct_and_goal;
           repeat simpl_eqb;
           repeat simpl_if;
           try solve [ lia ];
           try solve [ discriminate ];
           try solve [ by_contradiction ];
           try solve [ by_invariant ];
           auto;
           simpl in *).

  Lemma empty_not_valid:
    forall b, ~ empty ⊨ b.
  Proof.
    unfold valid_block.
    intros b H.
    inversion H.
    trivial.
  Qed.

  Lemma valid_iff_is_valid_true :
    forall M b, is_valid M b = true <-> M ⊨ b.
  Proof.
    reflect.
  Qed.

  Lemma valid_block_decidable:
    forall M b, M ⊨ b \/ not(M ⊨ b).
  Proof.
    intros M b.
    case_eq(is_valid M b); intro Hv.
    - apply valid_iff_is_valid_true in Hv.
      now left.
    - rewrite <- Bool.not_true_iff_false in Hv.
      rewrite valid_iff_is_valid_true in Hv.
      now right.
  Qed.
      
  Lemma valid_access_iff_is_valid_access_true :
    forall M κ b δ, is_valid_access M κ b δ = true <-> M ⫢ κ @ b,δ.
  Proof.
    reflect.
  Qed.

  Definition storable : value -> mtyp -> bool :=
    fun v κ =>
      match (v, κ) with
      | (Int n, κ) => (min_int (sizeof κ) <=? n) && (n <=? max_int (sizeof κ))
      | (Ptr _, κ) => sizeof κ =? sizeof machine_word
      | _ => false
      end%bool.

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

  Definition convert: value * mtyp * mtyp -> value :=
    fun argument =>
      match argument with
      | (v, κ, κ') => if (Mtyp.eqb κ κ') && (storable v κ)
                     then v
                     else Undef
      end%bool.

  #[local] Hint Unfold storable convert : local.
  
  Lemma alloc_invariant1 :
    forall M, let new_b := (1 + Nat.max (maximum M.(allocated))
                             (maximum M.(forbidden)))%nat in
         forall b, In b M.(forbidden) -> not(In b (new_b::M.(allocated))).
  Proof.
    intros M new_b b H.
    assert(HH: not(In new_b M.(forbidden))) by
            (unfold new_b; clear new_b; intro Hin;
             apply maximum_lt in Hin;
             lia).
    unfold new_b in *; clear new_b.
    contradict HH. simpl in *. destruct HH.
    - now subst.
    - apply (invariant1 M) in H.
      now contradict H.
  Qed.

  Lemma alloc_invariant2 :
    forall M (b b' : block) (δ δ' : Z) (κ : mtyp),
      let new_b := (1 + Nat.max (maximum M.(allocated))
                          (maximum M.(forbidden)))%nat in
      (if (b =? new_b)%nat then fun _ : Z => ϵ else content M b) δ =
        ⎣ (κ, Ptr (b', δ')) ⎦ ->
      In b' (new_b :: allocated M) \/ In b' (forbidden M).
  Proof.
    intros M b b' δ δ' κ new_b H.
    case_eq((b =? new_b)%nat); intro Heq; rewrite Heq in H.
    - discriminate.
    - apply (invariant2 M) in H.
      destruct H as [ H | H ]; [left;simpl; right | right];  auto.
  Qed.

  Lemma alloc_invariant3 :
    forall M n b,
      let new_b := (1 + Nat.max (maximum M.(allocated))
                          (maximum M.(forbidden)))%nat in
      let new_size := fun b => if (b =? new_b)%nat then Z.of_nat n else M.(size) b in
      let new_deallocated := fun b => if (b =? new_b)%nat then false
                                   else M.(is_deallocated) b in
      not(In b (new_b::allocated M)) \/ new_deallocated b = true ->
      new_size b = 0%Z.
  Proof.
    intros M n b new_b new_size new_deallocated [H | H];
      unfold new_size.
    - case_eq(Nat.eqb b new_b); intro Hb.
      + simpl_eqb. contradict H. now left.
      + apply invariant3. left. contradict H.
        simpl. now right.
    - case_eq(Nat.eqb b new_b); intro Hb; unfold new_deallocated in H.
      + simpl_eqb. simpl in H. simpl_eqb. discriminate.
      + apply invariant3. right.
        now rewrite Hb in H.
  Qed.
    
  Definition alloc : mem * nat -> block * mem :=
    fun argument =>
      let (M, n) := argument in
      let new_b := (1 + Nat.max (maximum M.(allocated))
                          (maximum M.(forbidden)))%nat in
      (new_b,
        Build_Memory
          (new_b::M.(allocated))
          (M.(forbidden))
          (fun b => if (b =? new_b)%nat then Z.of_nat n else M.(size) b)
          (fun b => if (b =? new_b)%nat then false else M.(is_deallocated) b)
          (fun b => if (b =? new_b)%nat
                 then fun δ => ϵ
                 else M.(content) b)
          (alloc_invariant1 M)
          (alloc_invariant2 M)
          (alloc_invariant3 M n)
      ).

  Definition free_invariant3 :
    forall M b,
      let new_size := (fun b' => if (b =? b')%nat then 0 else M.(size) b') in
      let new_deallocated := fun b' => if (b =? b')%nat  then true
                                    else M.(is_deallocated) b' in
      forall b', 
      not(In b' M.(allocated)) \/ new_deallocated b' = true ->
      new_size b' = 0.
  Proof.
    intros M b new_size new_deallocated b' H.
    unfold new_size, new_deallocated in *.
    case_eq(Nat.eqb b b'); intro Hb; trivial.
    rewrite Hb in H.
    now apply invariant3.
  Qed.

  Definition free : mem * block -> option mem :=
    fun argument =>
      let (M, b) := argument in
      if negb(is_valid M b)
      then ϵ
      else ⎣Build_Memory
             (M.(allocated))
             (M.(forbidden))
             (fun b' => if (b =? b')%nat then 0 else M.(size) b')
             (fun b' => if (b =? b')%nat  then true else M.(is_deallocated) b')
             (M.(content))
             (M.(invariant1))
             (M.(invariant2))
             (free_invariant3 M b)⎦.

  Lemma store_invariant1 :
    forall M v, let new_forbidden :=
              match v with
              | Ptr(b', _) => if existsb (Nat.eqb b') M.(allocated)
                             then M.(forbidden)
                             else b'::M.(forbidden)
              | _ => M.(forbidden)
              end in
         forall b, In b (new_forbidden) -> not(In b M.(allocated)).
  Proof.
    intros M v new_forbidden b H.
    destruct v as [ n | [b' δ'] | ].
    - now apply (invariant1 M) in H.
    - unfold new_forbidden in *. clear new_forbidden.
      simpl_if.
      + now apply (invariant1 M) in H.
      + destruct H as [ H | H ].
        * subst. existsb_false.
        * now apply invariant1.
    - now apply (invariant1 M) in H.
  Qed.


  Definition new_content κ M b δ v :=
    let sz := sizeof κ in 
    fun b' => if (b =? b')%nat
           then fun δ' =>
                  if ((δ<? δ') && (δ'<? δ + sz))%bool
                  then ϵ
                  else
                    if (δ'=? δ)
                    then ⎣(κ, v)⎦
                    else M.(content) b' δ'
           else M.(content) b'.

  Definition new_forbidden M v :=
    match v with
    | Ptr(b', _) => if existsb (Nat.eqb b') M.(allocated)
                   then M.(forbidden)
                   else b'::M.(forbidden)
    | _ => M.(forbidden)
    end.
    
  
  Lemma store_invariant2 :
    forall κ M b δ v b' b'' δ' δ'' κ',
      (new_content κ M b δ v) b' δ' = ⎣ (κ', Ptr (b'', δ'')) ⎦ ->
      In b'' (allocated M) \/ In b'' (new_forbidden M v).
  Proof.
    intros κ M b δ v b' b'' δ' δ'' κ' H.
    unfold new_content in H; simpl in H.
    unfold new_forbidden. simpl in H.
    assert(Hbeq: (b =? b)%nat = true) by now apply Nat.eqb_refl.
    assert(Hlt: (δ <? δ) = false) by lia.
    assert(Hδeq: (δ =? δ) = true) by lia.

    case_eq( (b =? b')%nat ); intro Hb; rewrite Hb in H.
    - assert(b = b') by now apply Nat.eqb_eq.
      subst. clear Hb.
      simpl_if; try discriminate; simpl_if.
      + clean_inv H.
        simpl_if.
        * left; reflect.
        * now (right; left).
      + destruct v as [ n | [b''' δ'''] | ];
          try solve [ eapply M.(invariant2); eauto ].
        simpl_if.
        * eapply M.(invariant2); eauto.
        * eapply M.(invariant2) in H; firstorder.
    - eapply M.(invariant2) in H; firstorder.
      destruct v as [ n | [b''' δ'''] | ]; auto.
      simpl_if; firstorder.
  Qed.
    
  Definition store : mtyp * mem * block * Z * value -> option mem :=
    fun argument =>
      match argument with
      | (κ, M, b, δ, v) => 
          if is_valid_access M κ b δ
          then
            ⎣Build_Memory
              M.(allocated)
              (new_forbidden M v)
              (M.(size))
              (M.(is_deallocated))
              (new_content κ M b δ v)
              (store_invariant1 M v)
              (store_invariant2 κ M b δ v)
              M.(invariant3)⎦
          else ϵ
      end.

  Definition load : mtyp * mem  * block * Z -> option value :=
    fun argument =>
      match argument with
      | (κ, M, b, δ) => 
          if is_valid_access M κ b δ
          then
            match M.(content) b δ with
            | ⎣(κ', v)⎦ =>
                let size_minus_1_values_from_δ_plus_1 :=
                  let size := sizeof κ in
                  let start := Z.to_nat (δ + 1) in
                  let len := ((Z.to_nat size) - 1)%nat in 
                  let indexes := List.map Z.of_nat (List.seq start len) in
                  map (M.(content) b) indexes in
                if ((Mtyp.eqb κ κ') && (storable v κ) &&
                     (forallb is_ϵ size_minus_1_values_from_δ_plus_1))%bool
                then ⎣convert(v,κ',κ)⎦
                else ⎣Undef⎦
            | _ => ⎣Undef⎦
            end
          else ϵ
      end.

  Definition length : mem * block -> Z :=
    fun argument =>
      let (M, b) := argument in
      M.(size) b.

  #[local] Hint Unfold length : local.

  Inductive in_supp (b: block) (M: mem) : Prop :=
  | in_supp_valid : M ⊨ b -> in_supp b M
  | in_supp_loadable : forall b' b'' δ δ' κ,
      b'' = b -> 
      load(κ, M, b', δ') = Some(Ptr(b'', δ)) ->
      in_supp b M.

  Notation "b '∈' 'supp' '(' M ')'" :=
    (in_supp b M) (at level 70).
  
  Ltac inversions :=
    match goal with
    | [ H: free _ = _ |- _ ] => clean_inv H
    | [ H: alloc _ = _ |- _ ] => clean_inv H
    | [ H: store _ = _ |- _ ] => clean_inv H
    | [ H: valid_block _ _ |- _ ] => clean_inv H
    | [ H: (_,_) = (_,_) |- _ ] => clean_inv H
    | [ H: Some _ = Some _ |- _ ] => clean_inv H
    | [ H: _ :: _ = _ :: _ |- _ ] => clean_inv H
    end.

  Ltac mauto :=
    repeat(repeat reflect; repeat inversions; simpl in *;
           try match goal with
           | [ |- ~_ ] => let H := fresh "H" in intro H
           end).
  
  Lemma convert_storable :
    forall v κ, storable v κ = true -> convert(v, κ, κ) = v.
  Proof.
    reflect.
  Qed.

  Lemma convert_different_mtyp_undef :
    forall v κ κ', κ <> κ' -> convert(v, κ, κ') = Undef.
  Proof.
    reflect.
  Qed.

  Lemma convert_not_storable_undef :
    forall v κ κ', storable v κ = false -> convert(v, κ, κ') = Undef.
  Proof.
    reflect.
  Qed.

  Lemma length_after_alloc_same: forall M1 M2 b n,
      alloc(M1, n) = (b, M2) ->
      length(M2, b) = Z.of_nat n.
  Proof.
    mauto.
  Qed.

  Lemma length_after_alloc_other: forall M1 M2 b b' n,
      b <> b' /\ alloc(M1, n) = (b, M2) ->
      length(M2, b') = length(M1, b').
  Proof.
    mauto.
  Qed.
    
  Lemma length_after_store: forall M1 M2 b b' δ κ v,
      store(κ, M1, b, δ, v) = ⎣M2⎦ ->
      length(M2, b') = length(M1, b').
  Proof.
    mauto.
  Qed.

  Lemma length_after_free: forall M1 M2 b b',
      b <> b' /\ free(M1, b) = ⎣M2⎦ ->
      length(M2, b') = length(M1, b').
  Proof.
    mauto.
  Qed.
  
  Lemma valid_after_alloc_same: forall M1 M2 n b,
      alloc(M1, n) = (b, M2) ->
      M2 ⊨ b.
  Proof.
    mauto.
    apply maximum_lt in H. lia.
  Qed.

  Lemma valid_after_alloc_other: forall M1 M2 b b' n,
      b <> b' /\ alloc(M1, n) = (b, M2) ->
      (M2 ⊨ b' <-> M1 ⊨ b').
  Proof.
    mauto.
  Qed.

  Lemma invalid_after_free: forall M1 M2 b,
      free(M1, b) = ⎣M2⎦ -> not(M2 ⊨ b).
  Proof.
    mauto.
  Qed.
    
  Lemma valid_after_free: forall M1 M2 b b',
      b <> b' /\ free(M1, b) = ⎣M2⎦ ->
      (M2 ⊨ b' <-> M1 ⊨ b').
  Proof.
    mauto.
  Qed.
  
  Lemma valid_after_store: forall M1 M2 b b' κ δ v,
      store(κ, M1, b, δ, v) = ⎣M2⎦ ->
      (M2 ⊨ b' <-> M1 ⊨ b').
  Proof.
    intros M1 M2 b b' κ δ v H; split; intro H';
      inversions; simpl_if; clean_inv H1;
      apply valid_iff_is_valid_true in H';
      unfold is_valid in *; simpl in *;
      now apply valid_iff_is_valid_true.
  Qed.

  Lemma alloc_undef: forall M1 M2 b δ κ n,
      alloc(M1, n) = (b, M2) /\
      0 <= δ /\ δ + sizeof(κ) <= Z.of_nat n ->
      load(κ, M2, b, δ) = ⎣Undef⎦.
  Proof.
    mauto.
  Qed.
  
  Lemma load_after_alloc: forall M1 M2 b b' n δ κ,
      b <> b' /\ alloc(M1, n) = (b, M2) ->
      load(κ, M2, b', δ) = load(κ, M1, b', δ).
  Proof.
    mauto.
  Qed.

  Lemma load_after_free: forall M1 M2 b b' δ κ,
      b <> b' /\ free(M1, b) = ⎣M2⎦ ->
      load(κ, M2, b', δ) = load(κ, M1, b', δ).
  Proof.
    mauto.
  Qed.
  
  Lemma load_after_store_same: forall M1 M2 b δ v κ κ',
      store(κ, M1, b, δ, v) = ⎣M2⎦ /\
        0 <= δ /\ δ + sizeof(κ') <= length(M2, b) ->
      load(κ', M2, b, δ) = ⎣convert(v, κ, κ')⎦.
  Proof.
    intros M1 M2 b δ v κ κ' H.
    destruct H as [Hstore [Hδl Hδh]].
    assert(Hva1: valid_access M1 κ b δ).
    {
      unfold store in Hstore.
      case_eq(is_valid_access M1 κ b δ); intro IsValidAccess.
      - now apply valid_access_iff_is_valid_access_true.
      - rewrite IsValidAccess in Hstore; simpl in Hstore; discriminate.
    }
    assert(Hva2: valid_access M2 κ' b δ).
    {
      unfold valid_access in *;
        repeat destruct_and_hyp;
        repeat destruct_and_goal; auto.
      apply valid_after_store with (b':=b) in Hstore.
      now apply Hstore.
    }
    unfold store in Hstore.
    apply valid_access_iff_is_valid_access_true in Hva1.
    rewrite Hva1 in Hstore. inversion Hstore as [HM2]; clear Hstore.
    simpl. rewrite HM2. apply valid_access_iff_is_valid_access_true in Hva2.
    rewrite Hva2. unfold new_content. simpl_eqb; 
    assert(H: (δ <? δ) = false) by lia.
    rewrite H. simpl. clear H.
    simpl_eqb. 
    case_eq(Mtyp.eqb κ' κ); intro Mtyp.
    - apply Mtyp.eqb_eq in Mtyp; rewrite Mtyp in *;
        simpl_mtyp_eqb; clear Mtyp. symmetry in HM2.
      case_eq(storable v κ); intro Storable; simpl; auto.
      subst; clear Hva2 Hva1 Storable; simpl in *.
      apply natlike_rec with (x:=sizeof κ).
      + intros; trivial.
      + intros n H H0.
        replace (Z.to_nat (Z.succ n) - 1)%nat with (Z.to_nat n) by lia.
        case_eq(n =? 0); intro Hn.
        * now simpl_eqb.
        * apply Z.eqb_neq in Hn.
          assert(Hcut:(Z.to_nat n = S (Z.to_nat(n-1)))%nat) by lia.
          rewrite Hcut.
          rewrite seq_S, map_app, map_app, forallb_app.
          match goal with
          | [ |- context [(?X && ?Y)%bool] ] =>
              case_eq(X);intro Hfb
          end.
          -- simpl. unfold is_ϵ.
             rewrite Nat2Z.inj_add, Z2Nat.id by lia.
             match goal with
             | [ |- context [if (?X && ?Y)%bool then ϵ else _] ] =>
                 assert(HH: X = true)
             end.
             rewrite Z.ltb_lt; lia.
             rewrite HH; simpl.
             assert(HHH: δ + 1 + Z.of_nat (Z.to_nat (n - 1)) <? δ + Z.succ n = true)
               by (rewrite Z2Nat.id by lia; rewrite Z.ltb_lt; lia).
             now rewrite HHH.
          -- replace (Z.to_nat (n - 1)) with
               (Z.to_nat n - 1)%nat in Hfb by lia.
             erewrite map_ext_in in H0.
             now rewrite Hfb in H0.
             intros a Hin. simpl. apply in_map_iff in Hin.
             destruct Hin as [k [Hk1 Hk2]].
             assert(Hk: k = Z.to_nat a) by (rewrite <- Hk1; lia).
             clear Hk1. subst.
             apply in_seq in Hk2.
             assert(HH:((δ <? a) && (a <? δ + n))%bool = true) by lia.
             assert(HH': Z.succ n = n+1) by lia.
             rewrite HH' in *.
             assert(HH'':((δ <? a) && (a <? δ + (n+1)))%bool = true) by lia.
             now rewrite HH, HH''.
      + now destruct κ.
    - rewrite Mtyp.eqb_sym in Mtyp. now rewrite Mtyp.
  Qed.

  Lemma load_after_store_overlap: forall M1 M2 b δ δ' κ κ' v,
      store(κ, M1, b, δ, v) = ⎣M2⎦ /\ δ <> δ' /\
      δ' < δ + sizeof(κ) /\ δ < δ' + sizeof(κ') /\
      0 <= δ' /\ δ' + sizeof(κ') <= length(M2, b) ->
      load(κ', M2, b, δ') = ⎣Undef⎦.
  Proof.
    intros M1 M2 b δ δ' κ κ' v H.
    repeat destruct_and_hyp. inversions. 
    assert(Hva2: is_valid_access M2 κ' b δ' = true) by mauto.
    assert(Hva1: is_valid_access M1 κ b δ = true) by mauto.
    assert(Hb: (b =? b)%nat = true) by reflect.
    assert(Hsz: 0 < sizeof κ) by now destruct κ.
    assert(Hsz': 0 < sizeof κ') by now destruct κ'.
    assert(Hlt1: δ' <? δ + sizeof κ = true) by lia.
    assert(Hdiff: (δ' =? δ) = false) by lia.
    assert(Heq: (δ =? δ) = true) by lia.
    rewrite Hva2.
    rewrite Hva1 in H5.
    clean_inv H5.
    unfold new_content.
    rewrite Hb, Hlt1; simpl.
    case_eq( (δ <? δ') ); intro Hlt.
    - trivial.
    - simpl. rewrite Hdiff.
      destruct(content M1 b δ') as [ [κ'' v'] | ].
      + simpl_if. repeat destruct_and_hyp.
        * assert( δ' <  δ ) by lia.
          set(k := δ - δ').
          assert(0 < k) by lia.
          assert(k < sizeof κ') by lia.
          assert(δ = δ' + k) by lia.
          set(len :=  (Z.to_nat (sizeof κ') - 1)%nat) in *.
          assert(len = (Z.to_nat k) + (len-Z.to_nat k))%nat by lia.
          replace len with (((Z.to_nat k) + (len-Z.to_nat k))%nat) in * by auto.
          rewrite seq_app in H5.
          repeat rewrite map_app in H5.
          rewrite forallb_app in H5.
          assert(HH:((Z.to_nat (δ' + 1) + (Z.to_nat k - 1)) = Z.to_nat δ)%nat) by lia.
          set(n := Z.to_nat(k-1)) in *.
          assert(HH': Z.to_nat k = S n) by lia.
          rewrite HH' in H5.
          rewrite seq_S in H5.
          assert(HH'': (Z.to_nat (δ' + 1) + n)%nat = Z.to_nat δ) by lia.
          rewrite HH'' in H5.
          repeat rewrite map_app in H5.
          simpl in H5.
          assert(HHH: δ = Z.of_nat (Z.to_nat δ)) by lia.
          rewrite <- HHH in H5.
          assert(HHH': ((δ <? δ) && (δ <? δ + sizeof κ))%bool = false) by lia.
          rewrite HHH', Heq in H5.
          rewrite forallb_app in H5.
          rewrite Bool.andb_false_r in H5.
          simpl in H5.
          discriminate.
        * trivial.
      + trivial.
  Qed.

  Lemma load_after_store_other: forall M1 M2 b b' δ δ' κ κ' v,
      store(κ, M1, b, δ, v) = ⎣M2⎦ /\
      (b <> b' \/ δ + sizeof(κ) <= δ' \/ δ' + sizeof(κ') <= δ) ->
      load(κ', M2, b', δ') = load(κ', M1, b', δ').
  Proof.
    intros M1 M2 b b' δ δ' κ κ' v H.
    destruct_and_hyp.
    unfold load.
    assert(Hsize : length (M2, b') = length (M1, b'))
      by (eapply length_after_store; eauto).
    assert(HH: is_valid_access M2 κ' b' δ' =
                 is_valid_access M1 κ' b' δ').
    {
      unfold is_valid_access.
      f_equal; trivial.
      f_equal; trivial.
      - apply valid_after_store with (b':=b') in H0.
        destruct H0 as [HM1 HM2].
        case_eq(is_valid M2 b'); case_eq(is_valid M1 b');
          intros H' H''; auto.
        + apply valid_iff_is_valid_true in H''.
          apply Bool.not_true_iff_false in H'.
          contradict H'.
          apply valid_iff_is_valid_true.
          auto.
        + apply valid_iff_is_valid_true in H'.
          apply Bool.not_true_iff_false in H''.
          contradict H''.
          apply valid_iff_is_valid_true.
          now apply HM2.
      - unfold length in Hsize; now rewrite Hsize.
    }
    clean_inv H0.
    case_eq(is_valid_access M1 κ b δ); intro Hva; rewrite Hva in H2;
      try discriminate.
    case_eq(is_valid_access M2 κ' b' δ');
      case_eq(is_valid_access M1 κ' b' δ');
      intros H' H''; rewrite H', H'' in HH; try discriminate; clear HH;
      clean_inv H2; auto.

    apply valid_access_iff_is_valid_access_true in Hva.
    destruct Hva as [ Hva [HH' HH'']]; simpl in *.

    destruct H1 as [Hdiff | [ Habove | Hbelow ] ]; unfold new_content.
    - now simpl_eqb.
    - case_eq((b =? b') %nat); intro Hbb'; auto.
      assert(HH1 : (δ <? δ') = true) 
        by (assert(0 < sizeof κ) by (now destruct κ); lia).
      assert(HH2 : (δ' <? δ + sizeof κ) = false) by lia.
      assert(HH3 : (δ' =? δ) = false) by lia. 
      rewrite HH1, HH2, HH3; simpl.
      destruct(content M1 b' δ'); auto.
      destruct p as [ κ'' v'' ].
      rewrite map_ext_in with (g:= content M1 b'). reflect.
      intros a Hin.
      apply in_map_iff in Hin.
      destruct Hin as [k [Hk1 Hk2]].
      assert(Hk: k = Z.to_nat a) by (rewrite <- Hk1; lia).
      clear Hk1. subst.
      apply in_seq in Hk2.
      reflect.
    - case_eq((b =? b') %nat); intro Hbb'; auto.
      assert(HH1 : (δ <? δ') = false) 
        by (assert(0 < sizeof κ') by (now destruct κ'); lia).
      assert(HH2 : (δ' <? δ) = true) 
        by (assert(0 < sizeof κ') by (now destruct κ'); lia).
      assert(HH3 : (δ' =? δ) = false) by lia. 
      rewrite HH1, HH3; simpl.
      destruct(content M1 b' δ'); auto.
      destruct p as [ κ'' v'' ].
      rewrite map_ext_in with (g:= content M1 b'). reflect.
      intros a Hin.
      apply in_map_iff in Hin.
      destruct Hin as [k [Hk1 Hk2]].
      assert(Hk: k = Z.to_nat a) by (rewrite <- Hk1; lia).
      clear Hk1. subst.
      apply in_seq in Hk2.
      reflect.
  Qed.
  
  Lemma alloc_freshness: forall M1 M2 n b,
      alloc(M1, n) = (b, M2) ->
      not(b ∈ supp(M1)).
  Proof.
    intros M1 M2 n b H Hsupp.
    clean_inv Hsupp.
    - clean_inv H.
      clean_inv H0.
      apply maximum_lt in H; lia.
    - clean_inv H.
      simpl_if.
      + case_eq(content M1 b' δ').
        * intros [κ' v'] Hc.
          rewrite Hc in H1.
          destruct v' as [ n' | [b'' δ''] | ].
          -- simpl_if; inversion H1. reflect.
          -- apply M1.(invariant2) in Hc;
               simpl_if; clean_inv H0; mauto; subst;
               apply maximum_lt in Hc; lia.
          -- simpl_if; clean_inv H1. reflect.
        * intro Hc; rewrite Hc in H1; inversion H1.
      + inversion H1.
  Qed.
             
  Lemma validaccess_store: forall M1 b κ δ v,
      M1 ⫢ κ @ b,δ <-> exists M2, store(κ, M1, b, δ, v) = ⎣M2⎦.
  Proof.
    intros M1 b κ δ v; split; intro Hva.
    - mauto; eexists; reflect.
    - destruct Hva as [ M2 Hstore].
      mauto.
  Qed.

  Lemma validaccess_load: forall M1 b κ δ,
      M1 ⫢ κ @ b,δ <-> exists v, load(κ, M1, b, δ) = ⎣v⎦.
  Proof.
    intros M1 b κ δ; split; intro Hva.
    - unfold load; simpl_if.
      + case_eq(content M1 b δ).
        * intros [κ' v] Hc;  simpl_if; eauto.
        * eauto.
      + reflect.
    - destruct Hva as [ M2 Hstore].
      mauto.
  Qed.
    
  Lemma valid_implies_freeable: forall M1 b,
      M1 ⊨ b <-> exists M2, free(M1, b) = ⎣M2⎦.
  Proof.
    intros M1 b; split; intro H.
    - apply valid_iff_is_valid_true in H.
      unfold free; rewrite H; simpl; eauto.
    - destruct H as [M2 H].
      mauto.
  Qed.

  Lemma invalid_length : forall M b,
      not(M ⊨ b) -> length(M, b) = 0%Z.
  Proof.
    intros M b H.
    unfold length, valid_block in *.
    apply invariant3.
    rewrite <- Bool.not_false_iff_true.
    rewrite or_comm.
    apply Decidable.not_and.
    - destruct(is_deallocated M b);
        [ right; intros; discriminate |
          now left ].
    - contradict H.
      destruct H as [H1 H2].
      constructor; auto.
      intro H. apply invariant1 in H.
      by_contradiction.
  Qed.
  
End Implementation.

Close Scope Z_scope.
