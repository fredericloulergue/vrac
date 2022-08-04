Require Import Arith ZArith Lia List Structures.Equalities Logic.FinFun.
Require Import Vrac.Tactics Vrac.Option Vrac.Eqb
  Vrac.MemoryType Vrac.ExecutionMemoryModel.


Module Context(V : DecidableType)(B: Eqb.EQB)
  (Import EMM: ExecutionMemoryModel B).

  Module Block := Full B. Import Block.

  Ltac simpl_block_eqb :=
    simpl_generic_eqb eqb Block.eqb_refl Block.eqb_sym
      Block.eqb_eq Block.eqb_neq.
  
  Definition environment := V.t -> option Block.t.
  
  Record context := {
      E: environment;
      M: mem;
      wf: forall x b, E x = ⎣b⎦ -> M ⊨ b
    }.

  Definition induced (σ: Block.t -> Block.t) (Hσ: Bijective σ) :=
    fun value => match value with
              | Int n => Int n
              | Undef => Undef
              | Ptr(b, δ) => Ptr(σ(b), δ)
              end.

  Class isomorphic (C1 C2: context)(σ: Block.t -> Block.t)(Hσ: Bijective σ) :=
    {
      iso_environment: forall x b, C1.(E) x = ⎣b⎦ <-> C2.(E) x = ⎣σ b⎦;
      iso_valid_block: forall b, C1.(M) ⊨ b <-> C2.(M) ⊨ σ(b);
      iso_length: forall b, C1.(M)⊨b -> length(C1.(M), b) = length(C2.(M), σ(b));
      iso_load: forall κ b δ v, load(κ, C1.(M), b, δ) = ⎣v⎦ <->
                             load(κ, C2.(M), σ b, δ) = ⎣(induced σ Hσ) v⎦
    }.

  Property valid_access_after_alloc:
    forall M1 M2 b b' n δ κ,
      b'<>b ->
      alloc(M1,n) = (b,M2) ->
      M1 ⫢ κ @ b',δ <-> M2 ⫢ κ @ b',δ.
  Proof.
    intros M1 M2 b b' n δ κ Halloc.
    split; intro Hva.
    - destruct Hva as [Hv [H1 H2]].
      repeat split; auto.
      now eapply valid_after_alloc_other; eauto.
      erewrite length_after_alloc_other; eauto.
    - destruct Hva as [Hv [H1 H2]].
      repeat split; eauto.
      erewrite <- valid_after_alloc_other with(M1:=M1); repeat split; eauto.
      erewrite <- length_after_alloc_other; repeat split; eauto.
  Qed.

  Property valid_access_after_free:
    forall M1 M2 b b' δ κ,
      b'<>b ->
      free(M1, b) = ⎣M2⎦ ->
      M1 ⫢ κ @ b',δ <-> M2 ⫢ κ @ b',δ.
  Proof.
    intros M1 M2 b b' δ κ H Hfree.
    split; intro Hva.
    - destruct Hva as [Hv [H1 H2]].
      repeat split; auto.
      now eapply valid_after_free; eauto.
      erewrite length_after_free; eauto.
    - destruct Hva as [Hv [H1 H2]].
      repeat split; eauto.
      erewrite <- valid_after_free with(M1:=M1); repeat split; eauto.
      erewrite <- length_after_free; repeat split; eauto.
  Qed.

  Property valid_access_after_store:
    forall M1 M2 b b' δ δ' κ κ' v,
      store(κ,M1,b,δ,v) = ⎣M2⎦ ->
      M1 ⫢ κ' @ b',δ' <-> M2 ⫢ κ' @ b',δ'.
  Proof.
    intros M1 M2 b b' δ κ κ' v Hstore.
    split; intro Hva.
    - destruct Hva as [Hv [H1 H2]].
      repeat split; auto.
      now eapply valid_after_store; eauto.
      erewrite length_after_store; eauto.
    - destruct Hva as [Hv [H1 H2]].
      repeat split; eauto.
      erewrite <- valid_after_store with(M1:=M1); repeat split; eauto.
      erewrite <- length_after_store; repeat split; eauto.
  Qed.

  Property isomorphic_valid_access:
    forall C1 C2 σ Hσ,
      isomorphic C1 C2 σ Hσ ->
      (forall κ b δ, C1.(M) ⫢ κ @ b,δ <-> C2.(M) ⫢ κ @ σ(b),δ).
  Proof.
    intros C1 C2 σ Hσ Hiso κ b δ.
    unfold valid_access; 
    split; intro Hva; clean_inv Hva;
      repeat destruct_and_hyp;
      repeat destruct_and_goal;
      try solve [ firstorder ].
    - now rewrite <- (Hiso.(iso_length)).
    - now rewrite Hiso.(iso_length) by (now apply Hiso.(iso_valid_block)).
  Qed.
        
  Property isomorphic_in_supp_σ:
    forall C1 C2 σ Hσ,
      isomorphic C1 C2 σ Hσ ->
      forall b, b ∈ supp( C1.(M) ) -> σ(b) ∈ supp(C2.(M)).
  Proof.
    intros C1 C2 σ Hσ Hiso b.
    intro Hsupp;inversion Hsupp as [ Hv | b' b'' δ' δ'' κ Heq Hl ]; subst;
      try (apply Hiso.(iso_valid_block) in Hv; now constructor).
    rewrite Hiso.(iso_load) in Hl.
    assert(Hv: C2.(M) ⫢ κ @ σ b', δ'' )
      by (apply validaccess_load; eexists; eauto).
    assert(M C2 ⊨ σ b')
      by (unfold valid_access in Hv; now destruct_and_hyp).
    econstructor 2; eauto.
  Qed.

  Property isomorphic_in_supp_invσ:
    forall C1 C2 σ Hσ,
      isomorphic C1 C2 σ Hσ ->
      forall b, b ∈ supp(C2.(M)) -> (exists b', b = σ(b') /\ b' ∈ supp(C1.(M))).
  Proof.
    intros C1 C2 σ Hσ Hiso b Hsupp.
    assert(Hb': exists b', b = σ b')
      by (destruct Hσ as [invσ [Hσ1 Hσ2]]; now exists(invσ b)).
    destruct Hb' as [b' Hb'].
    exists b'; split; auto.
    inversion Hsupp as [ Hv | b'' b''' δ' δ'' κ Heq Hl ]; subst;
      try (apply Hiso.(iso_valid_block) in Hv; now constructor).
    assert(Hb': exists b''', b'' = σ b''')
      by (destruct Hσ as [invσ [Hσ1 Hσ2]]; now exists(invσ b'')).
    destruct Hb' as [b''' Hb'].
    assert(Hi: Ptr (σ b', δ') = induced σ Hσ (Ptr(b', δ'))) by auto.
    rewrite Hi, Hb' in Hl.
    econstructor 2; eauto.
    rewrite Hiso.(iso_load). 
    eauto.
  Qed.

  Property isomorphic_in_supp_only:
    forall C1 C2 σ Hσ σ' Hσ',
      isomorphic C1 C2 σ Hσ ->
      (forall b, b ∈ supp( C1.(M) ) -> σ b = σ' b) ->
      isomorphic C1 C2 σ' Hσ'.
  Proof.
    intros C1 C2 σ Hσ σ' Hσ' Hiso Hsupp.
    constructor. 
    - intros x b. split; intro HE.
      + rewrite <- Hsupp
          by (constructor; eapply wf; eauto).
        now rewrite <- Hiso.(iso_environment).
      + assert(σ' b ∈ supp(C2.(M))) 
          by (eapply wf in HE; now constructor).
        apply isomorphic_in_supp_invσ with (C1:=C1)(σ:=σ)(Hσ:=Hσ) in H; auto.
        destruct H as [b' [H1 H2]].
        specialize (Hsupp _ H2).
        rewrite Hsupp in H1.
        destruct Hσ' as [invσ' [Hσ'1 Hσ'2]].
        assert(b = b')
          by (rewrite <- Hσ'1 with (x:=b);
              rewrite <- Hσ'1 with (x:=b');
              now rewrite H1).
        subst.
        rewrite <- Hsupp in HE.
        now rewrite <- Hiso.(iso_environment) in HE.
    - intros b; split; intro Hvb.
      + rewrite <- Hsupp by now constructor.
        now rewrite <- Hiso.(iso_valid_block).
      + assert(σ' b ∈ supp(C2.(M))) 
          by now constructor.
        apply isomorphic_in_supp_invσ with (C1:=C1)(σ:=σ)(Hσ:=Hσ) in H; auto.
        destruct H as [b' [H1 H2]].
        specialize (Hsupp _ H2).
        rewrite Hsupp in H1.
        destruct Hσ' as [invσ' [Hσ'1 Hσ'2]].
        assert(b = b')
          by (rewrite <- Hσ'1 with (x:=b);
              rewrite <- Hσ'1 with (x:=b');
              now rewrite H1).
        subst.
        rewrite <- Hsupp in Hvb.
        now apply Hiso.(iso_valid_block).
    - intros b  Hvb.
      rewrite <- Hsupp by now constructor.
      now rewrite <- Hiso.(iso_length).
    - intros κ b δ v.
      split; intro Hl.
      + assert(H: exists v, load (κ, M C1, b, δ) =  ⎣v⎦) by (eexists;eauto).
        assert(Hv: M C1 ⊨ b)
          by (rewrite <- validaccess_load in H;
              unfold valid_access in H; now destruct_and_hyp).
        assert(Hi: induced σ' Hσ' v = induced σ Hσ v)
          by (destruct v; auto; simpl; destruct p;
              rewrite <- Hsupp; trivial;
              econstructor 2; eauto).
        rewrite Hi; clear Hi.
        rewrite <- Hsupp by now constructor.
        now apply Hiso.(iso_load).
      + assert(H: exists v, load (κ, M C2, σ' b, δ) =  ⎣v⎦) by (eexists;eauto).
        assert(Hv: M C2 ⊨ σ' b)
          by (rewrite <- validaccess_load in H;
              unfold valid_access in H; now destruct_and_hyp).
        assert(HH: σ' b ∈ supp(C2.(M))) 
          by now constructor.
        apply isomorphic_in_supp_invσ with (C1:=C1)(σ:=σ)(Hσ:=Hσ) in HH; auto.
        destruct HH as [b' [H1 H2]].
        assert(Hi: induced σ' Hσ' v = induced σ Hσ v).
        {
          destruct v as [n|[b0 δ0]|]; auto; simpl; subst.
          simpl in Hl.
          assert(HH: σ' b0 ∈ supp(C2.(M))) by (econstructor 2; eauto).
          apply isomorphic_in_supp_invσ with (C1:=C1)(σ:=σ)(Hσ:=Hσ) in HH; auto.
          destruct HH as [b1 [H3 H4]].
          specialize (Hsupp _ H4).
          destruct Hσ' as [invσ' [Hσ'1 Hσ'2]].
          assert(b0 = b1)
            by(rewrite <- Hσ'1 with (x:=b0);
               rewrite <- Hσ'1 with (x:=b1);
               now rewrite H3, <- Hsupp).
          subst.
          now rewrite Hsupp.
        }
        rewrite Hi in Hl.
        assert(b = b')
          by (destruct Hσ' as [invσ' [Hσ'1 Hσ'2]];
              rewrite <- Hσ'1 with (x:=b);
              rewrite <- Hσ'1 with (x:=b');
              now rewrite H1, <- Hsupp).
        subst.
        apply Hiso.(iso_load).
        now rewrite <- H1.
  Qed.

  Corollary load_ϵ:
    forall κ M b δ,
      ~(M ⫢ κ @ b,δ) -> load(κ, M, b, δ) = ϵ.
  Proof.
    intros κ M0 b δ H.
    case_eq(load(κ, M0, b, δ)).
    - intros v Hl.
      assert(M0 ⫢ κ @ b,δ)
        by (apply validaccess_load; now exists v).
      by_contradiction.
    - trivial.
  Qed.
  
  Property isomorphic_alloc:
    forall C1 C2 M'1 M'2 b1 b2 σ Hσ n,
      isomorphic C1 C2 σ Hσ ->
      alloc(C1.(M), n) = (b1, M'1) ->
      alloc(C2.(M), n) = (b2, M'2) ->
      exists σ' Hσ' Hwf1 Hwf2,
        isomorphic {| E := C1.(E); M := M'1; wf := Hwf1 |}
                   {| E := C2.(E); M := M'2; wf := Hwf2  |} σ' Hσ'
          /\ (forall b, b <> b1 /\ σ b <> b2 -> σ' b = σ b)
          /\ (σ' b1 = b2)
          /\ (forall b, σ b = b2 -> σ' b = σ b1).
  Proof.
    intros C1 C2 M'1 M'2 b1 b2 σ Hσ n Hiso Halloc1 Halloc2.
    destruct Hσ as [inv_σ [Hinvσ1 Hinvσ2]].
    set(σ' := fun b => if (eqb b b1)
                    then b2
                    else if (eqb b (inv_σ b2))
                         then σ b1
                         else σ b).
    set(inv_σ' := fun b => if (eqb b b2)
                        then b1
                        else if (eqb b (σ b1))
                             then inv_σ b2
                             else inv_σ b).
    assert(Hσ'1: forall b : t, inv_σ' (σ' b) = b).
    {
      unfold inv_σ', σ'; intro b.
      repeat simpl_if; repeat simpl_block_eqb; auto; try discriminate.
      - rewrite  Hinvσ1 in H1. now simpl_block_eqb.
      - assert(b = b1).
        {
          rewrite <- Hinvσ1 with (x:=b).
          rewrite <- Hinvσ1 with (x:=b1).
          now rewrite H2.
        }
        simpl_block_eqb.
        now by_contradiction.
    }
    assert(Hσ'2: forall b : Block.t, σ' (inv_σ' b) = b).
    {
      intros b; unfold σ', inv_σ'.
      repeat simpl_if; repeat simpl_block_eqb; auto; try discriminate.
      - rewrite  Hinvσ2 in H1. now simpl_block_eqb.
      - assert(b = b2).
        {
          rewrite <- Hinvσ2 with (y:=b).
          rewrite <- Hinvσ2 with (y:=b2).
          now rewrite H2.
        }
        simpl_block_eqb.
        now by_contradiction.        
    }
    assert(Hσ': Bijective σ')
      by (exists inv_σ'; split; intro b; auto).
    assert(Hb2: forall b, σ b = b2 <-> b = inv_σ b2).
    {
      intros b; split; intro H.
      - rewrite <- H. now rewrite Hinvσ1.
      - rewrite H. now rewrite Hinvσ2.
    }
    assert(Hσeq: forall b : Block.t, b <> b1 /\ σ b <> b2 -> σ' b = σ b).
    {
      intros b H.
      destruct H; unfold σ'; repeat simpl_if; simpl_block_eqb.
      - by_contradiction.
      - rewrite Hinvσ2 in H0. by_contradiction.
      -trivial.
    }
    assert(H'σeq: forall b : Block.t, b <> b1 /\ b <> inv_σ b2 -> σ' b = σ b).
    {
      intros b [H1 H2].
      assert(σ b <> b2) by (contradict H2; apply Hb2; auto).
      now apply Hσeq.
    }
    assert(Hσ2: σ' b1 = b2) by
      (unfold σ'; repeat simpl_if; auto; now simpl_block_eqb).
    assert(Hσ1: forall b : Block.t, σ b = b2 -> σ' b = σ b1).
    {
      clear Hσ2; intros b H.
      unfold σ'; repeat simpl_if; auto.
      - now simpl_block_eqb.
      - assert(b = inv_σ b2) by (rewrite <- H; now rewrite Hinvσ1).
        simpl_block_eqb.
        by_contradiction.
    }
    assert(H'σ1: forall b : Block.t, b = inv_σ b2 -> σ' b = σ b1).
    {
      intros b H. rewrite H.
      unfold σ'. simpl_block_eqb.
      simpl_if.
      - simpl_block_eqb.
        rewrite <- H0.
        now rewrite Hinvσ2.
      - trivial.
    } 
    assert(Cases: forall b, b=b1 \/ (b <> b1 /\ b = inv_σ b2)
                       \/ (b <> b1 /\ b <> inv_σ b2)).
    {
      intros b.
      case_eq(eqb b b1); case_eq(eqb (σ b) b2); intros.
      - left; now simpl_block_eqb.
      - left; now simpl_block_eqb.
      - right;left; split; simpl_block_eqb;
        rewrite <- H; now rewrite Hinvσ1.
      - right;right;split; try simpl_block_eqb.
        apply Bool.not_true_iff_false in H.
        contradict H.
        rewrite H, Hinvσ2.
        now simpl_block_eqb.
    }
    assert(Hwf1: forall (x : V.t) (b : Block.t), E C1 x = ⎣b⎦ -> M'1 ⊨ b).
    {
      intros x b H.
      case_eq(eqb b b1); intro Heq; try simpl_block_eqb.
      - eapply valid_after_alloc_same; rewrite <- Heq in *; eauto.
      - eapply (valid_after_alloc_other).
        * split; eauto. intro Hbb. now simpl_block_eqb.
        * eapply C1.(wf); eauto.
    }
    assert(Hwf2: forall (x : V.t) (b : Block.t), E C2 x = ⎣b⎦ -> M'2 ⊨ b).
    {
      intros x b H.
      case_eq(eqb b b2); intro Heq; try simpl_block_eqb.
      + eapply valid_after_alloc_same; rewrite <- Heq in *; eauto.
      + eapply (valid_after_alloc_other).
        * split; eauto. intro Hbb. now simpl_block_eqb.
        * eapply C2.(wf); eauto.
    }
    exists σ', Hσ', Hwf1, Hwf2.
    assert(HisoE: forall x b, E C1 x = ⎣ b ⎦ <-> E C2 x = ⎣ σ' b ⎦).
    {
      intros x b.
      destruct(Cases b) as [Case|[[Case1 Case2]|[Case1 Case2]]].
      - rewrite Case in *.
        split; intro HEC.
        + apply alloc_freshness in Halloc1.
          apply C1.(wf) in HEC. apply in_supp_valid in HEC.
          by_contradiction.
        + rewrite Hσ2 in HEC.
          apply C2.(wf) in HEC. apply in_supp_valid in HEC.
          apply alloc_freshness in Halloc2.
          by_contradiction.
      - split; intro HEC.
        + rewrite Case2 in HEC.
          apply Hiso.(iso_environment) in HEC.
          rewrite Hinvσ2 in HEC.
          apply C2.(wf) in HEC. apply in_supp_valid in HEC.
          apply alloc_freshness in Halloc2.
          by_contradiction.
        + rewrite Case2 in HEC.
          rewrite H'σ1 in HEC by auto.
          apply Hiso.(iso_environment) in HEC.
          apply C1.(wf) in HEC. apply in_supp_valid in HEC.
          apply alloc_freshness in Halloc1.
          by_contradiction.
      - rewrite H'σeq by auto.
        now apply Hiso.(iso_environment).
    }
    assert(Hv': forall b : Block.t, M'1 ⊨ b <-> M'2 ⊨ σ' b).
    { intros b; simpl. 
      destruct (Cases b) as [Case|[[Case1 Case2]|[Case1 Case2]]].
      + rewrite Case in *; split; intro Hv.
        * rewrite Hσ2.
          eapply valid_after_alloc_same; eauto.
        * eapply valid_after_alloc_same in Halloc1; eauto.
      + split; intro Hv.
        * rewrite Case2 in *.
          rewrite H'σ1 by auto.
          rewrite valid_after_alloc_other 
            with (M1:=M C1)(M2:=M'1)(b:=b1)(b':=inv_σ b2)
            in Hv by (split; eauto; simpl_block_eqb).
          apply Hiso.(iso_valid_block) in Hv.
          rewrite Hinvσ2 in Hv.
          apply in_supp_valid in Hv.
          apply alloc_freshness in Halloc2.
          by_contradiction.
        * assert(b2 <> σ b1)
            by (contradict Case1;clear Hσ2;subst;apply Hinvσ1).
          rewrite valid_after_alloc_other with (M1:=M C2)(M2:=M'2)
            in Hv by (split; eauto; now rewrite H'σ1).
          rewrite Hσ1 in Hv by now apply Hb2.
          apply Hiso.(iso_valid_block) in Hv.
          apply in_supp_valid in Hv.
          apply alloc_freshness in Halloc1.
          by_contradiction.
      + rewrite H'σeq by (split;auto).
        split; intro Hv.
        * rewrite valid_after_alloc_other in Hv; eauto.
          rewrite Hiso.(iso_valid_block) in Hv by auto.
          now rewrite valid_after_alloc_other
            by (split;eauto;contradict Case2; now apply Hb2).
        * rewrite valid_after_alloc_other; eauto.
          rewrite Hiso.(iso_valid_block) by auto.
          now rewrite valid_after_alloc_other
            in Hv
              by (split;eauto;contradict Case2; now apply Hb2).
    }
    assert(Hl':  forall b, M'1 ⊨ b -> length (M'1, b) = length (M'2, σ' b)).
    {
      intros b Hv.
      destruct (Cases b) as [Case|[[Case1 Case2]|[Case1 Case2]]].
      - rewrite Case in *. rewrite Hσ2.
        apply length_after_alloc_same in Halloc1.
        apply length_after_alloc_same in Halloc2.
        now rewrite Halloc1, Halloc2.
      - apply Hv' in Hv.
        rewrite Hσ1 in Hv by (apply Hb2; auto).
        assert(b2 <> σ b1)
          by (contradict Case1;clear Hσ2;subst;apply Hinvσ1).        
        rewrite valid_after_alloc_other 
          with (M1:=C2.(M))
          in Hv by (split; eauto).
        apply Hiso.(iso_valid_block) in Hv.
        apply in_supp_valid in Hv.
        apply alloc_freshness in Halloc1.
        by_contradiction.
      - rewrite H'σeq by (split;auto).
        rewrite length_after_alloc_other
          with (M1:=C1.(M))(n:=n)(b:=b1)
          by (split;auto).
        rewrite length_after_alloc_other
          with (M1:=C2.(M))(M2:=M'2)(n:=n)(b:=b2)
          by (split;auto;contradict Case2; apply Hb2; auto).
        now rewrite Hiso.(iso_length)
          by now rewrite <- valid_after_alloc_other
            with (M2:=M'1)(n:=n)(b:=b1) by auto.
    }
    assert(Hload: forall (κ : mtyp) (b : Block.t) (δ : Z) (v : value),
              load (κ, M'1, b, δ) = ⎣ v ⎦ <->
                load (κ, M'2, σ' b, δ) = ⎣ induced σ' Hσ' v ⎦).
    {
      intros κ b δ v.
      destruct (Cases b) as [Case|[[Case1 Case2]|[Case1 Case2]]].
      - rewrite Case, Hσ2.
        assert(Len1: length(M'1,b1) = Z.of_nat n)
          by (eapply length_after_alloc_same; eauto).
        assert(Len2: length(M'2,b2) = Z.of_nat n)
          by (eapply length_after_alloc_same; eauto).
        clear Hσ2.
        destruct(Z_le_dec 0 δ) as [Hge0|Hlt0];
          destruct(Z_le_dec (δ + sizeof κ) (Z.of_nat n)) as [Hgelen|Hltlen].
        + rewrite alloc_undef with (M1:=C1.(M))(b:=b1)(n:=n)
            by (repeat split; auto).
          rewrite alloc_undef with (M1:=C2.(M))(b:=b2)(n:=n)
            by (repeat split; auto).
          split; intro Hl.
          * inversion Hl; now subst.
          * destruct v as [n'|[b' δ']|]; simpl in Hl; now inversion Hl.
        + split; intro H; rewrite load_ϵ in H; try discriminate;
          contradict Hltlen; unfold valid_access in *; try rewrite Len1 in *;
            try rewrite Len2 in *; now repeat destruct_and_hyp.
        + split; intro H; rewrite load_ϵ in H; try discriminate;
            contradict Hlt0; unfold valid_access in *;
            now repeat destruct_and_hyp.
        + split; intro H; rewrite load_ϵ in H; try discriminate;
            contradict Hlt0; unfold valid_access in *;
            now repeat destruct_and_hyp.
      - assert(b2 <> σ b1)
          by (contradict Case1;clear Hσ2;subst;apply Hinvσ1).
        rewrite H'σ1 by auto.
        rewrite load_after_alloc with (M1:=C1.(M))(b:=b1)(n:=n)
          by (split;auto).
        rewrite load_after_alloc with (M1:=C2.(M))(M2:=M'2)(b:=b2)(n:=n)
          by (split;auto).
        split; intro Hl.
        + rewrite Case2 in Hl.
          rewrite Hiso.(iso_load) in Hl.
          rewrite load_ϵ in Hl. discriminate.
          intro HH. rewrite Hinvσ2 in HH.
          unfold valid_access in HH. destruct_and_hyp.
          apply alloc_freshness in Halloc2.
          apply in_supp_valid in HH0.
          by_contradiction.
        + assert(HH: C2.(M) ⊨ σ b1).
          {
            assert(HH: C2.(M) ⫢ κ @ σ b1,δ)
              by (rewrite  validaccess_load; now exists (induced σ' Hσ' v)).
            unfold valid_access in HH.
            now destruct_and_hyp.
          }
          apply Hiso.(iso_valid_block) in HH.
          apply in_supp_valid in HH.
          apply alloc_freshness in Halloc1.
          by_contradiction.
      - rewrite H'σeq by (split;auto).
        rewrite load_after_alloc with (M1:=C1.(M))(b:=b1)(n:=n)
          by (repeat split; auto).
        rewrite load_after_alloc with (M1:=C2.(M))(M2:=M'2)(b:=b2)(n:=n)
          by(repeat split; auto; contradict Case2; now apply Hb2).
        destruct v as [n'|[b' δ']|]; simpl in *; try apply Hiso.(iso_load).
        split; intro Hl.
        + assert(b' <> b1).
          {
            intro HH. clear Hσ2. subst.
            apply in_supp_loadable with (b:=b1) in Hl; auto.
            apply alloc_freshness in Halloc1.
            by_contradiction.
          }
          rewrite Hiso.(iso_load) in Hl.
          simpl in Hl.
          assert(b' <> inv_σ b2).
          {
            intro HH. clear Hσ2. subst.
            apply in_supp_loadable with (b:=b2) in Hl; auto.
            apply alloc_freshness in Halloc2.
            by_contradiction.
          }
          unfold σ'.
          now repeat simpl_block_eqb.
        + assert(b' <> b1).
          {
            intro HH. rewrite HH in *.
            apply in_supp_loadable with (b:=b2) in Hl; auto.
            apply alloc_freshness in Halloc2.
            by_contradiction.
          }
          set(HH:= Hiso.(iso_load)).
          specialize(HH κ b δ (Ptr(b', δ'))). simpl in HH.
          assert(b' <> inv_σ b2).
          {
            intro HHH. rewrite HHH in Hl. rewrite H'σ1 in Hl by trivial.
            set(HH':= Hiso.(iso_load)).
            specialize(HH' κ b δ (Ptr(b1, δ'))). simpl in HH'.
            apply HH' in Hl.
            apply in_supp_loadable with (b:=b1) in Hl; auto.
            apply alloc_freshness in Halloc1.
            by_contradiction.
            
          }
          rewrite H'σeq in Hl by (repeat split; auto).
          now rewrite <- HH in Hl.
    }
    do 2 split; auto.
  Qed.


  Lemma σ_eq:
    forall A (σ:A->A) b b',
      Bijective σ ->
      σ b = σ b' ->
      b = b'.
  Proof.
    intros A σ b b' Hbij Heq.
    destruct Hbij as [inv [H1 H2]].
    now rewrite <- H1, <- Heq, H1.
  Qed.

  Property isomorphic_free:
    forall C1 C2 b σ Hσ,
      isomorphic C1 C2 σ Hσ ->
      C1.(M) ⊨ b ->
      (forall x, C1.(E) x <> ⎣b⎦) ->
      exists M'1 M'2 Hwf1 Hwf2,
        free(C1.(M), b) = ⎣M'1⎦
        /\ free(C2.(M), σ b) = ⎣M'2⎦
        /\ isomorphic {|E:=C1.(E);M:=M'1;wf:=Hwf1|}
                     {|E:=C2.(E);M:=M'2;wf:=Hwf2|}
                     σ Hσ .
  Proof.
    intros C1 C2 b σ Hσ Hiso Hv1 Him.
    assert(Hv2: C2.(M) ⊨ σ b)
      by now apply Hiso.(iso_valid_block).
    assert(H'1: exists M'1, free(C1.(M), b) = ⎣M'1⎦)
      by now apply valid_implies_freeable.
    assert(H'2: exists M'2, free(C2.(M), σ b) = ⎣M'2⎦)
      by now apply valid_implies_freeable.
    destruct H'1 as [M'1 H'1].
    destruct H'2 as [M'2 H'2].
    set(Hσ_copy:=Hσ).
    destruct Hσ_copy as [inv_σ [Hσ1 Hσ2]].
    assert(Hwf1: forall x b, E C1 x = ⎣ b ⎦ -> M'1 ⊨ b).
    {
      intros x b' H.
      assert(b'<>b)
        by (intro H'; subst; specialize (Him x); by_contradiction).
      assert(M'1⊨ b')
        by(rewrite valid_after_free; eauto; eapply C1.(wf); eauto).
      trivial.
    }
    assert(Hwf2: forall x b, E C2 x = ⎣ b ⎦ -> M'2 ⊨ b).
    {
      intros x b' H.
      set(b'':= inv_σ b').
      assert(Hb'': b' = σ b'') by (unfold b''; now rewrite Hσ2).
      rewrite Hb'' in *.
      assert(b<>b'').
      {
        intro H'; specialize (Him x); clear Hb''; subst.
        rewrite <- Hiso.(iso_environment) in H.
        now contradict Him.
      }
      assert(M'2⊨ σ b'').
      {
        rewrite valid_after_free; eapply C2.(wf) in H;
          eauto; split; eauto.
        contradict H0.
        now apply σ_eq with (σ:=σ).
      }
      trivial.
    }
    exists M'1. exists M'2. exists Hwf1. exists Hwf2.
    do 2 (split; auto).
    constructor; simpl.
    - apply Hiso.(iso_environment).
    - intro b'.
      case_eq(eqb b' b); intro Hb'.
      + simpl_block_eqb.
        apply invalid_after_free in H'1.
        apply invalid_after_free in H'2.
        split; intros; by_contradiction.
      + assert(b'<>b) by now simpl_block_eqb.
        split; intro Hv.
        * rewrite valid_after_free in Hv; eauto.
          apply Hiso.(iso_valid_block) in Hv; auto.
          rewrite valid_after_free; try split; eauto.
          contradict H.
          now apply σ_eq with (σ:=σ).
        * rewrite valid_after_free in Hv; try split; eauto.
          apply Hiso.(iso_valid_block) in Hv; auto.
          rewrite valid_after_free; try split; eauto.
          contradict H.
          now apply σ_eq with (σ:=σ).
    - intros b' Hv.
      case_eq(eqb b' b); intro Hb'.
      + simpl_block_eqb.
        apply invalid_after_free in H'1.
        apply invalid_after_free in H'2.
        by_contradiction.
      + assert(b'<>b) by simpl_block_eqb.
        erewrite length_after_free; try split; eauto.
        erewrite length_after_free with (M2:=M'2); try split; eauto.
        apply Hiso.(iso_length).
        now rewrite valid_after_free in Hv by (try split; eauto).
        contradict H.
        now apply σ_eq with (σ:=σ).
    - intros κ b' δ v.
      case_eq(eqb b' b); intro Hb'.
      + simpl_block_eqb.
        apply invalid_after_free in H'1.
        apply invalid_after_free in H'2.
        split; intro Hl;
        rewrite load_ϵ in Hl; try discriminate; intro Hva;
          unfold valid_access in Hva; destruct_and_hyp;
          by_contradiction.
      + assert(H1: load (κ, M'1, b', δ) = load (κ, C1.(M), b', δ))
          by (eapply load_after_free; split; eauto; simpl_block_eqb).
        assert(H2: load (κ, M'2, σ b', δ) = load (κ, C2.(M), σ b', δ))
          by(eapply load_after_free; split; eauto;
             apply Bool.not_true_iff_false in Hb';
             contradict Hb'; apply eqb_eq;
             now apply σ_eq with (σ:=σ)).
        rewrite H2, H1.
        apply Hiso.(iso_load).
  Qed.

  Corollary store_ϵ:
    forall κ M b δ v,
      ~(M ⫢ κ @ b,δ) <-> store(κ, M, b, δ, v) = ϵ.
  Proof.
    intros κ M' b δ v; split; intro H.
    - case_eq(store(κ, M', b, δ, v)).
      + intros M'' Hst.
        contradict H.
        rewrite validaccess_store.
        eexists; eauto.
      + trivial.
    - intro H'. rewrite validaccess_store with (v:=v) in H'.
      destruct H' as [M2 Hst2].
      rewrite H in Hst2; discriminate.
  Qed.

  
  Property isomorphic_store:
    forall C1 C2 κ b δ v σ Hσ,
      isomorphic C1 C2 σ Hσ ->
      ( (exists M'1, store(κ, C1.(M), b, δ, v) = ⎣M'1⎦ ->
                (exists M'2 Hwf1 Hwf2,
                    ( store(κ, C2.(M), σ b, δ, induced σ Hσ v) = ⎣M'2⎦
                      /\ isomorphic {|E:=C1.(E);M:=M'1;wf:=Hwf1|}
                                   {|E:=C2.(E);M:=M'2;wf:=Hwf2|}
                                   σ Hσ)))
        /\ (store(κ, C1.(M), b, δ, v) = ϵ ->
           store(κ, C2.(M), σ b, δ, induced σ Hσ v) = ϵ) ).
  Proof.
    intros C1 C2 κ b δ v σ Hσ Hiso. 
    - case_eq(store (κ, M C1, b, δ, v)).
      + intros M'1 Hst1.
        split.
        * exists M'1. intro H; clear H.
          assert(Hva1: C1.(M) ⫢ κ @ b,δ)
            by (rewrite validaccess_store; eexists; eauto).
          assert(Hva2: C2.(M) ⫢ κ @ σ b,δ).
          {
            unfold valid_access in *.
            repeat destruct_and_hyp; repeat destruct_and_goal; auto.
            * now apply Hiso.(iso_valid_block).
            * now rewrite <- Hiso.(iso_length).
          }
          assert (Hwf1: forall x b', E C1 x = ⎣b'⎦ -> M'1 ⊨ b').
          {
            intros x b' HEC.
            assert(C1.(M)⊨ b') by (eapply C1.(wf); eauto).
            apply valid_after_store with (b':=b') in Hst1.
            now apply Hst1.
          }
          assert(H'2: exists M'2,  store (κ, M C2, σ b, δ, induced σ Hσ v) = ⎣ M'2 ⎦)
            by now apply validaccess_store.
          destruct H'2 as [M'2 Hst2].
          assert(Hwf2: forall x b', E C2 x = ⎣b'⎦ -> M'2 ⊨ b').
          {
            intros x b' HEC.
            assert(C2.(M)⊨ b') by (eapply C2.(wf); eauto).
            apply valid_after_store with (b':=b') in Hst2.
            now apply Hst2.
          }
          assert(Hlength: forall b0, M'1 ⊨ b0 ->
                           length (M'1, b0) = length (M'2, σ b0)).
          {
            simpl; intros b' Hv.
             rewrite length_after_store
               with (M2:=M'1)(M1:=C1.(M))(κ:=κ)(δ:=δ)(v:=v)(b:=b)
               by auto.
             rewrite length_after_store
               with (M2:=M'2)(M1:=C2.(M))(κ:=κ)(δ:=δ)(v:=induced σ Hσ v)(b:=σ b)
               by auto.
             apply Hiso.(iso_length).
             apply valid_after_store with (b':=b') in Hst1.
             now apply Hst1.
          }
          assert(Hvalid: forall b0 : B.t, M'1 ⊨ b0 <-> M'2 ⊨ σ b0).
          {
            intro b'.
            apply valid_after_store with (b':=σ b') in Hst2.
            apply valid_after_store with (b':=b') in Hst1.
            rewrite Hst2, Hst1.
            apply Hiso.(iso_valid_block).
          }

          exists M'2;exists Hwf1;exists Hwf2; split; eauto.
          constructor.
          -- apply Hiso.(iso_environment).
          -- auto.
          -- auto.
          -- intros κ' b' δ' v'; simpl.
             case_eq(B.eqb b b'); intro HB;
               case_eq((δ + sizeof κ <=? δ')%Z); intro Hδsb;
               case_eq((δ' + sizeof κ' <=? δ)%Z); intro Hδ'sb;
               try (assert(Hb': b'<>b) by now simpl_block_eqb);
               try simpl_block_eqb;
               try assert(Hδs: (δ + sizeof κ <= δ')%Z) by lia;
               try assert(Hδ's: (δ' + sizeof κ' <= δ)%Z) by lia;
               try assert(Hδs: (δ' < δ + sizeof κ)%Z) by lia;
               try assert(Hδ's: (δ < δ' + sizeof κ')%Z) by lia;
               try (erewrite load_after_store_other by (split;eauto);
                    erewrite load_after_store_other with (M2:=M'2) by (split;eauto);
                    now apply Hiso.(iso_load)).
             ++ destruct(Z.eq_dec δ δ') as [Heq | Hneq].
                ** subst.
                   destruct Hva1 as [Hv1 [H1 H'1]].
                   destruct Hva2 as [Hv2 [H2 H'2]].
                   case_eq(Mtyp.eqb κ κ'); intro Hκ.
                   --- simpl_mtyp_eqb.
                       erewrite load_after_store_same
                         by(repeat split; eauto;
                            erewrite length_after_store; eauto).
                       erewrite load_after_store_same
                         by(repeat split; eauto;
                            erewrite length_after_store; eauto).
                       case_eq(storable v κ'); intro Hstorable.
                       +++ rewrite convert_storable by eauto.
                           destruct v as [n1|[b1 δ1]|], v' as [n2|[b2 δ2]|]; simpl;
                             split; intro H; inversion H; subst;
                             repeat rewrite convert_storable in * by eauto;
                             trivial; inversion H3; subst.
                           assert(b1 = b2) by (eapply σ_eq; eauto).
                           now subst.
                       +++ rewrite convert_not_storable_undef by eauto.
                           destruct v as [n1|[b1 δ1]|], v' as [n2|[b2 δ2]|]; simpl;
                             split; intro H; inversion H; subst;
                             repeat rewrite convert_not_storable_undef in *
                               by eauto; trivial; inversion H3; subst.
                   --- assert(Hκdiff: κ<>κ') by simpl_mtyp_eqb.
                       split; intro H.
                       +++ assert(HH: M'1 ⫢ κ' @ b', δ')
                             by (erewrite validaccess_load;eexists;eauto).
                           destruct HH as [HHv [HH1 HH'1]].
                           erewrite load_after_store_same with (M2:=M'1) in H
                               by (repeat split; eauto).
                           rewrite convert_different_mtyp_undef in H by auto.
                           inversion H; subst. simpl.
                           erewrite load_after_store_same with (M2:=M'2)
                             by (repeat split; eauto; now rewrite <- Hlength).
                           rewrite convert_different_mtyp_undef;
                             repeat split; eauto.
                       +++ assert(HH: M'2 ⫢ κ' @ σ b', δ')
                             by (erewrite validaccess_load;eexists;eauto).
                           destruct HH as [HHv2 [HH2 HH'2]].
                           erewrite load_after_store_same with (M2:=M'2) in H
                               by (repeat split; eauto).
                           erewrite load_after_store_same with (M2:=M'1)
                             by (repeat split; eauto; rewrite Hlength; auto;
                                 now rewrite Hvalid).
                           rewrite convert_different_mtyp_undef in H;
                             repeat split; eauto.
                           destruct v' as [n1|[b1 δ1]|]; simpl in H;
                             try discriminate.
                           now rewrite convert_different_mtyp_undef.
                ** split; intro H.
                   --- assert(HH: M'1 ⫢ κ' @ b', δ')
                         by (erewrite validaccess_load;eexists;eauto).
                       destruct HH as [HHv [HH1 HH'1]].
                       erewrite load_after_store_overlap in H; repeat split; eauto.
                       erewrite load_after_store_overlap
                         by (repeat split; eauto; now rewrite <- Hlength; auto).
                       inversion H; now subst.
                   --- assert(HH: M'2 ⫢ κ' @ σ b', δ')
                         by (erewrite validaccess_load;eexists;eauto).
                       destruct HH as [HHv2 [HH2 HH'2]].
                       erewrite load_after_store_overlap in H; repeat split; eauto.
                       erewrite load_after_store_overlap
                         by (repeat split; eauto; rewrite Hlength; auto;
                             rewrite Hvalid;auto).
                       destruct v' as [n1|[b1 δ1]|]; trivial; discriminate.
             ++ erewrite load_after_store_other by (split;eauto).
                erewrite load_after_store_other with (M2:=M'2)
                  by(repeat split; eauto; left;
                     contradict Hb'; eapply σ_eq; eauto).
                apply Hiso.(iso_load).
        * intros; discriminate.
      + split.
        * exists empty. intro. discriminate.
        * intros _.
          apply store_ϵ in H.
          assert(~ (M C2 ⫢ κ @ σ b, δ)).
          {
            contradict H.
            unfold valid_access in *.
            destruct H as [H1 [H2 H3]].
            split;[idtac|split].
            - now apply Hiso.(iso_valid_block).
            - trivial.
            - now rewrite Hiso.(iso_length)
                by now apply Hiso.(iso_valid_block).
          }
          now apply store_ϵ.
  Qed.

  Definition subcontext C1 C2 :=
    (forall x b, C1.(E) x = ⎣b⎦ -> C2.(E) x = ⎣b⎦)
    /\(forall b, C1.(M) ⊨ b -> C2.(M) ⊨ b)
    /\(forall b, C1.(M) ⊨ b -> length(C1.(M),b)=length(C2.(M), b))
    /\(forall κ b δ v, load(κ, C1.(M), b, δ) = ⎣v⎦ ->
                 load(κ, C2.(M), b, δ) = ⎣v⎦).

  Notation "C1 '⊆' C2":=(subcontext C1 C2)(at level 70).

  Property validaccess_subcontext:
    forall C1 C2 κ b δ, C1 ⊆ C2 -> C1.(M) ⫢ κ @ b,δ -> C2.(M) ⫢ κ @ b,δ.
  Proof.
    intros C1 C2 κ b δ Hsub Hva.
    destruct Hsub as [Hsub1 [Hsub2 [Hsub3 Hsub4]]].
    destruct Hva as [Hv [H1 H2]].
    repeat split; auto.
    now rewrite <- Hsub3 by auto.
  Qed.
  
End Context.

Module Type SIG(V:DecidableType)(B:Eqb.EQB)(EMM: ExecutionMemoryModel B).
  Include Context.Context V B EMM.
End SIG.
