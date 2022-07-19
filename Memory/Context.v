Require Import Arith ZArith Lia List Structures.Equalities Logic.FinFun.
Require Import Vrac.Tactics Vrac.Option Vrac.Eqb
  Vrac.MemoryType Vrac.ExecutionMemoryModel.


Module Context(V : DecidableType)(Import EMM: ExecutionMemoryModel).

  Module EMM'. Include EMM. Definition t := block. End EMM'.
  
  Module Block := Full EMM'.
  Import Block.

  Ltac simpl_block_eqb :=
    simpl_generic_eqb eqb Block.eqb_refl Block.eqb_sym
      Block.eqb_eq Block.eqb_neq.
  
  Definition environment := V.t -> option block.
  
  Record context := {
      E: environment;
      M: mem;
      wf: forall x b, E x = ⎣b⎦ -> M ⊨ b
    }.

  Definition induced (σ: block -> block) (Hσ: Bijective σ) :=
    fun value => match value with
              | Int n => Int n
              | Undef => Undef
              | Ptr(b, δ) => Ptr(σ(b), δ)
              end.

  (*
    Lemma induced_PI :
    forall (σ: block->block)(H1 H2: Bijective σ),
    forall value, induced σ H1 value = induced σ H2 value.
  Admitted.
   *)

  Class isomorphic (C1 C2: context)(σ: block -> block)(Hσ: Bijective σ) :=
    {
      iso_environment: forall x b, C1.(E) x = ⎣b⎦ <-> C2.(E) x = ⎣σ b⎦;
      iso_valid_block: forall b, C1.(M) ⊨ b <-> C2.(M) ⊨ σ(b);
      iso_length: forall b, C1.(M) ⊨ b -> length(C1.(M), b) = length(C2.(M), σ(b));
      iso_load: forall κ b δ v, load(κ, C1.(M), b, δ) = ⎣v⎦ <->
                             load(κ, C2.(M), σ b, δ) = ⎣(induced σ Hσ) v⎦
    }.

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
    - intros b Hvb.
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
          destruct v; auto; simpl; destruct p. subst.
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
    assert(Hσ'2: forall b : block, σ' (inv_σ' b) = b).
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
    assert(Hwf1: forall (x : V.t) (b : block), E C1 x = ⎣b⎦ -> M'1 ⊨ b).
    {
      intros x b H.
      case_eq(eqb b b1); intro Heq; try simpl_block_eqb.
      + eapply valid_after_alloc_same; eauto.
      + eapply (valid_after_alloc_other).
        * split; eauto. intro Hbb. now simpl_block_eqb.
        * eapply C1.(wf); eauto.
    }
    assert(Hwf2: forall (x : V.t) (b : block), E C2 x = ⎣b⎦ -> M'2 ⊨ b).
    {
      intros x b H.
      case_eq(eqb b b2); intro Heq; try simpl_block_eqb.
      + eapply valid_after_alloc_same; eauto.
      + eapply (valid_after_alloc_other).
        * split; eauto. intro Hbb. now simpl_block_eqb.
        * eapply C2.(wf); eauto.
    }
    exists σ', Hσ', Hwf1, Hwf2.
    assert(HisoE: forall x b, E C1 x = ⎣ b ⎦ <-> E C2 x = ⎣ σ' b ⎦).
    {
      intros x b; split; intro HEC.
      - unfold σ'.
        simpl_if; try simpl_block_eqb.
        + apply alloc_freshness in Halloc1.
          apply C1.(wf) in HEC.
          apply in_supp_valid in HEC.
          now by_contradiction.
        + simpl_if; try simpl_block_eqb.
          * apply Hiso.(iso_environment) in HEC.
            rewrite Hinvσ2 in HEC.
            apply alloc_freshness in Halloc2.
            apply C2.(wf) in HEC.
            apply in_supp_valid in HEC.
            now by_contradiction.
          * now apply Hiso.(iso_environment).
      - unfold σ' in HEC.
        simpl_if; try simpl_block_eqb.
        + apply alloc_freshness in Halloc2.
          apply C2.(wf) in HEC.
          apply in_supp_valid in HEC.
          now by_contradiction.
        + simpl_if; try simpl_block_eqb.
          * apply Hiso.(iso_environment) in HEC.
            apply alloc_freshness in Halloc1.
            apply C1.(wf) in HEC.
            apply in_supp_valid in HEC.
            now by_contradiction.
          * now apply Hiso.(iso_environment).      
    }
    split; [ constructor | repeat split ].
    - auto.
    - intros b; simpl; split; intro H.
      + case_eq(eqb b b1); intro Hb; unfold σ'.
        * repeat simpl_block_eqb.
          eapply valid_after_alloc_same; eauto.
        * rewrite Hb.
          simpl_if.
          -- simpl_block_eqb.
             assert(b2 <> σ b1) by (apply eqb_neq in Hb;contradict Hb;
                                   subst;apply Hinvσ1).
             rewrite valid_after_alloc_other 
               with (M1:=M C1)(M2:=M'1)(b:=b1)(b':=inv_σ b2)
               in H by (split; eauto; simpl_block_eqb).
             apply Hiso.(iso_valid_block) in H.
             rewrite Hinvσ2 in H.
             apply alloc_freshness in Halloc2.
             apply in_supp_valid in H.
             by_contradiction.
          -- eapply valid_after_alloc_other.
             ++ split; eauto; intro Heq.
                assert(Heq': b = inv_σ b2) by now rewrite Heq, Hinvσ1.
                subst. rewrite Hinvσ1 in H0.
                now simpl_block_eqb.
             ++ apply Hiso.(iso_valid_block).
                assert(b <> b1) by now simpl_block_eqb.
                now rewrite <- valid_after_alloc_other
                  with (M1:=M C1)(M2:=M'1)(b':=b);
                  try split; eauto.
      + case_eq(eqb b b1); intro Hb; unfold σ' in *.
        * repeat simpl_block_eqb.
          eapply valid_after_alloc_same; eauto.
        * rewrite Hb in H; simpl_if.
          -- simpl_block_eqb.
             assert(b2 <> σ b1) by (apply eqb_neq in Hb;contradict Hb;
                                   subst;apply Hinvσ1).
             rewrite valid_after_alloc_other 
               with (M1:=M C2)(M2:=M'2)(b:=b2)(b':=σ b1)
               in H by (split; eauto; simpl_block_eqb).
             apply Hiso.(iso_valid_block) in H.
             apply alloc_freshness in Halloc1.
             apply in_supp_valid in H.
             by_contradiction.
          -- eapply valid_after_alloc_other.
             ++ split; eauto; intro Heq.
                simpl_block_eqb.
                by_contradiction.
             ++ apply Hiso.(iso_valid_block).
                assert(σ b <> b2) by (apply eqb_neq in H0;contradict H0;
                                     subst;now rewrite Hinvσ1).
                rewrite valid_after_alloc_other
                  with (M1:=M C2)(M2:=M'2)
                  in H;try split; eauto.
    - intros b H. simpl.
      admit.
    - intros κ b δ v.
      admit.
    - intros b H.
      destruct H; unfold σ'; repeat simpl_if; simpl_block_eqb.
      + by_contradiction.
      + rewrite Hinvσ2 in H0. by_contradiction.
      + trivial.
    - unfold σ'; repeat simpl_if; auto; now simpl_block_eqb.
    - intros b H.
      unfold σ'; repeat simpl_if; auto.
      + now simpl_block_eqb.
      + assert(b = inv_σ b2) by (rewrite <- H; now rewrite Hinvσ1).
        simpl_block_eqb.
        by_contradiction.
  Admitted.
  
End Context.
