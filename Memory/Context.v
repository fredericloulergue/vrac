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
                        then b2
                        else if (eqb b (σ b1))
                             then inv_σ b2
                             else inv_σ b).
  Admitted.
  
End Context.
