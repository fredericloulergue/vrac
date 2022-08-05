Require Import Arith ZArith Lia List Structures.Equalities Logic.FinFun.

From Vrac.Lib Require Import Option Tactics Eqb.
From Vrac.Memory Require Import MemoryType
  ExecutionMemoryModel ObservationMemoryModel Context.

Module Representation(V : DecidableType)(B: Eqb.EQB)
  (Import EMM: ExecutionMemoryModel B)
  (Import OMM: ObservationMemoryModel B)
  (Import Ctx: Context.SIG V B EMM).

  Class represents (Me: mem) (Mo : obs) := {
      repr_valid: forall b, Me ⊨ b <-> is_valid(Mo, b) = true;
      repr_length: forall b, Me ⊨ b -> EMM.length(Me, b) = length(Mo, b);
      repr_isinit:
      forall κ b δ, Me ⫢ κ @ b,δ -> (exists v, v<>Undef /\ load(κ,Me,b,δ) = ⎣v⎦)
                              <-> is_initialized(κ, Mo, b, δ) = true
    }.

  Notation "Me '▷' Mo" :=(represents Me Mo)(at level 70).

  Property presentation_access_validity:
    forall Me Mo, Me ▷ Mo ->
             (forall κ b δ, Me ⫢ κ @ b, δ <-> is_valid_access Mo κ b δ = true).
  Proof.
    intros Me Mo R κ b δ. split; intro Hva.
    - destruct Hva as [Hv [H1 H2]].
      unfold is_valid_access.
      repeat destruct_and_goal.
      + now apply R.(repr_valid).
      + lia.
      + rewrite <- R.(repr_length) by trivial.
        lia.
    - unfold is_valid_access in Hva.
      repeat destruct_and_hyp.
      repeat split.
      + now apply R.(repr_valid).
      + lia.
      + rewrite R.(repr_length) by now apply R.(repr_valid).
        lia.
  Qed.

  Property representation_alloc:
    forall Me Mo, Me ▷ Mo ->
             forall n b Me2, alloc(Me, n) = (b, Me2) ->
                        Me2 ▷ store_block(Mo, b, n).
  Proof.
    intros Me Mo R n b Me2 Halloc.
    constructor.
    - intros b0. case_eq(B.eqb b0 b); intro Hb0.
      + simpl_block_eqb.
        apply valid_after_alloc_same in Halloc.
        assert(is_valid (store_block (Mo, b, n), b) = true)
          by (eapply storeblock_validblock_same; eauto).
        split; auto.
      + split; intro Hv.
        * assert(b0<>b) by now simpl_block_eqb.
          rewrite valid_after_alloc_other in Hv; eauto.
          erewrite storeblock_validblock_other; eauto.
          now apply R.(repr_valid).
        * unfold is_valid_access in Hv; repeat destruct_and_hyp.
          erewrite storeblock_validblock_other in Hv
              by(try split; eauto; try simpl_block_eqb).
          rewrite valid_after_alloc_other
            by(try split; eauto; try simpl_block_eqb).
          now apply R.(repr_valid).
    - intros b0 Hv. case_eq(B.eqb b0 b); intro Hb0.
      + simpl_block_eqb.
        erewrite length_after_alloc_same by eauto.
        now erewrite storeblock_length_same by eauto.
      + assert(b0<>b) by now simpl_block_eqb.
        erewrite length_after_alloc_other by eauto.
        erewrite storeblock_length_other by eauto.
        apply R.(repr_length).
        now rewrite <- valid_after_alloc_other
          by (try split; eauto; try simpl_block_eqb).
    - intros κ b0 δ Hva; split; intro Hinit;
        case_eq(B.eqb b0 b); intro Hb0.
      + simpl_block_eqb.
        destruct Hva as [Hv [H1 H2]].
        assert(load (κ, Me2, b, δ) = ⎣Undef⎦)
          by (eapply alloc_undef; repeat split; eauto;
              now erewrite <- length_after_alloc_same by eauto).
        destruct Hinit as [v [Hvalue Hload]].
        assert(v = Undef) by (rewrite Hload in H; now inversion H).
        by_contradiction.
      + assert(b0<>b) by now simpl_block_eqb.
        destruct Hinit as [v [Hvalue Hload]].
        erewrite storeblock_isinit_other by eauto.
        erewrite load_after_alloc in Hload by eauto.
        apply R.(repr_isinit); try apply validaccess_load; eexists; eauto.
      + simpl_block_eqb.
        now erewrite storeblock_isinit_same in Hinit by eauto.
      + assert(b0<>b) by now simpl_block_eqb.
        assert(Hva': Me ⫢ κ @ b0, δ)
          by (rewrite valid_access_after_alloc; eauto).
          destruct Hva as [Hv [H1 H2]].
        erewrite length_after_alloc_other in H2 by eauto.
        erewrite storeblock_isinit_other in Hinit by eauto.
        erewrite load_after_alloc by eauto.
        apply R.(repr_isinit) in Hinit; trivial.
  Qed. 

  Property representation_free:
    forall Me1 Mo, Me1 ▷ Mo ->
              forall b Me2, free(Me1, b) = ⎣Me2⎦ ->
                       Me2 ▷ delete_block(Mo, b).
  Proof.
    intros Me1 Mo R b Me2 Hfree.
    constructor.
    - intros b0; case_eq(B.eqb b0 b); intro Hb0.
      + simpl_block_eqb.
        apply invalid_after_free in Hfree.
        erewrite deleteblock_validblock_same by eauto.
        split; intro H; now auto.
      + assert(Hdiff: b0<>b) by now simpl_block_eqb.
        split; intro Hv.
        * erewrite deleteblock_validblock_other by eauto.
          apply R.(repr_valid).
          now rewrite <- valid_after_free by (eauto; split; eauto).
        * rewrite valid_after_free by (eauto; split; eauto).
          erewrite deleteblock_validblock_other in Hv by eauto.
          now apply R.(repr_valid).
    - intros b0 Hv; case_eq(B.eqb b0 b); intro Hb0.
      + simpl_block_eqb.
        apply invalid_after_free in Hfree.
        by_contradiction.
      + assert(Hdiff: b0<>b) by now simpl_block_eqb.
        erewrite length_after_free by eauto.
        erewrite deleteblock_length_other_ by eauto.
        apply R.(repr_length).
        now rewrite <- valid_after_free by (eauto; split; eauto).
    - intros κ b0 δ Hva2; case_eq(B.eqb b0 b); intro Hb0.
      + simpl_block_eqb.
        apply invalid_after_free in Hfree.
        destruct Hva2 as [Hv2 _].
        by_contradiction.
      + assert(Hdiff: b0<>b) by now simpl_block_eqb.
        assert(Hva1: Me1 ⫢ κ @ b0, δ)
          by (rewrite valid_access_after_free; eauto).
        split; intro Hv.
        * erewrite deleteblock_isinit_other by eauto.
          erewrite load_after_free in Hv by eauto.
          destruct Hva2 as [Hv2 [H1 H2]].
          erewrite length_after_free in H2 by eauto.
          apply R.(repr_isinit); auto.
        * erewrite deleteblock_isinit_other in Hv by eauto.
          erewrite load_after_free by eauto.
          destruct Hva2 as [Hv2 [H1 H2]].
          erewrite length_after_free in H2 by eauto.
          apply R.(repr_isinit); auto.
  Qed.
  
  Property representation_store:
    forall Me1 Mo, Me1 ▷ Mo ->
              forall κ b δ v Me2, v<>Undef -> storable v κ = true ->
                             store(κ,Me1,b,δ,v) = ⎣Me2⎦ ->
                             Me2 ▷ initialize(κ, Mo, b, δ).
  Proof.
    intros Me1 Mo R κ b δ v Me2 Hdef Hstorable Hst.
    constructor.
    - intros b'.
      rewrite valid_after_store by eauto.
      erewrite initialize_validblock by eauto.
      now apply R.(repr_valid).
    - intros b' Hv.
      erewrite length_after_store by eauto.
      erewrite initialize_length by eauto.
      rewrite valid_after_store in Hv by eauto.
      now apply R.(repr_length).
    - intros κ' b' δ' Hva2.
      assert(Hva1: Me1 ⫢ κ' @ b', δ')
        by(rewrite valid_access_after_store; eauto).
      case_eq(B.eqb b b'); intro HB;
        case_eq((δ + sizeof κ <=? δ')%Z); intro Hδsb;
        case_eq((δ' + sizeof κ' <=? δ)%Z); intro Hδ'sb;
        try (assert(Hb': b'<>b) by now simpl_block_eqb);
        try simpl_block_eqb;
        try assert(Hδs: (δ + sizeof κ <= δ')%Z) by lia;
        try assert(Hδ's: (δ' + sizeof κ' <= δ)%Z) by lia;
        try assert(Hδs: (δ' < δ + sizeof κ)%Z) by lia;
        try assert(Hδ's: (δ < δ' + sizeof κ')%Z) by lia;
        try (erewrite load_after_store_other by eauto;
             erewrite initialize_isinit_other by eauto;
             now apply R.(repr_isinit)).
      destruct(Z.eq_dec δ δ').
      + subst.
        destruct Hva1 as [Hv1 [H1 H'1]].
        destruct Hva2 as [Hv2 [H2 H'2]].
        erewrite load_after_store_same 
          by (repeat split; eauto; try lia).
        split; intro H.
        * destruct H as [v0 [Hdef_v0 Hv0]].
          assert(κ = κ').
          {
            case_eq(Mtyp.eqb κ κ'); intro Heqb.
            now simpl_mtyp_eqb.
            rewrite convert_different_mtyp_undef in Hv0 by simpl_mtyp_eqb.
            inversion Hv0. by_contradiction.
          }
          subst.
          now erewrite initialize_isinit_same by eauto.
        * case_eq(Mtyp.eqb κ κ'); intro Hκ.
          -- simpl_mtyp_eqb.
             rewrite convert_storable by auto.
             eexists; eauto.
          -- erewrite initialize_isinit_overlap in H.
             discriminate.
             repeat split; eauto.
             left; repeat split; eauto; simpl_mtyp_eqb.
             erewrite initialize_length by eauto.
             now rewrite <- R.(repr_length).
      + destruct Hva1 as [Hv1 [H1 H'1]].
        destruct Hva2 as [Hv2 [H2 H'2]].
        erewrite load_after_store_overlap by(repeat split; eauto).
        split; intro H.
        * destruct H as [v0 [Hdef_v0 Hv0]].
          inversion Hv0.
          by_contradiction.
        * erewrite initialize_isinit_overlap in H.
          discriminate.
          repeat split; eauto.
          erewrite initialize_length by eauto.
          now rewrite <- R.(repr_length).
  Qed.

  Property representation_empty:
    EMM.empty ▷ OMM.empty.
  Proof.
    constructor.
    - intros b; split; intro H.
      + now apply empty_not_valid in H.
      + now rewrite empty_isvalid in H.
    - intros b; intro H.
      now apply empty_not_valid in H.
    - intros κ b δ [H [H1 H2]].
      now apply empty_not_valid in H.
  Qed.
  
End Representation.
        
        
      



      
               

         
