Require Import Arith ZArith Lia List Structures.Equalities Logic.FinFun.
Require Import Vrac.Tactics Vrac.Option Vrac.Eqb Vrac.MemoryType
  Vrac.ExecutionMemoryModel Vrac.ObservationMemoryModel
  Vrac.Context.

Module Representation(V : DecidableType)(B: Eqb.EQB)
  (Import EMM: ExecutionMemoryModel B)
  (Import OMM: ObservationMemoryModel B)
  (Import Ctx: Context.CONTEXT V B EMM).

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
        destruct Hva as [Hv [H1 H2]].
        erewrite length_after_alloc_other in H2 by eauto.
        erewrite storeblock_isinit_other in Hinit by eauto.
        erewrite load_after_alloc by eauto.
        apply R.(repr_isinit) in Hinit; trivial.
        repeat split; auto.
        now erewrite <- valid_after_alloc_other by eauto.
  Qed. 

End Representation.
        
        
      



      
               

         
