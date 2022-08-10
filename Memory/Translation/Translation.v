Require Import ZArith Structures.Equalities List Lia.
Import ListNotations.

From Vrac.Lib Require Import Error Option Tactics Maximum.
From Vrac.Memory Require Import MemoryType.
From Vrac.Common Require Import Syntax.
From Vrac.Source Require Import Syntax.
From Vrac.Target Require Import Syntax.

Module Type Countable (V : DecidableType).
  Parameter t2nat: V.t -> nat.
  Parameter nat2t: nat -> V.t.
  Axiom nat2t2nat: forall n, t2nat(nat2t n) = n.
  Axiom t2nat2t: forall t, nat2t(t2nat t) = t.
End Countable.

Module Type DecCountable := DecidableType <+ Countable.

Module Fresh(Import V : DecCountable).

  Lemma t2nat_injective:
    forall t1 t2, t2nat t1 = t2nat t2 -> t1 = t2.
  Proof.
    intros t1 t2 H.
    replace t1 with (nat2t(t2nat t1)) by apply t2nat2t.
    replace t2 with (nat2t(t2nat t2)) by apply t2nat2t.
    now rewrite H.
  Qed.

  Lemma nat2t_injective:
    forall n1 n2, nat2t n1 = nat2t n2 -> n1 = n2.
  Proof.
    intros n1 n2 H.
    replace n1 with (t2nat(nat2t n1)) by apply nat2t2nat.
    replace n2 with (t2nat(nat2t n2)) by apply nat2t2nat.
    now rewrite H.
  Qed.
  
  Definition fresh (init: list t) : V.t :=
    nat2t(S (maximum (List.map t2nat init))).

  Lemma fresh_is_fresh:
    forall init, not(In (fresh init) init).
  Proof.
    intros init. unfold fresh.
    assert(HnotIn: not(In (S(maximum(map t2nat init)))(map t2nat init)))
      by apply S_maximum_not_in.
    contradict HnotIn.
    apply in_map with (f:=t2nat) in HnotIn.
    now rewrite nat2t2nat in HnotIn.
  Qed.

  Definition res init n :=
    nat2t(S(maximum(map t2nat init))+n).

  Lemma res_is_fresh :
    forall init n, not(In (res init n) init).
  Proof.
    intros init n H. unfold res in H.
    apply in_map with (f:=t2nat) in H.
    rewrite nat2t2nat in H.
    apply in_map_iff in H.
    destruct H as [v [H1 H2]].
    assert(H: In (t2nat v) (map t2nat init)) by (eapply in_map in H2; eauto).
    assert(H': t2nat v <= maximum (map t2nat init)) by now apply maximum_lt.
    lia.
  Qed.
    
  Lemma res_injective: forall init n1 n2,
      res init n1 = res init n2 -> n1 = n2.
  Proof.
    unfold res.
    intros init n1 n2 H.
    apply nat2t_injective in H.
    lia.
  Qed.
      
End Fresh.

Module Translation (V : DecCountable)
  (Import CStx: Common.Syntax.SIG V)
  (Import SStx: Source.Syntax.SIG V CStx)
  (Import TStx: Target.Syntax.SIG V CStx).
 
End Translation.

Module Type SIG (V : DecCountable)
  (Import CStx: Common.Syntax.SIG V)
  (Import SStx: Source.Syntax.SIG V CStx)
  (Import TStx: Target.Syntax.SIG V CStx).
  
  Include Translation V CStx SStx TStx.

End SIG.
