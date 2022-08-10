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

Module Fresh.

  Module Make (Import V : DecCountable).

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

  End Make.

  Module Type SIG(V: DecCountable).
    Include Make V.
  End SIG.
    
End Fresh.

Module Translation (V : DecCountable)
  (Import CStx: Common.Syntax.SIG V)
  (Import SStx: Source.Syntax.SIG V CStx)
  (Import TStx: Target.Syntax.SIG V CStx)
  (Import F: Fresh.SIG V).

  Import CStx.Expr SStx.Term SStx.Stmt TStx.Stmt.

  Notation stmt := SStx.Stmt.stmt.
  Notation stmt' := TStx.Stmt.stmt.

  
  Fixpoint t_trans (t: term)(vars: list V.t)(n: nat): stmt' :=
    match t with
    | TExpr e τ => SAssign (EVar (res vars n) τ) e
    | TDeref t1 τ =>
        let tmp := res vars (n+1) in
        let E_tmp := EVar tmp (Term.typeof t1) in
        SLet tmp (typeof t1)
          (SSeq
             (t_trans t1 vars (n+1))
             (SAssign
                (EVar (res vars n) τ)
                (EDeref E_tmp τ)))
    | TUnop op t1 τ1 =>
        let tmp := res vars (n+1) in
        let E_tmp := EVar tmp (Term.typeof t1) in
        SLet tmp (typeof t1)
          (SSeq
             (t_trans t1 vars (n+1))
             (SAssign
                (EVar (res vars n) τ1)
                (EUnop op E_tmp τ1)))
    | TBinop op t1 t2 τ =>
        let tmp1 := res vars (n+1) in
        let E_tmp1 := EVar tmp1 (Term.typeof t1) in
        let tmp2 := res vars (n+2) in
        let E_tmp2 := EVar tmp2 (Term.typeof t2) in
        SLet tmp1 (typeof t1)
          (SLet tmp2 (typeof t2)
             (SSeq
                (t_trans t1 vars (n+1))
                (SSeq
                   (t_trans t2 vars (n+2))
                   (SAssign
                      (EVar (res vars n) τ)
                      (EBinop op E_tmp1 E_tmp2 τ)))))
    | TBaseaddress t1 τ =>
        let tmp := res vars (n+1) in
        let E_tmp := EVar tmp (Term.typeof t1) in
        SLet tmp (typeof t1)
          (SSeq
             (t_trans t1 vars (n+1))
             (SBaseaddress
                (EVar (res vars n) τ)
                E_tmp))
    | TOffset t1 τ =>
        let tmp := res vars (n+1) in
        let E_tmp := EVar tmp (Term.typeof t1) in
        SLet tmp (typeof t1)
          (SSeq
             (t_trans t1 vars (n+1))
             (SOffset
                (EVar (res vars n) τ)
                E_tmp))
    | TBlocklength t1 τ =>
                let tmp := res vars (n+1) in
        let E_tmp := EVar tmp (Term.typeof t1) in
        SLet tmp (typeof t1)
          (SSeq
             (t_trans t1 vars (n+1))
             (SBlocklength
                (EVar (res vars n) τ)
                E_tmp))
    end.
 
End Translation.

Module Type SIG (V : DecCountable)
  (Import CStx: Common.Syntax.SIG V)
  (Import SStx: Source.Syntax.SIG V CStx)
  (Import TStx: Target.Syntax.SIG V CStx)
  (Import F: Fresh.SIG V).
  
  Include Translation V CStx SStx TStx F.

End SIG.
