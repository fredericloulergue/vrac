Require Import Arith ZArith Lia List Structures.Equalities.

From Vrac.Lib Require Import Tactics Option Eqb Error.
From Vrac.Memory Require Import MemoryType ExecutionMemoryModel Context.
From Vrac.Common Require Import Syntax Semantics.
From Vrac.Target Require Import Syntax.

Module Semantics(V : DecidableType)(B: Eqb.EQB)
  (Import EMM: ExecutionMemoryModel B)
  (Import Ctx: Context.SIG V B EMM)
  (Import CStx: Common.Syntax.SIG V)
  (Import Stx: Target.Syntax.SIG V CStx)
  (CSem: Common.Semantics.SIG V B EMM Ctx CStx).

  Import CStx.Types CStx.Expr Stx.Stmt CSem.
  
  (* TODO: explanation wrt. to the companion paper. *)
  Inductive sseval : forall (C: context) (Γ: type_env) (s: stmt) (M2: mem)
                      (Invariant: forall x b, C.(E) x = ⎣b⎦ -> M2 ⊨ b), Prop :=
    
  | S_skip: forall C Γ,
      sseval C Γ SSkip C.(M) C.(wf)
                                             
  | S_assign: forall C Γ e1 e2 τ v b δ M2
      (Hstore: store(mtype τ, C.(M), b, δ, v) = ⎣M2⎦),
      Expr.check_type Γ e1 = Ok τ ->
      Expr.check_type Γ e2 = Ok τ ->
      eeval C Γ e2 v ->
      lveval C Γ e2 (b,δ) ->
      sseval C Γ (SAssign e1 e2) M2 (wf_after_store Hstore)

  | S_malloc: forall C Γ e1 e2 τ n b δ b' M2 M3
                (Halloc: alloc(C.(M), Z.to_nat n) = (b', M2))
                (Hstore: store(mtype (TPtr τ), M2, b, δ, Ptr(b',0%Z)) = ⎣M3⎦),
      Expr.check_type Γ e1 = Ok (TPtr τ) ->
      eeval C Γ e2 (Int n) ->
      lveval C Γ e1 (b,δ) ->
      sseval C Γ (SMalloc e1 e2) M3 (wf_after_malloc Halloc Hstore)

  | S_free: forall C Γ e b M2
              (Hfree: free(C.(M), b) = ⎣M2⎦)
              (Him: forall x, C.(E) x <> ⎣b⎦),
      eeval C Γ e (Ptr(b, 0%Z)) ->
      sseval C Γ (SFree e) M2 (wf_after_free Hfree Him)
                                             
  | S_seq: forall C Γ s1 s2 M2 Wf2 M3 Wf3,
      sseval C Γ s1 M2 Wf2 ->
      sseval {|E:=C.(E);M:=M2;inj:=C.(inj);wf:=Wf2|} Γ s2 M3 Wf3 ->
      sseval C Γ (SSeq s1 s2) M3 Wf3

  | S_if_false: forall C Γ e s1 s2 M2 Wf2,
      eeval C Γ e (Int 0%Z) ->
      sseval C Γ s2 M2 Wf2 ->
      sseval C Γ (SIf e s1 s2) M2 Wf2

  | S_if_true: forall C Γ e s1 s2 M1 Wf1 n,
      eeval C Γ e (Int n) ->
      n <> 0%Z -> 
      sseval C Γ s1 M1 Wf1 ->
      sseval C Γ (SIf e s1 s2) M1 Wf1

  | S_while_false: forall C Γ e s,
      eeval C Γ e (Int 0%Z) ->
      sseval C Γ (SWhile e s) C.(M) C.(wf)

  | S_while_true: forall C Γ e s n M2 Wf2 M3 Wf3,
      eeval C Γ e (Int n) ->
      n <> 0%Z ->
      sseval C Γ s M2 Wf2 ->
      sseval {|E:=C.(E);M:=M2;inj:=C.(inj);wf:=Wf2|} Γ (SWhile e s) M3 Wf3 -> 
      sseval C Γ (SWhile e s) M3 Wf3

  | S_let: forall C1 Γ x τ s C2 M3 Wf3 M4
     (Hdom: C1.(E) x = ϵ)
     (Halloc: C2 = alloc_var C1 x (sizeof(mtype τ)))
     (Hdealloc: ⎣M4⎦ = dealloc_var {|E:=C2.(E);M:=M3;inj:=C2.(inj);wf:=Wf3|} x),
      sseval C2 Γ s M3 Wf3 ->
      sseval C1 Γ (SLet x τ s) M4 (wf_after_alloc_dealloc_var Hdom Halloc Hdealloc)

  (* TODO: add missing rules *)
  .
  
End Semantics.

Module Type SIG(V : DecidableType)(B: Eqb.EQB)
  (Import EMM: ExecutionMemoryModel B)
  (Import Ctx: Context.SIG V B EMM)
  (Import CStx: Common.Syntax.SIG V)
  (Import Stx: Target.Syntax.SIG V CStx)
  (CSem: Common.Semantics.SIG V B EMM Ctx CStx).

  Include Semantics V B EMM Ctx CStx Stx CSem.
  
End SIG.
