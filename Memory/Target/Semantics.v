Require Import Arith ZArith Lia List Structures.Equalities.

From Vrac.Lib Require Import Tactics Option Eqb Error.
From Vrac.Memory Require Import MemoryType ExecutionMemoryModel Context
  ObservationMemoryModel.
From Vrac.Common Require Import Syntax Semantics.
From Vrac.Target Require Import Syntax.

Module Semantics(V : DecidableType)(B: Eqb.EQB)
  (Import EMM: ExecutionMemoryModel B)
  (Import Ctx: Context.SIG V B EMM)
  (Import OMM: ObservationMemoryModel B)
  (Import CStx: Common.Syntax.SIG V)
  (Import Stx: Target.Syntax.SIG V CStx)
  (CSem: Common.Semantics.SIG V B EMM Ctx CStx).

  Import CStx.Types CStx.Expr Stx.Stmt CSem.
  
  (* TODO: explanation wrt. to the companion paper. *)
  Inductive seval : forall (C: context)(O: obs)(Γ: type_env) (s: stmt) (M2: mem)
                       (O2: obs) (Invariant: forall x b, C.(E) x = ⎣b⎦ -> M2 ⊨ b), Prop :=
    
  | S_skip: forall C O Γ,
      seval C O Γ SSkip C.(M) O C.(wf)
                                             
  | S_assign: forall C O Γ e1 e2 τ v b δ M2
      (Hstore: store(mtype τ, C.(M), b, δ, v) = ⎣M2⎦),
      Expr.check_type Γ e1 = Ok τ ->
      Expr.check_type Γ e2 = Ok τ ->
      eeval C Γ e2 v ->
      lveval C Γ e2 (b,δ) ->
      seval C O Γ (SAssign e1 e2) M2 O (wf_after_store Hstore)

  | S_malloc: forall C O Γ e1 e2 τ n b δ b' M2 M3
                (Halloc: alloc(C.(M), Z.to_nat n) = (b', M2))
                (Hstore: store(mtype (TPtr τ), M2, b, δ, Ptr(b',0%Z)) = ⎣M3⎦),
      Expr.check_type Γ e1 = Ok (TPtr τ) ->
      eeval C Γ e2 (Int n) ->
      lveval C Γ e1 (b,δ) ->
      seval C O Γ (SMalloc e1 e2) M3 O (wf_after_malloc Halloc Hstore)

  | S_free: forall C O Γ e b M2
              (Hfree: free(C.(M), b) = ⎣M2⎦)
              (Him: forall x, C.(E) x <> ⎣b⎦),
      eeval C Γ e (Ptr(b, 0%Z)) ->
      seval C O Γ (SFree e) M2 O (wf_after_free Hfree Him)
                                             
  | S_seq: forall C Γ s1 s2 M2 Wf2 M3 Wf3 O O2 O3,
      seval C O Γ s1 M2 O2 Wf2 ->
      seval {|E:=C.(E);M:=M2;inj:=C.(inj);wf:=Wf2|} O2 Γ s2 M3 O3 Wf3 ->
      seval C O Γ (SSeq s1 s2) M3 O3 Wf3

  | S_if_false: forall C Γ e s1 s2 M2 Wf2 O O2,
      eeval C Γ e (Int 0%Z) ->
      seval C O Γ s2 M2 O2 Wf2 ->
      seval C O Γ (SIf e s1 s2) M2 O2 Wf2

  | S_if_true: forall C Γ e s1 s2 M1 Wf1 n O O1,
      eeval C Γ e (Int n) ->
      n <> 0%Z -> 
      seval C O Γ s1 M1 O1 Wf1 ->
      seval C O Γ (SIf e s1 s2) M1 O1 Wf1 

  | S_while_false: forall C Γ e s O,
      eeval C Γ e (Int 0%Z) ->
      seval C O Γ (SWhile e s) C.(M) O C.(wf)

  | S_while_true: forall C Γ e s n M2 Wf2 M3 Wf3 O O2 O3,
      eeval C Γ e (Int n) ->
      n <> 0%Z ->
      seval C O Γ s M2 O2 Wf2 ->
      seval {|E:=C.(E);M:=M2;inj:=C.(inj);wf:=Wf2|} O2 Γ (SWhile e s) M3 O3 Wf3 -> 
      seval C O Γ (SWhile e s) M3 O3 Wf3

  | S_let: forall C1 Γ x τ s C2 M3 Wf3 M4 O O3
     (Hdom: C1.(E) x = ϵ)
     (Halloc: C2 = alloc_var C1 x (sizeof(mtype τ)))
     (Hdealloc: ⎣M4⎦ = dealloc_var {|E:=C2.(E);M:=M3;inj:=C2.(inj);wf:=Wf3|} x),
      seval C2 O Γ s M3 O3 Wf3 ->
      seval C1 O Γ (SLet x τ s) M4 O3
        (wf_after_alloc_dealloc_var Hdom Halloc Hdealloc)

  | S_assert: forall C O Γ e n,
      eeval C Γ e (Int n) ->
      n <> 0%Z ->
      seval C O Γ (SAssert e) C.(M) O C.(wf)

  | S_storeblock: forall C O Γ p e b n O2,
      eeval C Γ p (Ptr(b,0%Z)) ->
      eeval C Γ e (Int n) ->
      store_block(O, b, Z.to_nat n) = O2 ->
      seval C O Γ (SStoreblock p e) C.(M) O2 C.(wf)

  | S_deleteblock: forall C O Γ p b O2,
      eeval C Γ p (Ptr(b,0%Z)) ->
      delete_block(O, b) = O2 ->
      seval C O Γ (SDeleteblock p) C.(M) O2 C.(wf)

  | S_initialize: forall C O Γ e τ b δ O2,
      Expr.check_type Γ e = Ok (TPtr τ) ->
      eeval C Γ e (Ptr(b,δ)) ->
      initialize(mtype τ, O, b, δ) = O2 ->
      seval C O Γ (SInitialize e) C.(M) O2 C.(wf)

  | S_baseaddr: forall C O Γ e1 e2 τ b1 δ1 b2 δ2 M2
      (Hstore: store(mtype (TPtr τ), C.(M), b1, δ1, Ptr(b2, 0%Z)) = ⎣M2⎦),
      Expr.check_type Γ e1 = Ok(TPtr τ) ->
      lveval C Γ e1 (b1,δ1) ->
      eeval C Γ e2 (Ptr(b2,δ2)) ->
      seval C O Γ (SBaseaddress e1 e2) M2 O (wf_after_store Hstore)

  | S_offset: forall C O Γ e1 e2 b1 δ1 b2 δ2 M2
      (Hstore: store(i64, C.(M), b1, δ1, Int δ2) = ⎣M2⎦),
      lveval C Γ e1 (b1,δ1) ->
      eeval C Γ e2 (Ptr(b2,δ2)) ->
      seval C O Γ (SOffset e1 e2) M2 O (wf_after_store Hstore)

  | S_block_length: forall C O Γ e1 e2 b1 δ1 b2 δ2 M2 n
      (Hstore: store(i64, C.(M), b1, δ1, Int n) = ⎣M2⎦),
      lveval C Γ e1 (b1,δ1) ->
      eeval C Γ e2 (Ptr(b2,δ2)) ->
      length(O, b2) = n -> 
      seval C O Γ (SBlocklength e1 e2) M2 O (wf_after_store Hstore)

  | S_is_valid: forall C O Γ e1 e2 b1 δ1 b2 δ2 M2 τ β
      (Hstore: store(i64, C.(M), b1, δ1, Int (Z.b2z β)) = ⎣M2⎦),
      Expr.check_type Γ e2 = Ok(TPtr τ) ->
      lveval C Γ e1 (b1,δ1) ->
      eeval C Γ e2 (Ptr(b2,δ2)) ->
      is_valid_access(mtype τ, O, b2, δ2)  = β -> 
      seval C O Γ (SIsvalid e1 e2) M2 O (wf_after_store Hstore)

  | S_is_initialized: forall C O Γ e1 e2 b1 δ1 b2 δ2 M2 τ β
      (Hstore: store(i64, C.(M), b1, δ1, Int (Z.b2z β)) = ⎣M2⎦),
      Expr.check_type Γ e2 = Ok(TPtr τ) ->
      lveval C Γ e1 (b1,δ1) ->
      eeval C Γ e2 (Ptr(b2,δ2)) ->
      is_initialized((mtype τ), O, b2, δ2) = β -> 
      seval C O Γ (SIsinitialized e1 e2) M2 O (wf_after_store Hstore)
  .
  
End Semantics.

Module Type SIG(V : DecidableType)(B: Eqb.EQB)
  (Import EMM: ExecutionMemoryModel B)
  (Import Ctx: Context.SIG V B EMM)
  (Import OMM: ObservationMemoryModel B)
  (Import CStx: Common.Syntax.SIG V)
  (Import Stx: Target.Syntax.SIG V CStx)
  (CSem: Common.Semantics.SIG V B EMM Ctx CStx).

  Include Semantics V B EMM Ctx OMM CStx Stx CSem.
  
End SIG.
