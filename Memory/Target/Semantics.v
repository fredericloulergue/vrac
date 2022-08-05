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

  Import CStx.Types CStx.Expr CSem.
  
End Semantics.
