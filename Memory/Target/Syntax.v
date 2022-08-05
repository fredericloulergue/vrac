Require Import ZArith Structures.Equalities String.

From Vrac.Lib Require Import Error Option Tactics.
From Vrac.Memory Require Import MemoryType.
From Vrac.Common Require Import Syntax.

Module Syntax(V : DecidableType)(Import CStx: Syntax.SIG V).

  Open Scope error_monad_scope.
  
  Close Scope error_monad_scope.
  
End Syntax.

Module Type SIG(V : DecidableType)(CStx: Syntax.SIG V).
  Include Syntax V CStx.
End SIG.

