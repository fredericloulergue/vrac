Require Import ZArith Structures.Equalities String.

From Vrac.Lib Require Import Error Option Tactics.
From Vrac.Memory Require Import MemoryType.
From Vrac.Common Require Import Syntax.

Module Syntax(V : DecidableType)(Import CStx: Syntax.SIG V).

  Open Scope error_monad_scope.
  
  Import Types. Import T. Import Expr.

  Module Stmt.

    Inductive stmt :=
    | SSkip
    | SAssign (e1 e2: expr)
    | SSeq (s1 s2: stmt)
    | SIf (e: expr) (s1 s2: stmt)
    | SWhile (e: expr) (s: stmt)
    | SMalloc (e1 e2: expr)
    | SFree (e: expr)
    | SLet (x: V.t)(τ: ctyp)(s: stmt)
    | SAssert (e: expr)
    | SStoreblock (e1 e2: expr)
    | SDeleteblock (e: expr)
    | SIsvalid (e1 e2: expr)
    | SIsinitialized (e1 e2: expr)
    | SInitialize (e: expr)
    | SBaseaddress (e1 e2: expr)
    | SOffset (e1 e2: expr)
    | SBlocklength (e1 e2: expr).

    Fixpoint check_type Γ (s: stmt) : result unit :=
      match s with
      | SSkip => Ok tt
      | SAssign e1 e2 =>
          do τ1 <- Expr.check_type Γ e1;
          do τ2 <- Expr.check_type Γ e2;
          do r <- match_ctyp τ1 τ2;
          Ok tt
      | SSeq s1 s2 =>
          do ct1 <- check_type Γ s1;
          do ct2 <- check_type Γ s2;
          Ok tt
      | SIf e s1 s2 =>
          do τ <- Expr.check_type Γ e;
          do ct1 <- check_type Γ s1;
          do ct2 <- check_type Γ s2;
          Ok tt
      | SWhile e s =>
          do τ <- Expr.check_type Γ e;
          do ct <- check_type Γ s;
          Ok tt                     
      | SMalloc e1 e2 | SStoreblock e1 e2 =>
          do τ1 <- Expr.check_type Γ e1;
          do τ2 <- Expr.check_type Γ e2;
          match (τ1, τ2) with
          | (TPtr _, TInt _) => Ok tt
          | _ => Error "incorrect types for malloc or store_block"
          end
      | SFree e | SDeleteblock e | SInitialize e =>
          do τ <- Expr.check_type Γ e;
          match τ with
          | TPtr _ => Ok tt
          | _ => Error "incorrect type for free, delete_block or initialize"
          end
      | SLet x τ s =>
          let Γ' := fun y => if V.eq_dec y x then ⎣τ⎦ else Γ y in
          check_type Γ' s
      | SAssert e =>
          do τ <- Expr.check_type Γ e;
          match τ with
          | TInt _ => Ok tt
          | _ => Error "incorrect type for assert"
          end
      | SIsvalid e1 e2 | SIsinitialized e1 e2 =>
          do τ1 <- Expr.check_type Γ e1;
          do τ2 <- Expr.check_type Γ e2;
          match (τ1, τ2) with
          | (TInt i8, TPtr _) => Ok tt
          | _ => Error "incorrect types for is_valid or is_initialized"
          end
      | SBlocklength e1 e2 | SOffset e1 e2 =>
          do τ1 <- Expr.check_type Γ e1;
          do τ2 <- Expr.check_type Γ e2;
          match (τ1, τ2) with
            (* Note: from the paper, but should it really by that? *)
          | (TInt i64, TPtr _) => Ok tt
          | _ => Error "incorrect types for block_length or offset"
          end
      | SBaseaddress e1 e2 =>
          do τ1 <- Expr.check_type Γ e1;
          do τ2 <- Expr.check_type Γ e2;
          match (τ1, τ2) with
          | (TPtr τ1, TPtr τ2) =>
              if Types.eqb τ1 τ2
              then Ok tt
              else Error "Incompatible pointer types in base_address"
          | _ => Error "incorrect types for is_valid"
          end
            
      end.

  End Stmt.
    
  Close Scope error_monad_scope.
  
End Syntax.

Module Type SIG(V : DecidableType)(CStx: Syntax.SIG V).
  Include Syntax V CStx.
End SIG.
