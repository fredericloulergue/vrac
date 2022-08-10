Require Import ZArith Structures.Equalities String.

From Vrac.Lib Require Import Error Option Tactics.
From Vrac.Memory Require Import MemoryType.
From Vrac.Common Require Import Syntax.



Module Syntax(V : DecidableType)(Import CStx: Syntax.SIG V).


  Import Types. Import T. Import Expr.

  Open Scope error_monad_scope.
  
  Module Term.
    
    Inductive term :=
    | TExpr (e: expr) (τ: ctyp)
    | TDeref (t: term) (τ: ctyp)
    | TUnop (op: unary_operation) (t: term) (τ: ctyp)
    | TBinop (op: binary_operation) (t1: term) (t2: term) (τ: ctyp)
    | TBaseaddress (t: term) (τ: ctyp)
    | TOffset (t: term) (τ: ctyp)
    | TBlocklength (t: term) (τ: ctyp).

    Definition typeof (t: term): ctyp :=
      match t with
      | TExpr _ τ 
      | TDeref _ τ 
      | TUnop _ _ τ 
      | TBinop _ _ _ τ
      | TBaseaddress _ τ
      | TOffset _ τ
      | TBlocklength _ τ => τ
      end.
    
    Fixpoint check_type (Γ: type_env) (t: term) : result ctyp :=
      match t with
      | TExpr e τ =>
          do τ' <- Expr.check_type Γ e;
          match_ctyp τ τ'
      | TDeref t τ =>
          match check_type Γ t with 
          | Ok (TPtr τ') => match_ctyp τ τ'
          | _ => Error "not dereferencing a pointer"
          end
      | TUnop op t τ =>
          do τ' <- check_type Γ t;
          match τ' with
          | TInt _ => match_ctyp τ τ'
          | TPtr _ => Error "no unary operation on pointers"
          end
      | TBinop op t1 t2 τ =>
          do τ1 <- check_type Γ t1;
          do τ2 <- check_type Γ t2;
          match (op, τ1, τ2) with
          | (_, TInt κ1, TInt κ2) =>
              match_ctyp τ (TInt (MemoryType.max κ1 κ2))
          | ((Oadd|Osub), TPtr τ', TInt _) =>
              match_ctyp τ (TPtr τ')
          | (Oeq, TPtr τ'1, TPtr τ'2) =>
              if Types.eqb τ'1 τ'2
              then match_ctyp τ (TInt i8)
              else Error "incompatible types for eq"
          | _ => Error "incorrect types for binary operation"
          end
      | TBaseaddress t τ =>
          do τ' <- check_type Γ t;
          match_ctyp τ (TPtr τ')
      | TOffset t τ =>
          do τ' <- check_type Γ t;
          match (τ', τ) with
          | (TPtr _, TInt _) => Ok τ
          | (TPtr _, _) => Error "offset should be an integer"
          | (_, _) => Error "argument of offset should be a pointer"
          end
      | TBlocklength t τ =>
          do τ' <- check_type Γ t;
          match (τ', τ) with
          | (TPtr _, TInt _) => Ok τ
          | (TPtr _, _) => Error "block_length should be an integer"
          | (_, _) => Error "argument of block_length should be a pointer"
          end
      end.

    Ltac destructs :=
      match goal with
      | [H : context [ match ?e with | Ok _ => _ | _ => _ end ] |- _ ] =>
          destruct e; simpl in *; try discriminate
      | [H : context [ match ?e with | TInt _ => _ | _ => _ end ] |- _ ] =>
          destruct e; simpl in *; try discriminate
      | [H : context [ match ?e with | Oadd => _ | _ => _ end ] |- _ ] =>
          destruct e; simpl in *; try discriminate
      | [H : context [ match ?e with | Onot => _ | _ => _ end ] |- _ ] =>
          destruct e; simpl in *; try discriminate
      | [H : context [ do _ <- ?e; _ ] |- _ ] =>
          destruct e; simpl in *; try discriminate
      end.

    Ltac simpl_match_ctyp := 
      unfold match_ctyp in *; simpl_if; try discriminate.
    
    Lemma type_check_type_of:
      forall Γ t τ, check_type Γ t = Ok τ -> typeof t = τ.
    Proof.
      intros Γ t0 τ H.
      destruct t0 ; simpl in *;
        try solve [repeat destructs;
                   repeat simpl_match_ctyp;
                   now inversion H].
    Qed.

  End Term.

  Import Term.
  
  Module Pred.

    Inductive relational_predicate :=
    | PEq
    | PLt
    | PGt
    | PLe
    | PGe.
    
    Inductive pred :=
    | PTrue
    | PFalse
    | PComp (R: relational_predicate) (t1 t2: term)
    | PAnd (p1 p2: pred)
    | PNot (p: pred)
    | PValid (t: term)
    | PInitialized (t: term).

    Fixpoint check_type Γ p : result unit :=
      match p with
      | PTrue | PFalse => Ok tt
      | PComp R t1 t2 =>
          do τ1 <- Term.check_type Γ t1;
          do τ2 <- Term.check_type Γ t2;
          match (R, τ1, τ2) with
          | (_, TInt _, TInt _) => Ok tt
          | (PEq, TPtr τ'1, TPtr τ'2) =>
              if Types.eqb τ'1 τ'2
              then Ok tt
              else Error "incompatible types for equality"
          | _ => Error "incorrect types for comparison"
          end
      | PNot p => check_type Γ p
      | PAnd p1 p2 =>
          do ct1 <- check_type Γ p1;
          do ct2 <- check_type Γ p2;
          Ok tt
      | (PValid t | PInitialized t) =>
          do τ' <- Term.check_type Γ t;
          match τ' with
          | TPtr _ => Ok tt
          | _ => Error "argument of valid should be a pointer term"
          end
      end%bool.

  End Pred.

  Import Pred.

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
    | SLogicalassert (p: pred).

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
      | SMalloc e1 e2 =>
          do τ1 <- Expr.check_type Γ e1;
          do τ2 <- Expr.check_type Γ e2;
          match (τ1, τ2) with
          | (TPtr _, TInt _) => Ok tt
          | _ => Error "incorrect types for malloc"
          end
      | SFree e =>
          do τ <- Expr.check_type Γ e;
          match τ with
          | TPtr _ => Ok tt
          | _ => Error "incorrect type for free"
          end
      | SLet x τ s =>
          let Γ' := fun y => if V.eq_dec y x then ⎣τ⎦ else Γ y in
          check_type Γ' s
      | SLogicalassert p =>
          Pred.check_type Γ p
      end.

  End Stmt.
    
  Close Scope error_monad_scope.
  
End Syntax.

Module Type SIG(V : DecidableType)(CStx: Syntax.SIG V).
  Include Syntax V CStx.
End SIG.

