Require Import ZArith Structures.Equalities String.
Require Import Vrac.MemoryType Vrac.Error Vrac.Option Vrac.Tactics.



Module Syntax(V : DecidableType).

  Open Scope error_monad_scope.
  
  Module Types.
  
    Inductive ctyp :=
    | TInt : Mtyp.t -> ctyp
    | TPtr: ctyp -> ctyp.

    Definition t := ctyp.
    
    Definition mtype: mtyp -> ctyp -> mtyp :=
      fun machine_word ty =>
        match ty with
        | TInt mtype => mtype 
        | TPtr _ => machine_word
        end.

    Fixpoint eqb τ1 τ2 : bool :=
      match (τ1, τ2) with
      | (TInt κ1, TInt κ2) => Mtyp.eqb κ1 κ2
      | (TPtr τ'1, TPtr τ'2) => eqb τ'1 τ'2
      | _ => false
      end.

    Lemma eqb_eq : forall x y, eqb x y = true <-> x = y.
    Proof.
      intros x y; split; intro H; revert H; revert y.
      - induction x as [|x Hx]; destruct y;
          intro H; simpl in *; try discriminate.
        + apply Mtyp.eqb_eq in H.
          now subst.
        + apply Hx in H.
          now subst.
      - induction x as [|x Hx]; destruct y;
          intro H; simpl in *; try discriminate.
        + inversion H; subst.
          now simpl_mtyp_eqb.
        + apply Hx.
          now inversion H.
    Qed.

  End Types.
  
  Module T := Eqb.Full Types. Import Types. Import T.

  Ltac simpl_ctyp_eqb :=
    simpl_generic_eqb eqb eqb_refl eqb_sym eqb_eq eqb_neq.


  Definition match_ctyp τ τ' : result ctyp :=
    if Types.eqb τ τ'
    then Ok τ
    else Error "type mismatch".
  
  Definition type_int (n:Z) (τ:ctyp) : result ctyp :=
    match τ with
    | TInt κ =>  if ( (min_int (sizeof κ)<=? n)%Z &&
                       (n <=? max_int (sizeof κ))%Z )%bool
                then Ok τ
                else Error "not storable"
    | _ => Error "not an integer type"
    end.

  Definition type_env := V.t -> option ctyp.
  
  Module Expr.
  
    Inductive unary_operation : Type :=
    | Onot
    | Oneg.
    
    Inductive binary_operation : Type :=
    | Oadd  (* addition *)
    | Osub  (* subtraction *)
    | Omul  (* multiplication *)
    | Odiv  (* division *)
    | Omod  (* remainder *)
    | Oeq   (* comparison (==) *)
    | Olt   (* comparison (<) *)
    | Ogt   (* comparison (>) *)
    | Ole   (* comparison (<=) *)
    | Oge   (* comparison (>=) *).
    
    Inductive expr : Type :=
    | EInt (n: Z) (τ: ctyp)      (* Integer value *)
    | EVar (x: V.t) (τ: ctyp)    (* variable *)
    | EDeref (e: expr) (τ: ctyp) (* dereference *)
    | EAddrof (e: expr) (τ: ctyp)(* address *)
    | EUnop (op: unary_operation) (e: expr) (τ: ctyp)
    | EBinop (op: binary_operation) (e1 e2: expr) (τ: ctyp).
        
    Fixpoint check_type (Γ: type_env) (e: expr) : result ctyp :=
      match e with
      | EInt n τ => type_int n τ
      | EVar x τ => match Γ x with
                   | ϵ => Error "undefined identifier"
                   | ⎣τ'⎦ => match_ctyp τ τ'
                   end
      | EDeref e τ =>
          match check_type Γ e with 
          | Ok (TPtr τ') => match_ctyp τ τ'
          | _ => Error "not dereferencing a pointer"
          end
      | EAddrof e τ =>
          do τ' <- check_type Γ e;
          match_ctyp τ (TPtr τ')
      | EUnop op e τ =>
          do τ' <- check_type Γ e;
          match τ' with
          | TInt _ => match_ctyp τ τ'
          | TPtr _ => Error "no unary operation on pointers"
          end
      | EBinop op e1 e2 τ =>
          do τ1 <- check_type Γ e1;
          do τ2 <- check_type Γ e2;
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
      end.

  End Expr.

  Import Expr.

  Module Term.
    
    Inductive term :=
    | TExpr (e: expr) (τ: ctyp)
    | TDeref (t: term) (τ: ctyp)
    | TUnop (op: unary_operation) (t: term) (τ: ctyp)
    | TBinop (op: binary_operation) (t1: term) (t2: term) (τ: ctyp)
    | TBaseaddress (t: term) (τ: ctyp)
    | TOffset (t: term) (τ: ctyp)
    | TBlocklength (t: term) (τ: ctyp).

    Fixpoint check_type (Γ: type_env) (t: term) : result ctyp :=
      match t with
      | TExpr e τ => Expr.check_type Γ e
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

Module Type SIG(V : DecidableType).
  Include Syntax V.
End SIG.

