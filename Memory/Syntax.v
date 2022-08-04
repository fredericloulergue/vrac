Require Import ZArith Structures.Equalities String.
Require Import Vrac.MemoryType Vrac.Error Vrac.Option Vrac.Tactics.



Module Syntax(V : DecidableType).

  Module Types.
  
    Inductive type :=
    | TInt : Mtyp.t -> type
    | TPtr: type -> type.

    Definition t := type.
    
    Definition mtype: mtyp -> type -> mtyp :=
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

  Ltac simpl_type_eqb :=
    simpl_generic_eqb eqb eqb_refl eqb_sym eqb_eq eqb_neq.
  
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
  | EInt (n: Z) (τ: type)      (* Integer value *)
  | EVar (x: V.t) (τ: type)    (* variable *)
  | EDeref (e: expr) (τ: type) (* dereference *)
  | EAddrof (e: expr) (τ: type)(* address *)
  | EUnop (op: unary_operation) (e: expr) (τ: type)
  | EBinop (op: binary_operation) (e1 e2: expr) (τ: type).

  Definition type_int (n:Z) (τ:type) : result type :=
    match τ with
    | TInt κ =>  if ( (min_int (sizeof κ)<=? n)%Z &&
                     (n <=? max_int (sizeof κ))%Z )%bool
                then Ok τ
                else Error "not storable"
    | _ => Error "not an integer type"
    end.

  Open Scope error_monad_scope.

  Definition same_as_checked τ τ' : result type :=
     if Types.eqb τ τ'
     then Ok τ
     else Error "type mismatch".

  Definition type_env := V.t -> option type.
  
  Fixpoint check_type (Γ: type_env) (e: expr) : result type :=
    match e with
    | EInt n τ => type_int n τ
    | EVar x τ => match Γ x with
                 | ϵ => Error "undefined identifier"
                 | ⎣τ'⎦ => same_as_checked τ τ'
                 end
    | EDeref e τ =>
        match check_type Γ e with 
        | Ok (TPtr τ') => same_as_checked τ τ'
        | _ => Error "not dereferencing a pointer"
        end
    | EAddrof e τ =>
        do τ' <- check_type Γ e;
        same_as_checked τ (TPtr τ')
    | EUnop op e τ =>
        do τ' <- check_type Γ e;
        match τ' with
        | TInt _ => same_as_checked τ τ'
        | TPtr _ => Error "no unary operation on pointers"
        end
    | EBinop op e1 e2 τ =>
        do τ1 <- check_type Γ e1;
        do τ2 <- check_type Γ e2;
        match (op, τ1, τ2) with
        | (_, TInt κ1, TInt κ2) =>
            same_as_checked τ (TInt (MemoryType.max κ1 κ2))
        | ((Oadd|Osub), TPtr τ', TInt _) =>
            same_as_checked τ (TPtr τ')
        | (Oeq, TPtr τ'1, TPtr τ'2) =>
            if Types.eqb τ'1 τ'2
            then same_as_checked τ (TInt i8)
            else Error "incompatible types for eq"
        | _ => Error "incorrect types for binary operation"
        end
    end.
  
End Syntax.

Module Type SIG(V : DecidableType).
  Include Syntax V.
End SIG.

