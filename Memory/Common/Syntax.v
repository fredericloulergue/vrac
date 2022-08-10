Require Import ZArith Structures.Equalities String.

From Vrac.Lib Require Import Tactics Option Error.
From Vrac.Memory Require Import MemoryType.

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

    Definition typeof (e: expr) :=
      match e with
        | EInt _ τ 
        | EVar _ τ  
        | EDeref _ τ  
        | EAddrof _ τ  
        | EUnop _ _ τ  
        | EBinop _ _ _ τ => τ
      end.
    
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

    Lemma type_check_type_of:
      forall Γ e τ, check_type Γ e = Ok τ -> typeof e = τ.
    Proof.
      intros Γ e τ H.
      destruct e; simpl in *; unfold type_int, match_ctyp in *;
        try solve [ destruct(check_type Γ e); simpl in *;
                    try destruct(c); try simpl_if; try discriminate;
                    now inversion H ].
      - destruct τ0; repeat simpl_if; try discriminate; now inversion H.
      - destruct(Γ x); simpl in *;
          try simpl_if; try discriminate;
          now inversion H.
      - destruct(check_type Γ e1); simpl in *;
          destruct(check_type Γ e2); simpl in *;
          try destruct op, c, c0; repeat simpl_if; try discriminate;
          now inversion H.
    Qed.

  End Expr.

  Import Expr.
   
  Close Scope error_monad_scope.
  
End Syntax.

Module Type SIG(V : DecidableType).
  Include Syntax V.
End SIG.

