(************************************************************************)
(* VRAC: Verified Runtime Assertion Checker                             *)
(* Copyright Université d'Orléans                                       *)
(* Coq code by Frédéric Loulergue                                       *)
(*   based on the VRAC project by                                       *)
(*   Dara Ly, Nikolai Kosmatov, Frédéric Loulergue, Julien Signoles     *)
(* This file is distributed under the terms of the                      *)
(*   Université d'Orléans Non-Commercial License Agreement              *)
(* (see LICENSE file for the text of the license)                       *) 
(************************************************************************)

Require Import Arith ZArith Lia List Structures.Equalities.

From Vrac.Memory Require Import MemoryType ExecutionMemoryModel Context.
From Vrac.Common Require Import Syntax.
From Vrac.Lib Require Import Tactics Option Error.

Module Semantics(V : DecidableType)(B: Eqb.EQB)
  (Import EMM: ExecutionMemoryModel B)
  (Import Ctx: Context.SIG V B EMM)
  (Import Stx: Syntax.SIG V).

  Import Stx.Types Stx.Expr.

  Definition mtype := mtype machine_word.
  
  Inductive kind := KInt | KPtr | KUn.
  
  Definition kind_t (τ: ctyp) : kind :=
    match τ with
    | TInt _ => KInt
    | TPtr _ => KPtr
    end.

  Definition kind_v (v: value) : kind :=
    match v with
    | Int _ => KInt
    | Ptr _ => KPtr
    | _ => KUn
    end.

  Definition valid_expr (Γ: type_env)(e: expr) : Prop :=
    exists τ, Expr.check_type Γ e = Ok τ.

  Ltac rewrite_clear :=
    match goal with
    | [ H: _ = _ |- _ ] =>
        try rewrite H; clear H
    end.

  Ltac check_type :=
    intros; simpl; repeat rewrite_clear; simpl;
    unfold match_ctyp; now simpl_ctyp_eqb.
  
  Fact deref_check_type:
    forall Γ e τ,
    Expr.check_type Γ e = Ok (TPtr τ) ->
    Expr.check_type Γ (EDeref e τ) = Ok τ.
  Proof. check_type. Qed.
  
  Fact parith_check_type:
    forall Γ e1 τ1 e2 κ2,
      Expr.check_type Γ e1 = Ok (TPtr τ1) ->
      Expr.check_type Γ e2 = Ok (TInt κ2) ->
      Expr.check_type Γ (EBinop Oadd e1 e2 (TPtr τ1)) = Ok (TPtr τ1).
  Proof. check_type. Qed.

  Definition within_bounds (κ: mtyp)(n:Z) : option value :=
    if ((min_int (sizeof κ) <=? n)%Z && (n <=? max_int (sizeof κ))%Z)%bool
      then ⎣Int n⎦
    else ⎣Undef⎦.

  Ltac within_bounds :=
    let Hcond := fresh "Hcond" in 
    unfold within_bounds in *;
    match goal with
    | [ H: context [ if ?cond then _ else _ ] |- context[if ?cond then _ else _]] =>
        case_eq(cond); intro Hcond; rewrite Hcond in H;
        injection H; clear H; intro H; subst; trivial
    end.
  
  Definition sem_unop (κ: mtyp) op (v: value) : option value :=
    match (op,v) with
    | (_, Undef) => ⎣Undef⎦
    | (Oneg, Int n) => within_bounds κ (-n)%Z
    | (Onot, Int n) => ⎣Int(Z.b2z(n =? 0)%Z)⎦
    | (_, _) => ϵ
    end.

  Property sem_unop_not_ptr:
    forall κ op v b δ, sem_unop κ op v <> ⎣Ptr(b,δ)⎦.
  Proof.
    intros κ op v b δ H.
    unfold sem_unop in H.
    destruct op; destruct v; simpl in H;
      try solve [inversion H;discriminate].
    unfold within_bounds in H; simpl_if; inversion H;discriminate.
  Qed.
  
  Definition sem_binop (κ: mtyp) op (v1 v2: value) : option value :=
    match (op, v1, v2) with
    | (Odiv, _, Int 0%Z) => ϵ
    | (Omod, _, Int 0%Z) => ϵ
    | (_, Undef, _) => ⎣Undef⎦
    | (_, _, Undef) => ⎣Undef⎦
    | (Oadd, Int n1, Int n2) => within_bounds κ (n1 + n2)%Z
    | (Osub, Int n1, Int n2) => within_bounds κ (n1 - n2)%Z
    | (Omul, Int n1, Int n2) => within_bounds κ (n1 * n2)%Z
    | (Odiv, Int n1, Int n2) => within_bounds κ (n1 / n2)%Z
    | (Omod, Int n1, Int n2) => within_bounds κ (n1 mod n2)%Z
    | (Oeq, Int n1, Int n2) => ⎣Int(Z.b2z(n1 =? n2)%Z)⎦
    | (Olt, Int n1, Int n2) => ⎣Int(Z.b2z(n1 <? n2)%Z)⎦
    | (Ogt, Int n1, Int n2) => ⎣Int(Z.b2z(n1 >? n2)%Z)⎦
    | (Ole, Int n1, Int n2) => ⎣Int(Z.b2z(n1 <=? n2)%Z)⎦
    | (Oge, Int n1, Int n2) => ⎣Int(Z.b2z(n1 >=? n2)%Z)⎦
    | (Oeq, Ptr (b,δ), Ptr(b',δ')) => ⎣Int(Z.b2z( (B.eqb b b') && (Z.eqb δ δ'))%bool)⎦
    | (_, _, _) => ϵ
    end.

  Property sem_binop_not_ptr:
    forall κ op v1 v2 b δ, sem_binop κ op v1 v2 <> ⎣Ptr(b,δ)⎦.
  Proof.
    intros κ op [n1|[b1 δ1]|] [n2|[b2 δ2]|] b δ H;
      unfold sem_binop in H; destruct op; simpl in H;
      solve [inversion H;discriminate] ||
        solve [unfold within_bounds in H; simpl_if; inversion H;discriminate] ||
        match goal with
        | [ H: context [match ?n with | 0%Z => _ | _ => _ end] |- _ ] =>
            destruct n; try discriminate;
            unfold within_bounds in H; simpl_if; inversion H;discriminate
        end.
  Qed.

  Inductive eeval: context -> type_env -> expr -> value -> Prop :=
  | E_int: forall C Γ n τ,
      valid_expr Γ (EInt n τ) ->
      eeval C Γ (EInt n τ) (Int n)

  | E_addr: forall C Γ e τ b δ,
      valid_expr Γ e ->
      lveval C Γ e (b,δ) ->
      eeval C Γ (EAddrof e τ) (Ptr(b,δ))

  | E_lval: forall C Γ e τ b δ v,
      Expr.check_type Γ e = Ok τ -> 
      lveval C Γ e (b,δ) ->
      EMM.load(mtype τ, C.(M), b, δ) = ⎣v⎦ ->
      v <> Undef ->
      kind_t τ = kind_v v ->
      eeval C Γ e v
            
  | E_unop: forall C Γ op e τ v v',
      Expr.check_type Γ (EUnop op e τ) = Ok τ ->
      eeval C Γ e v ->
      sem_unop (mtype τ) op v = ⎣v'⎦ ->
      eeval C Γ (EUnop op e τ) v'

  | E_binop: forall C Γ op e1 e2 τ v1 v2 v,
      Expr.check_type Γ (EBinop op e1 e2 τ) = Ok τ ->
      eeval C Γ e1 v1 ->
      eeval C Γ e2 v2 ->
      sem_binop (mtype τ) op v1 v2 = ⎣v⎦ ->
      eeval C Γ (EBinop op e1 e2 τ) v
         
  | E_parith: forall C Γ e1 τ1 e2 κ2 b δ n sz,
      Expr.check_type Γ e1 = Ok (TPtr τ1) ->
      Expr.check_type Γ e2 = Ok (TInt κ2) ->
      eeval C Γ e1 (Ptr(b,δ)) ->
      eeval C Γ e2 (Int n) ->
      sz = sizeof(mtype τ1) ->
      (δ mod sz = 0)%Z ->
      eeval C Γ (EBinop Oadd e1 e2 (TPtr τ1)) (Ptr(b,(δ+n*sz)%Z))

  with lveval: context -> type_env -> expr -> B.t * Z -> Prop :=
  | LV_var: forall C Γ x τ b,
      C.(E) x = ⎣ b ⎦ ->
      lveval C Γ (EVar x τ) (b,0%Z)

  | LV_deref: forall C Γ e τ b δ,
      Expr.check_type Γ e = Ok (TPtr τ) ->
      eeval C Γ e (Ptr(b,δ)) ->
      lveval C Γ (EDeref e τ) (b,δ)
  .

  Scheme eeval_ind' :=
    Induction for eeval Sort Prop
      with lveval_ind' :=
      Induction for lveval Sort Prop.

  Fact induced_undef:
    forall σ Hσ v, v<>Undef -> induced σ Hσ v <> Undef.
  Proof.
    intros σ Hσ [n|[b δ]|] H; simpl;
      try discriminate.
    now contradict H.
  Qed.

  Fact induced_kind:
    forall σ Hσ v, kind_v v = kind_v (induced σ Hσ v).
  Proof.
    intros σ Hσ [n|[b δ]|]; trivial.
  Qed.
  
  Fact induced_unop:
    forall τ op σ Hσ v v',
      sem_unop (mtype τ) op v = ⎣ v' ⎦ ->
      sem_unop (mtype τ) op (induced σ Hσ v) = ⎣ induced σ Hσ v' ⎦.
  Proof.
    unfold sem_unop.
    intros τ op σ Hσ [n|[b δ]|] v' H; destruct op; simpl in H; simpl;
      try discriminate;
      try within_bounds;
      injection H; clear H; intro H; subst; trivial.
  Qed.

  Fact induced_binop:
    forall κ op σ Hσ v1 v2 v,
      sem_binop κ op v1 v2 = ⎣ v ⎦ -> 
      sem_binop κ op (induced σ Hσ v1) (induced σ Hσ v2) = ⎣ induced σ Hσ v ⎦.
  Proof.
    intros κ op σ Hσ [n1|[b1 δ1]|][n2|[b2 δ2]|] v H;
    unfold sem_binop in *; simpl in *;
      destruct op; simpl in *;
      try discriminate;
      try within_bounds;
      try solve [destruct n2; try discriminate; try within_bounds;
                 inversion H; now subst];
      try solve [injection H; clear H; intro H; subst; trivial].
    assert(Heqb: B.eqb b1 b2 = B.eqb (σ b1) (σ b2)).
    {
      case_eq(B.eqb b1 b2); intro HH.
      - now repeat simpl_block_eqb.
      - apply Block.eqb_neq in HH.
        symmetry. apply Bool.not_true_iff_false.
        contradict HH.
        simpl_block_eqb.
        eapply σ_eq; eauto.
    }
    rewrite <- Heqb.
    injection H; clear H; intro H; now subst.
  Qed.
  
  Lemma isomorphic_evalexpr:
    forall C C' Γ σ Hσ,
      isomorphic C C' σ Hσ ->
      (forall e v,
          eeval C Γ e v ->
          eeval C' Γ e (induced σ Hσ v)).
  Proof.
    intros C C' Γ σ Hσ Hiso e v Heeval.
    generalize dependent C'. generalize dependent σ.
    induction Heeval
      using eeval_ind'
      with (P0:=fun C Γ e ptr (H: lveval C Γ e ptr) =>
                  forall C' σ Hσ (Hiso: isomorphic C C' σ Hσ),
                    let (b,δ) := ptr in
                    lveval C' Γ e (σ b, δ)); subst.
    - intros. now constructor.
    - constructor.
      + trivial.
      + eapply IHHeeval; eauto.
    - intros σ Hσ C' Hiso.
      assert(Hlveval: lveval C' Γ e (σ b, δ)) by eauto.
      assert(Hload: load (mtype τ, C'.(M), σ b, δ) = ⎣ induced σ Hσ v ⎦)
        by now rewrite <- iso_load.
      eapply E_lval; eauto.
      + now apply induced_undef.
      + now rewrite <- induced_kind.
    - simpl in *. intros σ Hσ C' Hiso.
      eapply E_unop; eauto.
      now apply induced_unop.
    - simpl in *. intros σ Hσ C' Hiso.
      eapply E_binop; eauto.
      now apply induced_binop.
    - simpl in *. intros σ Hσ C' Hiso.
      specialize (IHHeeval1 σ Hσ C' Hiso).
      specialize (IHHeeval2 σ Hσ C' Hiso).
      eapply E_parith; eauto.
    - intros; constructor.
      now apply iso_environment.
    - intros C' σ Hσ Hiso. simpl in *.
      econstructor; eauto.
  Qed.

  Lemma value_in_supp:
    forall C Γ e v b δ,
      eeval C Γ e v ->
      v = Ptr(b,δ) ->
      b ∈ supp(C.(M)).
  Proof.
    intros C Γ e v b δ Heval Hv.
    generalize dependent δ.
    generalize dependent b.
    induction Heval
      using eeval_ind'
      with (P0:=fun C Γ e ptr (H: lveval C Γ e ptr) =>
                  forall b δ, ptr = (b,δ) ->
                  b ∈ supp (C.(M))).
    - intros; discriminate.
    - intros; eapply IHHeval; now inversion Hv.
    - intros b' δ' Hv. subst.
      econstructor 2; eauto.
    - intros b δ Hv. subst.
      assert(H: sem_unop (mtype τ) op v <> ⎣ Ptr (b, δ) ⎦)
        by  apply sem_unop_not_ptr.
      exfalso; now apply H.
    - intros b δ Hv. subst.
      assert(H: sem_binop (mtype τ) op v1 v2 <> ⎣ Ptr (b, δ) ⎦)
        by  apply sem_binop_not_ptr.
      exfalso; now apply H.
    - intros b' δ' Hv; inversion Hv; subst; clear Hv.
      now eapply IHHeval1.
    - intros b' δ' H. inversion H; subst; clear H.
      match goal with
      | [ H: _.(E) _ = _ |- _ ] =>
          apply wf in H
      end.
      now constructor.
    - intros b' δ' H. inversion H; subst; clear H.
      now eapply IHHeval.
  Qed.
  
End Semantics.

Module Type SIG (Import V : DecidableType)(Import B: Eqb.EQB)
  (Import EMM: ExecutionMemoryModel B)
  (Import Ctx: Context.SIG V B EMM)
  (Import Stx: Syntax.SIG V).

  Include Semantics V B EMM Ctx Stx.
  
End SIG.
