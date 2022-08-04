Require Import Arith ZArith Lia List Structures.Equalities.
Require Import Vrac.Tactics Vrac.Option Vrac.Eqb Vrac.MemoryType
  Vrac.ExecutionMemoryModel Vrac.Context Vrac.Syntax Vrac.Error.

Module Semantics(V : DecidableType)(B: Eqb.EQB)
  (Import EMM: ExecutionMemoryModel B)
  (Import Ctx: Context.SIG V B EMM)
  (Import Stx: Syntax.SIG V).

  Import Stx.Types.

  Definition mtype := mtype machine_word.
  
  Inductive kind := KInt | KPtr | KUn.
  
  Definition kind_t (τ : type) : kind :=
    match τ with
    | TInt _ => KInt
    | TPtr _ => KPtr
    end.

  Definition kind_v (v : value) : kind :=
    match v with
    | Int _ => KInt
    | Ptr _ => KPtr
    | _ => KUn
    end.

  Definition valid_expr (Γ: type_env)(e: Stx.expr) : Prop :=
    exists τ, check_type Γ e = Ok τ.

  Ltac rewrite_clear :=
    match goal with
    | [ H: _ = _ |- _ ] =>
        try rewrite H; clear H
    end.

  Ltac check_type :=
    intros; simpl; repeat rewrite_clear; simpl;
    unfold same_as_checked; now simpl_type_eqb.
  
  Fact deref_check_type:
    forall Γ e τ,
    check_type Γ e = Ok (TPtr τ) ->
    check_type Γ (EDeref e τ) = Ok τ.
  Proof. check_type. Qed.
  
  Fact parith_check_type:
    forall Γ e1 τ1 e2 κ2,
      check_type Γ e1 = Ok (TPtr τ1) ->
      check_type Γ e2 = Ok (TInt κ2) ->
      check_type Γ (EBinop Oadd e1 e2 (TPtr τ1)) = Ok (TPtr τ1).
  Proof. check_type. Qed.

  Inductive eeval: Ctx.context -> Stx.type_env -> Stx.expr -> value -> Prop :=
  | E_int: forall C Γ n τ,
      valid_expr Γ (EInt n τ) ->
      eeval C Γ (EInt n τ) (Int n)
  | E_addr: forall C Γ e τ b δ,
      valid_expr Γ e ->
      lveval C Γ e (b,δ) ->
      eeval C Γ (EAddrof e τ) (Ptr(b,δ))
  | E_lval: forall C Γ e τ b δ v,
      check_type Γ e = Ok τ -> 
      lveval C Γ e (b,δ) ->
      EMM.load(mtype τ, C.(M), b, δ) = ⎣v⎦ ->
      v <> Undef ->
      kind_t τ = kind_v v ->
      eeval C Γ e v
  | E_parith: forall C Γ e1 τ1 v1 e2 κ2 b δ n sz e v,
      check_type Γ e1 = Ok (TPtr τ1) ->
      check_type Γ e2 = Ok (TInt κ2) ->
      eeval C Γ e1 v1 -> v1 = (Ptr(b,δ)) ->
      eeval C Γ e2 (Int n) ->
      sz = sizeof(mtype τ1) ->
      (δ mod sz = 0)%Z ->
      e = EBinop Oadd e1 e2 (TPtr τ1) ->
      v = Ptr(b,(δ+n*sz)%Z) ->
      eeval C Γ e v
  with lveval: Ctx.context -> Stx.type_env -> Stx.expr -> B.t * Z -> Prop :=
  | LV_var: forall C Γ x τ b,
      lveval C Γ (EVar x τ) (b,0%Z)
  | LV_deref: forall C Γ e τ b δ,
      check_type Γ e = Ok (TPtr τ) ->
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
    - simpl in *.
      intros σ Hσ C' Hiso.
      specialize (IHHeeval1 σ Hσ C' Hiso).
      specialize (IHHeeval2 σ Hσ C' Hiso).
      eapply E_parith; eauto.
    - intros; constructor.
    - intros C' σ Hσ Hiso. simpl in *.
      econstructor; eauto.
  Qed.

End Semantics.



