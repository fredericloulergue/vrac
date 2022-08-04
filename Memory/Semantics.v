Require Import Arith ZArith Lia List Structures.Equalities.
Require Import Vrac.Tactics Vrac.Option Vrac.Eqb Vrac.MemoryType
  Vrac.ExecutionMemoryModel Vrac.Context Vrac.Syntax Vrac.Error.

Module Semantics(V : DecidableType)(B: Eqb.EQB)
  (Import EMM: ExecutionMemoryModel B)
  (Import Ctx: Context.SIG V B EMM)
  (Import Stx: Syntax.SIG V).

  Import Stx.Types Stx.Expr Stx.Term Stx.Pred Stx.Stmt.

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


  Inductive teval: context -> type_env -> term -> value -> Prop :=
  | T_expr: forall C Γ e τ v,
      Expr.check_type Γ e = Ok τ -> 
      eeval C Γ e v ->
      teval C Γ (TExpr e τ) v

  | T_baseaddr: forall C Γ t τ b δ,
      Term.check_type Γ (TBaseaddress t τ) = Ok τ ->
      teval C Γ t (Ptr(b,δ)) ->
      teval C Γ (TBaseaddress t τ) (Ptr(b,0%Z))

  | T_offset: forall C Γ t τ b δ,
      Term.check_type Γ (TBaseaddress t τ) = Ok τ ->
      teval C Γ t (Ptr(b,δ)) ->
      teval C Γ (TOffset t τ) (Int δ)

  | T_blocklength: forall C Γ t τ b δ n,
      Term.check_type Γ (TBaseaddress t τ) = Ok τ ->
      teval C Γ t (Ptr(b,δ)) ->
      EMM.length(C.(M), b) = n ->
      teval C Γ (TBlocklength t τ) (Int n)

  | T_deref: forall C Γ t τ b δ v,
      Term.check_type Γ t = Ok (TPtr τ) ->
      teval C Γ t (Ptr(b,δ)) ->
      EMM.load(mtype τ, C.(M), b, δ) = ⎣v⎦ ->
      v <> Undef ->
      kind_t τ = kind_v v ->
      teval C Γ (TDeref t τ) v
            
  | T_unop: forall C Γ op t τ v v',
      Term.check_type Γ (TUnop op t τ) = Ok τ ->
      teval C Γ t v ->
      sem_unop (mtype τ) op v = ⎣v'⎦ ->
      teval C Γ (TUnop op t τ) v'

  | T_binop: forall C Γ op t1 t2 τ v1 v2 v,
      Term.check_type Γ (TBinop op t1 t2 τ) = Ok τ ->
      teval C Γ t1 v1 ->
      teval C Γ t2 v2 ->
      sem_binop (mtype τ) op v1 v2 = ⎣v⎦ ->
      teval C Γ (TBinop op t1 t2 τ) v
         
  | T_parith: forall C Γ t1 τ1 t2 κ2 b δ n sz,
      Term.check_type Γ t1 = Ok (TPtr τ1) ->
      Term.check_type Γ t2 = Ok (TInt κ2) ->
      teval C Γ t1 (Ptr(b,δ)) ->
      teval C Γ t2 (Int n) ->
      sz = sizeof(mtype τ1) ->
      (δ mod sz = 0)%Z ->
      teval C Γ (TBinop Oadd t1 t2 (TPtr τ1)) (Ptr(b,(δ+n*sz)%Z))
  .

  Lemma isomorphic_evalterm:
    forall C C' Γ σ Hσ,
      isomorphic C C' σ Hσ ->
      (forall t v,
          teval C Γ t v ->
          teval C' Γ t (induced σ Hσ v)).
  Proof.
    intros C C' Γ σ Hσ Hiso t v H.
    generalize dependent C'. generalize dependent σ.
    induction H; intros σ Hσ C' Hiso.
    - constructor; auto.
      eapply isomorphic_evalexpr; eauto.
    - eapply T_baseaddr; eauto.
      eapply IHteval;  eauto.
    - eapply T_offset; eauto.
      eapply IHteval; eauto.
    - eapply T_blocklength; eauto.
      eapply IHteval;  eauto.
      destruct(valid_block_decidable C.(M) b) as [Hv | Hi].
      + rewrite <- iso_length; auto.
      + assert(Hlen: length(C.(M), b) = 0%Z) by now apply invalid_length.
        assert(Hn: n = 0%Z) by now rewrite Hlen in H1.
        rewrite Hn.
        apply invalid_length.
        contradict Hi.
        now apply iso_valid_block.
    - eapply T_deref; eauto.
      eapply IHteval; eauto.
      + now apply iso_load.
      + unfold induced; destruct v as [n'|[b' δ']|];
          intros; try discriminate; auto.
      + now erewrite <- induced_kind.
    - eapply T_unop; eauto.
      now apply induced_unop.
    - eapply T_binop; eauto.
      now apply induced_binop.
    - simpl in *.
      eapply T_parith; eauto.
  Qed.

  Definition sem_cmp : relational_predicate -> value -> value -> bool :=
    fun cmp v1 v2 => true.
  
  Inductive peval : context -> type_env -> pred -> bool -> Prop :=
  | P_true: forall C Γ,  peval C Γ PTrue true
  | P_false: forall C Γ, peval C Γ PFalse false
  | P_valid: forall C Γ t τ b δ,
      Term.check_type Γ t = Ok (TPtr τ) ->
      teval C Γ t (Ptr (b,δ)) ->
      (C.(M) ⫢ (mtype τ) @ b,δ) ->
      peval C Γ (PValid t) true
  | P_invalid: forall C Γ t τ b δ,
      Term.check_type Γ t = Ok (TPtr τ) ->
      teval C Γ t (Ptr (b,δ)) ->
      not(C.(M) ⫢ (mtype τ) @ b,δ) ->
      peval C Γ (PValid t) false
  | P_initialized: forall C Γ t τ b δ v,
      Term.check_type Γ t = Ok (TPtr τ) ->
      teval C Γ t (Ptr (b,δ)) ->
      load(mtype τ, C.(M), b, δ) = ⎣v⎦ ->
      v <> Undef ->
      peval C Γ (PInitialized t) true
  | P_uninitialized: forall C Γ t τ b δ,
      Term.check_type Γ t = Ok (TPtr τ) ->
      teval C Γ t (Ptr (b,δ)) ->
      ( load(mtype τ, C.(M), b, δ) = ⎣Undef⎦ \/
        load(mtype τ, C.(M), b, δ) = ϵ ) ->
      peval C Γ (PInitialized t) false
  | P_cmp: forall C Γ t1 v1 t2 v2 cmp V,
      Pred.check_type Γ (PComp cmp t1 t2) = Ok tt -> 
      teval C Γ t1 v1 ->
      teval C Γ t2 v2 ->
      sem_cmp cmp v1 v2 = V ->
      peval C Γ (PComp cmp t1 t2) V
  | P_conj_left: forall C Γ p1 p2,
      Pred.check_type Γ (PAnd p1 p2) = Ok tt ->
      peval C Γ p1 false ->
      peval C Γ (PAnd p1 p2) false
  | P_conj_right: forall C Γ p1 p2 V,
      Pred.check_type Γ (PAnd p1 p2) = Ok tt ->
      peval C Γ p1 true ->
      peval C Γ p2 V ->
      peval C Γ (PAnd p1 p2) V
  | P_neg: forall C Γ p V,
      Pred.check_type Γ (PNot p) = Ok tt ->
      peval C Γ p V ->
      peval C Γ (PNot p) (negb V) 
  .

  Generalizable All Variables.
  
  Fact wf_after_store `(Hstore: store(mtype τ, C.(M), b, δ, v) = ⎣M2⎦) :
      (forall x b', C.(E) x = ⎣b'⎦ -> M2 ⊨ b').
  Proof.
    intros x b' Henv. apply wf in Henv.
    now erewrite valid_after_store by eauto.
  Qed.

  
  (* Rules S-seq and S-while-true are slightly different than their
     counterparts in the companion paper. *)
  Inductive seval : forall (C: context) (Γ: type_env) (s: stmt) (M2: mem)
    (Invariant: forall x b, C.(E) x = ⎣b⎦ -> M2 ⊨ b), Prop :=
  | S_skip: forall C Γ, seval C Γ SSkip C.(M) C.(wf)
  | S_assign: forall C Γ e1 e2 τ v b δ M2
      (Hstore: store(mtype τ, C.(M), b, δ, v) = ⎣M2⎦),
      Expr.check_type Γ e1 = Ok τ ->
      Expr.check_type Γ e2 = Ok τ ->
      eeval C Γ e2 v ->
      lveval C Γ e2 (b,δ) ->
      seval C Γ (SAssign e1 e2) M2 (wf_after_store Hstore)
  (*
  | S_malloc: forall C Γ e1 e2 τ n b δ b' M2 M3,
      Expr.check_type Γ e1 = Ok (TPtr τ) ->
      eeval C Γ e2 (Int n) ->
      alloc(C.(M), Z.to_nat n) = (b', M2) ->
      lveval C Γ e1 (b,δ) ->
      store(mtype (TPtr τ), M2, b, δ, Ptr(b',0%Z)) = ⎣M3⎦ ->
      seval C Γ (SMalloc e1 e2) M3
  | S_free: forall C Γ e b M2,
      eeval C Γ e (Ptr(b, 0%Z)) ->
      free(C.(M), b) = ⎣M2⎦ ->
      (forall x, C.(E) x <> ⎣b⎦) ->
      seval C Γ (SFree e) M2
      *)
  | S_logical_assert: forall C Γ p,
      peval C Γ p true ->
      seval C Γ (SLogicalassert p) C.(M) C.(wf)
  | S_seq: forall C Γ s1 s2 M2 Wf2 M3 Wf3,
      seval C Γ s1 M2 Wf2 ->
      seval {|E:=C.(E);M:=M2;wf:=Wf2|} Γ s2 M3 Wf3 ->
      seval C Γ (SSeq s1 s2) M3 Wf3
  .
  
End Semantics.
