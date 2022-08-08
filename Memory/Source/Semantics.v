Require Import Arith ZArith Lia List Structures.Equalities.

From Vrac.Lib Require Import Tactics Option Eqb Error.
From Vrac.Memory Require Import MemoryType ExecutionMemoryModel Context.
From Vrac.Common Require Import Syntax Semantics.
From Vrac.Source Require Import Syntax.

Module Semantics(V : DecidableType)(B: Eqb.EQB)
  (Import EMM: ExecutionMemoryModel B)
  (Import Ctx: Context.SIG V B EMM)
  (Import CStx: Common.Syntax.SIG V)
  (Import Stx: Source.Syntax.SIG V CStx)
  (CSem: Common.Semantics.SIG V B EMM Ctx CStx).

  Import CStx.Types CStx.Expr Stx.Term Stx.Pred Stx.Stmt CSem.

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
      EMM.load((mtype τ), C.(M), b, δ) = ⎣v⎦ ->
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
  
  (* TODO: explanation wrt. to the companion paper. *)
  Inductive sseval : forall (C: context) (Γ: type_env) (s: stmt) (M2: mem)
                      (Invariant: forall x b, C.(E) x = ⎣b⎦ -> M2 ⊨ b), Prop :=
    
  | S_skip: forall C Γ,
      sseval C Γ SSkip C.(M) C.(wf)
                                             
  | S_assign: forall C Γ e1 e2 τ v b δ M2
      (Hstore: store(mtype τ, C.(M), b, δ, v) = ⎣M2⎦),
      Expr.check_type Γ e1 = Ok τ ->
      Expr.check_type Γ e2 = Ok τ ->
      eeval C Γ e2 v ->
      lveval C Γ e2 (b,δ) ->
      sseval C Γ (SAssign e1 e2) M2 (wf_after_store Hstore)

  | S_malloc: forall C Γ e1 e2 τ n b δ b' M2 M3
                (Halloc: alloc(C.(M), Z.to_nat n) = (b', M2))
                (Hstore: store(mtype (TPtr τ), M2, b, δ, Ptr(b',0%Z)) = ⎣M3⎦),
      Expr.check_type Γ e1 = Ok (TPtr τ) ->
      eeval C Γ e2 (Int n) ->
      lveval C Γ e1 (b,δ) ->
      sseval C Γ (SMalloc e1 e2) M3 (wf_after_malloc Halloc Hstore)

  | S_free: forall C Γ e b M2
              (Hfree: free(C.(M), b) = ⎣M2⎦)
              (Him: forall x, C.(E) x <> ⎣b⎦),
      eeval C Γ e (Ptr(b, 0%Z)) ->
      sseval C Γ (SFree e) M2 (wf_after_free Hfree Him)

  | S_logical_assert: forall C Γ p,
      peval C Γ p true ->
      sseval C Γ (SLogicalassert p) C.(M) C.(wf)
                                             
  | S_seq: forall C Γ s1 s2 M2 Wf2 M3 Wf3,
      sseval C Γ s1 M2 Wf2 ->
      sseval {|E:=C.(E);M:=M2;inj:=C.(inj);wf:=Wf2|} Γ s2 M3 Wf3 ->
      sseval C Γ (SSeq s1 s2) M3 Wf3

  | S_if_false: forall C Γ e s1 s2 M2 Wf2,
      eeval C Γ e (Int 0%Z) ->
      sseval C Γ s2 M2 Wf2 ->
      sseval C Γ (SIf e s1 s2) M2 Wf2

  | S_if_true: forall C Γ e s1 s2 M1 Wf1 n,
      eeval C Γ e (Int n) ->
      n <> 0%Z -> 
      sseval C Γ s1 M1 Wf1 ->
      sseval C Γ (SIf e s1 s2) M1 Wf1

  | S_while_false: forall C Γ e s,
      eeval C Γ e (Int 0%Z) ->
      sseval C Γ (SWhile e s) C.(M) C.(wf)

  | S_while_true: forall C Γ e s n M2 Wf2 M3 Wf3,
      eeval C Γ e (Int n) ->
      n <> 0%Z ->
      sseval C Γ s M2 Wf2 ->
      sseval {|E:=C.(E);M:=M2;inj:=C.(inj);wf:=Wf2|} Γ (SWhile e s) M3 Wf3 -> 
      sseval C Γ (SWhile e s) M3 Wf3

  | S_let: forall C1 Γ x τ s C2 M3 Wf3 M4
     (Hdom: C1.(E) x = ϵ)
     (Halloc: C2 = alloc_var C1 x (sizeof(mtype τ)))
     (Hdealloc: ⎣M4⎦ = dealloc_var {|E:=C2.(E);M:=M3;inj:=C2.(inj);wf:=Wf3|} x),
      sseval C2 Γ s M3 Wf3 ->
      sseval C1 Γ (SLet x τ s) M4 (wf_after_alloc_dealloc_var Hdom Halloc Hdealloc)
  .
  
End Semantics.
