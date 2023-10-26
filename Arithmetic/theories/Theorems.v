Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import RAC.Semantics.
Require Import RAC.Translation.
Require Import  Strings.String.
From Coq Require Import ZArith.ZArith.

Open Scope utils_scope.
Open Scope definition_scope.


(* Properties of the semantics *)

Definition _no_env_mpz_aliasing (env : Ω) : Prop := forall v v' l l',  (fst env) v = Some (VMpz l)  /\ (fst env) v' = Some (VMpz l') -> l <> l'.

Definition _no_mem_aliasing {S T : Set} (stmt_sem : @stmt_sem_sig S T)  : Prop := forall (exp_sem:@exp_sem_sig T)  funs procs env mem s env' mem', 
    stmt_sem funs procs env mem s env' mem' -> _no_env_mpz_aliasing env -> _no_env_mpz_aliasing env'.

Fact no_mem_aliasing_gen { S T : Set} : 
    forall exp_sem stmt_sem, 
    @_no_mem_aliasing S T stmt_sem ->  @_no_mem_aliasing S T (@generic_stmt_sem S T exp_sem stmt_sem).
Proof with auto with rac_hint.
    intros exp_sem stmt_sem H e funs procs env mem s env' mem' Hderiv Hnoalias. 
    induction Hderiv ; auto ; intros v v' l l'[Hns1 Hns2] ; 
     unfold _no_env_mpz_aliasing in Hnoalias ;specialize Hnoalias with v v' l l' ; apply Hnoalias ; simpl in *.
Admitted.

Fact eq_env_partial_order :  forall e e' v z, e ⊑ e' ->  z <> UInt /\ z <> UMpz -> (fst e) v = Some z -> (fst e') v = Some z.
Proof.
    intros. destruct H with v ; try assumption ; try rewrite H2 in H1 ; try injection H1 as Eq ; subst ; now try assumption.
Qed.

Fact sym_env_cond : forall env env', 
(forall v, (dom (fst env) - dom (fst env')) v ) -> (env ⊑ env') -> (env' ⊑ env).

Proof.
    intros env env' H rel v ; destruct H with v as [Hin Hnotin] ; destruct Hnotin ; destruct rel with v.
    - now exists n. 
    - now exists n. 
    - destruct H1.
        + now exists UInt. 
        + destruct H1. now exists x. 
    - destruct H1.
        + now exists UMpz.
        + destruct H1. now exists x.
    - destruct Hin. destruct env. simpl in *. congruence.
Qed.

Corollary sym_env_cond_mem : forall (env : Ω) env' mem mem', 
(forall v, (dom (fst env) - dom (fst env')) v ) -> (env,mem) ⊑ (env',mem') ->  (env',mem) ⊑ (env,mem').
Proof.
    intros. split. apply sym_env_cond ; easy. now destruct H0.
Qed.




Corollary eq_env_partial_order_add :  forall e e' v v' z z',  e ⊑ e' ->  z <> UInt /\ z <> UMpz -> v <> v'-> (fst e) v = Some z -> ((fst e'){v'\z'}) v = Some z.
Proof.
    intros [v l] [v' l'] var var' z z' Hrel Hnundef Hneq H. 
    pose proof (eq_env_partial_order (v,l) (v',l') var z Hrel Hnundef H).
    pose proof (p_map_not_same v' var var' z' Hneq). simpl in *. congruence.
Qed.


Fact eq_mem_partial_order :  
    forall mem mem' z l, mems_partial_order mem mem' -> z <> None ->  
    mem l = z ->  mem' l = z.
Proof.
    intros. destruct z.
    - edestruct H; eauto.
    - contradiction.
Qed.



Fact env_partial_order_add : forall Ω₀ Ω₀', Ω₀ ⊑ Ω₀' -> 
    (forall var' z, (((fst Ω₀) {var' \ z}, snd Ω₀)) ⊑  (((fst (Ω₀')) {var' \ z}, snd Ω₀'))).
Proof.
    intros [v l][v' l'] H x z var. destruct (string_dec x var) as [Heq|Hneq].
    - subst. simpl. specialize (H var). induction z.
        + apply EsameInt with n; apply p_map_same.
        + apply EsameMpz with n ; apply p_map_same.
        + apply EundefInt; simpl.
            ++ apply p_map_same.
            ++ left. apply p_map_same.
        + apply EundefMpz ; simpl.
            ++ apply p_map_same.
            ++ left. apply p_map_same.
    - apply not_eq_sym in Hneq. epose proof (p_map_not_same v var x ?[z] Hneq) as H0. simpl. remember (v var) as res. destruct res as [z'|]. induction z'.
        + apply EsameInt with n ; simpl.
            ++ apply H0.
            ++ pose proof (p_map_not_same_eq v var x z (Some (VInt n)) Hneq ). destruct H1 as [H1 _]. specialize (H1 H0).
                epose proof (eq_env_partial_order_add  _ _ _ _ _ _ H).  assert (VInt n <> UInt /\ VInt n <> UMpz) as Neq. easy.
                specialize (H2 Neq Hneq H1). apply H2.
        + apply EsameMpz with n; simpl.
            ++ apply H0.
            ++ pose proof (p_map_not_same_eq v var x z (Some (VMpz n)) Hneq ). destruct H1 as [H1 _]. specialize (H1 H0).
                epose proof (eq_env_partial_order_add  _ _ _ _ _ _ H).  assert (VMpz n <> UInt /\ VMpz n <> UMpz) as Neq. easy.
                specialize (H2 Neq Hneq H1). apply H2.

        + apply EundefInt ;subst ;simpl.
            ++ apply H0.
            ++ destruct H with var ; pose proof (p_map_not_same_eq v' var x z) as Hres; simpl in *; try congruence.
                +++ destruct H2.
                    ++++ specialize (Hres  (Some UInt) Hneq). left. now apply Hres.
                    ++++ destruct H2 as [x0]. specialize (Hres  (Some (VInt x0)) Hneq). right. exists x0. now apply Hres.

        + apply EundefMpz ; subst ; simpl.
            ++ apply H0.
            ++ destruct H with var ; pose proof (p_map_not_same_eq v' var x z) as Hres; simpl in * ; try congruence.
                +++ destruct H2.
                    ++++ specialize (Hres  (Some UMpz) Hneq). left. now apply Hres.
                    ++++ destruct H2 as [x0]. specialize (Hres  (Some (VMpz x0)) Hneq). right. exists x0. now apply Hres.
        + now apply Enone.
Qed.

Fact mems_partial_order_add : forall M₀ M₀', mems_partial_order M₀ M₀' -> 
    (forall l mi, mems_partial_order ((M₀) {l \ mi}) ((M₀') {l \ mi})).
Proof.
    intros mem mem' H l mi. intros l' i H1. destruct (loc_eq_dec l' l).
    - subst. pose proof (p_map_same mem l mi). rewrite H0 in H1. injection H1 as eq. subst.  apply p_map_same.
    - pose proof (p_map_not_same mem l' l mi n). rewrite H0 in H1. apply p_map_not_same_eq ; auto.
Qed.


Fact env_same_ty : forall  (Ω Ω' : Ω) v t, Ω ⊑ Ω' -> t <> None -> type_of_value (fst Ω v) = t -> type_of_value (fst Ω' v) = t.
Proof.
    intros. 
    match goal with | IncRel : _ ⊑ _ |- _ =>  destruct IncRel with v ; subst end ; 
    match goal with 
    | L : fst Ω v = _,  R : fst Ω' v = _  |- _ => now rewrite L,R 
    | L : fst Ω v = _,  R : fst Ω' v = _ \/ _ |- _ => destruct R as [SomeUInt| [ n Some_n ]]; [now rewrite L,SomeUInt | now rewrite L,Some_n] 
    | L : _ = None,  Contra : _ <> None |- _ =>  now rewrite L in Contra
    end.
Qed.

Open Scope generic_sem_scope.

Definition _determinist_exp_eval {T : Set} (exp_sem : @exp_sem_sig T) : Prop := 
    forall e env mem v,  exp_sem env mem e v ->  (forall v', exp_sem env mem e v' -> v = v')
.

Fact determinist_exp_eval {T : Set}: 
forall exp_sem, _determinist_exp_eval exp_sem -> _determinist_exp_eval (@generic_exp_sem T exp_sem).
Proof.
    intros exp_sem ext_inj. unfold _determinist_exp_eval. intros e. induction e ; intros ; inversion H ; inversion H0 ; subst ; try easy.
    5,6:
        apply IHe1 with (v:=(z ⁱⁿᵗ z_ir)) (v':=(z0 ⁱⁿᵗ z_ir0)) in H11 ; [|assumption] ; injection H11 as eqz ;
        apply IHe2 with (v:=(z' ⁱⁿᵗ z'_ir)) (v':=(z'0 ⁱⁿᵗ z'_ir0)) in H13; [|assumption] ;  injection H13 as eqz' ; subst ; now rewrite H14 in H7.
    - f_equal. now apply Int.mi_eq. 
    - congruence.
    - destruct ty. easy. 1,2: apply ext_inj in H1 ; now apply H1 in H4.
    - f_equal. apply Int.mi_eq. simpl. f_equal.
        + apply IHe1 with (v:=(z ⁱⁿᵗ z_ir)) (v':=(z0 ⁱⁿᵗ z_ir0)) in H13; [|assumption]. now injection H13. 
        + apply IHe2 with (v:=(z' ⁱⁿᵗ z'_ir)) (v':=(z'0 ⁱⁿᵗ z'_ir0)) in H14; [|assumption]. now injection H14.
Qed.

Fact _determinist_c_exp_eval : _determinist_exp_eval Empty_exp_sem.
Proof. easy. Qed.

Definition determinist_c_exp_eval := determinist_exp_eval Empty_exp_sem _determinist_c_exp_eval.

Fact _determinist_gmp_exp_eval :  _determinist_exp_eval _gmp_exp_sem.
Proof.
    unfold _determinist_exp_eval. intros e. induction e ; intros env mem v H v' H0. inversion H ; inversion H0 ; subst.
    - inversion H ; inversion H0 ; subst ; try easy. rewrite H3 in H8. f_equal. now injection H8.
    - inversion H.
    - inversion H.
Qed.

Definition determinist_gmp_exp_eval := determinist_exp_eval _gmp_exp_sem _determinist_gmp_exp_eval.


Definition _determinist_stmt_eval {S T : Set} (exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) : Prop := 
    @_determinist_exp_eval T exp_sem  -> 
    forall funs procs s env mem env' mem',  stmt_sem funs procs env mem s env' mem' ->  (forall env'' mem'', stmt_sem funs procs env mem s env'' mem'' -> env' = env'' /\ mem' = mem'').


Fact Forall2_same_zargs { T : Set} : forall env mem eargs zargs zargs0  exp_sem, 
    _determinist_exp_eval exp_sem
    -> List.Forall2 (@generic_exp_sem T exp_sem env mem) eargs zargs 
    -> List.Forall2 (@generic_exp_sem T exp_sem env mem) eargs zargs0 -> zargs = zargs0.
Proof.
    intros env mem eargs zargs zargs0 exp H  Hderiv. generalize dependent zargs0. induction Hderiv ; intros zargs0 H1.
    - now inversion H1.
    - destruct zargs0. inversion H1. apply List.Forall2_cons_iff in H1 as [H1 Hderiv2].
        apply determinist_exp_eval in H0 ; [|assumption]. apply H0 in H1. subst. f_equal. clear H0.
        now apply IHHderiv in Hderiv2.
Qed.

Fact determinist_stmt_eval {S T : Set}: 
    forall  exp_sem stmt_sem, 
    @_determinist_stmt_eval S T exp_sem stmt_sem -> 
    _determinist_stmt_eval exp_sem (@generic_stmt_sem S T exp_sem stmt_sem).
Proof with auto. 
    intros exp_sem stmt_sem Hds Hde funs procs s env mem env' mem' Hderiv. induction Hderiv ; intros.
    - inversion H... easy.
    - inversion H1 ; subst. split... repeat f_equal. apply determinist_exp_eval in H0... easy.
    - inversion H1 ; subst...  apply determinist_exp_eval in H7... destruct H. apply H7 in H. now symmetry in H. easy.
    - inversion H1 ; subst... apply determinist_exp_eval in H... destruct H7. apply H in H2. now symmetry in H2. easy.
    - inversion H0... easy.
    - inversion H1 ; subst... apply IHHderiv in H4 as [Eq1 Eq2]. subst. apply IHHderiv0 in H7. now subst. easy.
    - inversion H5 ; subst. 
        + (* same args, same body *) 
            rewrite H11 in H0. injection H0 as H0. subst.
            (* same args eval *) 
            assert (zargs = zargs0) by auto using (@Forall2_same_zargs T env mem eargs zargs zargs0 exp_sem). 
            subst. apply IHHderiv in H15 as [Eq1 Eq2]. subst. rewrite H4 in H17. injection H17 as H17. now subst.
        + easy.
    - inversion H3...
        + subst. split... rewrite H7 in H0. injection H0 as Eq1. subst. 
            assert (zargs = zargs0) by auto using (@Forall2_same_zargs T env'' mem eargs zargs zargs0 exp_sem). subst. 
            now apply IHHderiv in H11.
        + easy.
    - inversion H0 ; subst... apply determinist_exp_eval in H... apply H in H5. subst. now subst. easy.
    - inversion H1... easy.
    - destruct s; try easy. inversion H0. subst. unfold _determinist_stmt_eval in Hds. eapply Hds... apply H. apply H1.
Qed.

Fact _determinist_gmp_stmt_eval :  _determinist_stmt_eval _gmp_exp_sem _gmp_stmt_sem.
Proof with auto.
    intros Hde funs procs s. induction s ; intros ; inversion H ; inversion H0; subst ; split ; try easy ; try now destruct bop.
    -  injection H6 as H6. subst. rewrite H2 in H7. apply determinist_gmp_exp_eval in H3. apply H3 in H8. congruence.
    - injection H7 as H7. subst.  congruence.
    - injection H6 as H6. subst. apply determinist_gmp_exp_eval in H2. apply H2 in H7. injection H7 as Eq2. subst. rewrite H3 in H8. 
        injection H8 as Eq2. subst. f_equal. f_equal. f_equal. f_equal. now apply Int.mi_eq.
    - injection H6 as H6. subst. congruence.
    -  injection H9 as H9. subst. repeat f_equal. destruct H6 as [Sup [Inf Eq]]. destruct H14 as [Sup2 [Inf2 Eq2]].
        apply determinist_gmp_exp_eval in H3. apply H3 in H11. clear H3.
        apply determinist_gmp_exp_eval in H2. apply H2 in H10. clear H2. injection H10 as H10. injection H11 as H11. subst. rewrite H4 in H12. rewrite H5 in H13.
        injection H12 as H12. injection H13 as H13. subst. destruct (Z.lt_trichotomy lx0 ly0) as [Hinf | [Heq | Hsup]].
            + apply Inf in Hinf as X. apply Inf2 in Hinf as X2. congruence.
            + apply Eq in Heq as X. apply Eq2 in Heq as X2. congruence.
            + apply Z.lt_gt in Hsup. apply Sup in Hsup as X. apply Sup2 in Hsup as X2. congruence.

    - unfold op in H9. destruct bop,bop0 ; try easy.
        1,2,3,4: (injection H9 as H9; subst; apply determinist_gmp_exp_eval in H2; apply H2 in H10; 
            apply determinist_gmp_exp_eval in H4; apply H4 in H12; congruence).
Qed.


Definition determinist_gmp_stmt_eval := determinist_stmt_eval _gmp_exp_sem _gmp_stmt_sem _determinist_gmp_stmt_eval.


Definition _weakening_of_expression_semantics {T : Set} (exp_sem : @exp_sem_sig T) : Prop := 
    forall e env mem (x:𝕍), 
    exp_sem env mem e x <-> (forall env' mem',  (env,mem) ⊑ (env',mem') -> exp_sem env' mem' e x).


Lemma weakening_of_expression_semantics {T : Set} : 
    forall exp_sem, 
    (_weakening_of_expression_semantics exp_sem )
    ->
    _weakening_of_expression_semantics (@generic_exp_sem T exp_sem)
.
Proof with (eauto using refl_env_mem_partial_order with rac_hint).
    split...
    - intro Hderiv. induction Hderiv; intros...
        + constructor. eapply eq_env_partial_order... easy. easy.
        + constructor. specialize (H e env mem v). destruct e... destruct ty.
            ++ contradiction.
            ++ apply H...
            ++ apply H...
Qed.

Fact _weakening_of_c_expression_semantics : _weakening_of_expression_semantics Empty_exp_sem. 
Proof.
    unfold _weakening_of_expression_semantics. intros. split ; unfold Empty_exp_sem.
    - intros [].
    - intro H. apply H with env mem... apply refl_env_mem_partial_order.
Qed.

Definition weakening_of_c_expression_semantics := 
    weakening_of_expression_semantics Empty_exp_sem _weakening_of_c_expression_semantics.
Close Scope generic_sem_scope.

Open Scope gmp_sem_scope.
Lemma _weakening_of_gmp_expression_semantics : 
    _weakening_of_expression_semantics _gmp_exp_sem
.
Proof with (eauto with rac_hint; try easy).
    split.
    - intro H. inversion H. subst. intros. apply GMP_E_Var with z; destruct H2 as [relEnv memEnv]. 
        + eapply eq_env_partial_order...
        + eapply eq_mem_partial_order... 
    - intros. specialize H with env mem. now apply H.
Qed.

Definition weakening_of_gmp_expression_semantics := 
    weakening_of_expression_semantics _gmp_exp_sem _weakening_of_gmp_expression_semantics.
Close Scope gmp_sem_scope.


Open Scope generic_sem_scope.

Definition _weakening_of_statement_semantics_1  {S T : Set} (exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) := 
    _weakening_of_expression_semantics exp_sem ->
    _determinist_stmt_eval exp_sem stmt_sem -> 
    forall (funs : @𝓕 S T) (procs : @𝓟 S T) Ω₀ M₀ s Ω₁ M₁,
    stmt_sem funs procs Ω₀ M₀ s Ω₁ M₁ <->
    ( forall Ω₀' M₀', (Ω₀ , M₀) ⊑ (Ω₀', M₀') ->
    exists Ω₁' M₁', (Ω₁ , M₁) ⊑ (Ω₁', M₁') /\ stmt_sem funs procs Ω₀' M₀' s Ω₁' M₁').
    

Lemma weakening_of_statement_semantics_1 {S T : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_statement_semantics_1 exp_sem stmt_sem 
    -> _determinist_stmt_eval exp_sem stmt_sem
    -> _weakening_of_statement_semantics_1 exp_sem (@generic_stmt_sem S T exp_sem stmt_sem)
.
Proof with eauto using refl_env_mem_partial_order,env_partial_order_add with rac_hint.
    intros exp_sem stmt_sem Hext_stmt Hext_d Hext_exp Hd funs procs Ω₀ M₀ s Ω₁ M₁. 
    pose proof (weakening_of_expression_semantics exp_sem Hext_exp) as exp_weak.
    split.
    - intro Hderiv. induction Hderiv ; intros Ω₀' M₀' [Henv Hmem].
        (* skip *)
        * exists Ω₀',M₀'... 
        
        (* assign *) 
        * exists ((fst Ω₀') {x \ z}, (snd Ω₀')) , M₀'. split.
            + split...
            + apply S_Assign.
                *** now apply env_same_ty with env. 
                *** rewrite (exp_weak e) in H0. specialize (H0 Ω₀' M₀'). apply H0...


        (* if true *)
        * destruct H. destruct (IHHderiv Ω₀' M₀') as [env_s [mem_s [[Henv2 Hmem2] Hderiv2]]]... exists env_s, mem_s. intros . split...
            apply S_IfTrue with z. split...
            rewrite  (exp_weak e) in H... apply Hderiv2...
        (* if false *)
        * destruct (IHHderiv Ω₀' M₀') as [env_s [mem_s [[Henv2 Hmem2] Hderiv2]]]... exists env_s, mem_s. split...
            apply S_IfFalse...
            rewrite  (exp_weak e) in H... 


         (* while *)
        * destruct (IHHderiv Ω₀' M₀') as [env_s [mem_s [[Henv2 Hmem2] Hderiv2]]]... exists env_s, mem_s.
            intros. split... 


        (* c seq *)
        *   destruct IHHderiv with Ω₀' M₀' as [I1env [I1mem [I1Hrel I1Hderiv]]]...
            destruct IHHderiv0 with I1env I1mem as [I2env [I2mem [I2Hrel I2Hderiv]]]... 

        (* f call *)
         * specialize IHHderiv with (p_map_addall (H:=eqdec_v) ⊥ xargs zargs, ⊥)  M₀'. destruct IHHderiv as [env_s [mem_s [Hrel Hderiv2]]].
            + now split.
            + eexists ?[env],?[mem]. split.
                ++ instantiate (env:=((fst Ω₀') {c \ z}, snd Ω₀')). instantiate (mem:=mem_s). split... easy. 
                ++ eapply S_FCall... 
                    +++ epose proof (List.Forall2_impl (R1:=generic_exp_sem env mem) (generic_exp_sem Ω₀' M₀')) as Hforall. destruct Hforall with eargs zargs... intros.
                        apply exp_weak with env mem...
                    +++ admit . (* return value must be untouched because it isn't in the variables visible by the user *)

        (* p call *)
        * specialize IHHderiv with (p_map_addall (H:=eqdec_v) ⊥ xargs zargs, ⊥)  M₀'. destruct IHHderiv as [env_s [mem_s [Hrel Hderiv2]]].
            + now split... 
            + repeat eexists... 
                ++ destruct Hrel...
                ++ eapply S_PCall ...
                +++ epose proof (List.Forall2_impl (R1:=generic_exp_sem env mem) (generic_exp_sem Ω₀' M₀')) as Hforall. destruct Hforall with eargs zargs... intros.
                    apply exp_weak with env mem...

        (* return *)
        * exists ((fst Ω₀') {resf \ z}, snd Ω₀'), M₀'. split.
            + split...
            + apply S_Return... apply (exp_weak e env mem z)...

        (* assert *)
        * exists Ω₀', M₀'. split... apply S_PAssert with z...
            apply (exp_weak e env mem z)...

        (* other cases *)
        * unfold _weakening_of_statement_semantics_1 in *. specialize (Hext_stmt Hext_exp Hext_d funs procs env mem s env' mem').
            destruct s... 
            apply Hext_stmt with Ω₀' M₀' in H. destruct H as [env'' [mem'' [Hrel2 Hderiv]]]... easy.
                
    - intros H. specialize (H Ω₀ M₀ (refl_env_mem_partial_order Ω₀ M₀))...
        destruct H as [Ω₁' [M₁' [Hrel Hderiv ]]]... (* ??? *) 
Admitted.


Fact _weakening_of_c_statements_semantics_1 : _weakening_of_statement_semantics_1 Empty_exp_sem Empty_stmt_sem. 
Proof.
    unfold _weakening_of_statement_semantics_1. intros. split; unfold Empty_stmt_sem.
    - intros [].
    - intro H2. destruct H2 with Ω₀ M₀.
        + apply refl_env_mem_partial_order.
        + destruct H1 as [_ [_ []]]. 
Qed.


Lemma _weakening_of_gmp_statements_semantics : 
    _weakening_of_statement_semantics_1 _gmp_exp_sem _gmp_stmt_sem
.
Proof with eauto using eq_env_partial_order, eq_mem_partial_order,refl_env_mem_partial_order with rac_hint ; try easy.
    intros Hweak Hdet funs procs Ω₀ M₀ s Ω₁ M₁. split.
    - intro Hderiv. induction Hderiv; intros Ω₀' M₀' [Henv Hmem] ;
        pose (fun y => weakening_of_gmp_expression_semantics y Ω₀ M₀) as weak_exp ; specialize weak_exp.  

        * exists Ω₀',(M₀') {a \ (z) ̇}. split.
            + split... intro n. apply (mems_partial_order_add M₀ M₀' Hmem a (Int.to_z z)). 
            + apply S_set_i. eapply eq_env_partial_order... apply weak_exp...

        * exists Ω₀', M₀' {a \ z}. split.
            + split... intro n0.  apply (mems_partial_order_add M₀ M₀' Hmem a). 
            + apply S_set_z with n.
                ++ eapply eq_env_partial_order...
                ++ eapply eq_env_partial_order...
                ++ apply (eq_mem_partial_order M₀ M₀')...

        * inversion H0. subst. eexists (((fst Ω₀') {x \ VInt (Int.mkMI z  ir)}, snd Ω₀')), M₀'... split.
            + split... pose env_partial_order_add...
            + apply S_get_int with v... apply weak_exp...
        
        * exists Ω₀',M₀' {a \ z}. split. 
            + split... apply (mems_partial_order_add M₀ M₀' Hmem a z). 
            + constructor... eapply eq_env_partial_order...

        * inversion H. inversion H4. inversion H0. inversion H11. subst. 
            eexists ((fst Ω₀') {c \ b}, snd Ω₀'),M₀'. split.
            ** split... pose env_partial_order_add...
            ** apply S_cmp with vx vy lx ly...
                + constructor. apply GMP_E_Var with z.
                    ++ eapply eq_env_partial_order...
                    ++ apply (eq_mem_partial_order M₀ M₀')...
                + constructor. apply GMP_E_Var with z0.
                    ++ eapply eq_env_partial_order...
                    ++ apply (eq_mem_partial_order M₀ M₀')...
        
        * eexists Ω₀', M₀' {lr \ ⋄ (□ bop) z1 z2}. split.
            ** split... intro n. apply mems_partial_order_add...
            **  apply S_op with vx vy.
                + apply weak_exp...
                + apply (eq_mem_partial_order M₀ M₀')...
                + apply weak_exp...
            + apply (eq_mem_partial_order M₀ M₀')...
            + eapply eq_env_partial_order...
    
    - intro H. specialize (H Ω₀ M₀ (refl_env_mem_partial_order Ω₀ M₀))...
        destruct H as [Ω₁' [M₁' [Hrel Hderiv ]]]... induction Hderiv.
        + (* non sense ... *)
Admitted.

Definition weakening_of_gmp_statements_semantics := 
    weakening_of_statement_semantics_1 _gmp_exp_sem _gmp_stmt_sem _weakening_of_gmp_statements_semantics.
(* 2 *)


Definition _weakening_of_statement_semantics_2  {S T : Set} (exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) := 
    
    forall (funs : @𝓕 S T) (procs : @𝓟 S T) Ω₀ Ω₀' M₀ M₀' s Ω₁ M₁,
    _determinist_exp_eval exp_sem ->
    _weakening_of_expression_semantics exp_sem ->
    stmt_sem funs procs Ω₀ M₀ s Ω₁ M₁ /\ (Ω₀, M₀) ⊑ (Ω₀', M₀')  ->
    (
        forall Ω₁' M₁',
        stmt_sem funs procs Ω₀' M₀' s Ω₁' M₁'->
        (forall (v:𝓥),v ∉ fst Ω₀ -> fst Ω₀' v = fst Ω₁' v) 
        /\
        (forall (x:location) (v:𝓥), (fst Ω₀ v) <> Some (VMpz x) -> M₀' x = M₁' x)
    ).
    

Lemma weakening_of_statement_semantics_2 {S T : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_statement_semantics_2 exp_sem stmt_sem 
    -> _weakening_of_statement_semantics_2 exp_sem (@generic_stmt_sem S T exp_sem stmt_sem)
.
Proof with auto with rac_hint.
    intros exp_sem stmt_sem ext_stmt_weak funs procs Ω₀ Ω₀' M₀ M₀' s Ω₁ M₁ ext_exp_deter ext_exp_weak  [Hderiv1 Hrel] Ω₁' M₁' Hderiv2 .
    pose proof (weakening_of_expression_semantics exp_sem ext_exp_weak) as exp_weak.
    unfold _weakening_of_expression_semantics in exp_weak.
    unfold _weakening_of_statement_semantics_2 in ext_stmt_weak.
    
    induction Hderiv1 ; inversion Hderiv2 ; subst ; try easy...
    
    (* assign *)
    - split... simpl. intros. destruct (string_dec x v).
        + exfalso.  subst. unfold "∉" in H1. destruct (fst env v).
            ++ edestruct H1...
            ++ discriminate H.
        + symmetry. apply p_map_not_same...

    (* if false *)
    - apply IHHderiv1... destruct H. specialize (exp_weak e env mem z). rewrite exp_weak in H. specialize (H Ω₀' M₀' Hrel). 
            apply determinist_exp_eval in H. apply H in H6. now subst. assumption.

    (* if true *)
    -  destruct H6. specialize (exp_weak e env mem zero). rewrite exp_weak in H. specialize (H Ω₀' M₀' Hrel).
            apply determinist_exp_eval in H. apply H in H1. now subst. assumption.

    (* seq *)
    - apply IHHderiv1... admit.
    (* fcall *)
    - admit.
    (* pcall *)
    - split... rewrite H6 in H0. injection H0 as H0. subst. admit.

    (* return *)
    - split ; intros... simpl. unfold "∉" in H0.  destruct (string_dec resf v).
        + apply exp_weak with (env':=Ω₀') (mem':=M₁') in H...
            apply determinist_exp_eval in H... apply H in H4. subst. admit. (* can't happen *)
        +  symmetry. apply p_map_not_same...
            
    (* assert *)
    - destruct s ; try easy. inversion Hderiv2. subst. eapply ext_stmt_weak with ( Ω₀:=env) ( M₀:=mem) (Ω₁:=env') (M₁:=mem') in H0...
Admitted.


(* 3 *)
Definition _weakening_of_statement_semantics_3  {S T : Set} (stmt_sem : @stmt_sem_sig S T) := 
    forall funs procs Ω₀ M₀  s Ω₁ M₁,
    stmt_sem funs procs Ω₀ M₀ s Ω₁ M₁ -> 
    (
        forall Ω₀' M₀', (Ω₀', M₀') ⊑ (Ω₀, M₀) ->
        (
            (forall v, (dom (fst Ω₀) - dom (fst Ω₀')) v /\ ~ List.In v (stmt_vars s))
            /\
            (forall x v, (dom M₀ - dom M₀') x -> (fst Ω₀) v = Some (VMpz x) /\ ~ List.In v (stmt_vars s))
        ) ->

        exists Ω₁' M₁', stmt_sem funs procs Ω₀' M₀' s Ω₁' M₁'
    ).

Lemma weakening_of_statement_semantics_3 {S T : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_expression_semantics exp_sem
    -> _weakening_of_statement_semantics_3 stmt_sem 
    -> _weakening_of_statement_semantics_3 (@generic_stmt_sem S T exp_sem stmt_sem)
.

Proof with auto with rac_hint.
    intros exp_sem stmt_sem ext_exp_weak ext_stmt_weak funs procs Ω₀ M₀ s Ω₁ M₁ Hderiv Ω₀' M₀' Hrel [Henv Hmem].  induction Hderiv.
    (* skip *)
    - exists Ω₀', M₀'. constructor.
    (* assign *)
    - destruct Henv with x. destruct H1. exists ((fst Ω₀'){x\z}, snd  Ω₀'). exists  M₀'. constructor.
        + apply env_same_ty with (Ω':=Ω₀') in H ; [easy|idtac|easy]. destruct Hrel ;  apply sym_env_cond ; [|easy].
            intros v. destruct Henv with v... admit.
        + unfold not in H2. simpl in H2. destruct H2...
    (* if true *)
    - admit.
    (* if false *)
    - admit.
    (* while *)
    - admit.
    (* seq *)
    - admit.
    (* fcall *)
    - admit.
    (* pcall *)
    - admit.
    (* return *)
    - admit.
    (* assert *)
    - exists Ω₀'. exists M₀'. apply S_PAssert with z... admit.
    (* other cases *)
    - admit.
Admitted.


(* Proofs of structural properties of the translation *)

Lemma mpz_pointer_invariant : True. 
Proof.
auto.
Qed.

Lemma absence_of_aliasing : 
    forall (* program...*) z, type_of_value (Some z) = Some (T_Ext Mpz) -> True.
auto.
Qed.


(* Theorem absence_of_dangling_pointers :
    forall n (z:=VMpz n) (mem_state:𝓜) (var_env:Ωᵥ), 
        mem_state n <> ⊥ n <-> 
        exists x, var_env x = Some z /\
        ~(exists x', x <> x' -> var_env x <> Some z)
.
Admitted. *)



(* Proofs of the semantics of the macros *)

Fact Mpz_exp_is_var : forall e, exists x, ty e = Mpz -> e = C_Id x Mpz.
Proof. 
    intros. destruct e ; try now exists "z".
    exists var. intro H. unfold Definitions.ty in H. now rewrite H.
Qed.

Open Scope gmp_sem_scope.
Fact same_eval_env : forall Ω M x v (e : gmp_exp)  z, 
    ~ List.In x (exp_vars e) -> 
    Ω ⋅ M  |= e => z ->
    ( ((fst Ω){x\v},snd Ω) ⋅ M  |= e => z ).
Proof with try easy.
    intros. generalize dependent Ω.  generalize dependent z. induction e ; intros.
    - inversion H0 ; [constructor | easy]...
    - destruct ty ; inversion H0;  try specialize (H1 I)...
        * constructor. simpl. subst. apply Decidable.not_or_iff in H as [H _]. apply p_map_not_same_eq...
        * destruct t... inversion H1. subst. constructor. apply GMP_E_Var with z0... simpl.
            apply Decidable.not_or_iff in H as [H3 _]. apply p_map_not_same_eq... 

    - simpl in H.  rewrite List.in_app_iff in H. apply Decidable.not_or_iff in H. destruct H as [He1 He2].
        pose proof (IHe1 He1). pose proof (IHe2 He2). clear He1 He2 IHe1 IHe2. inversion H0... subst. 
        apply C_E_BinOpInt with z_ir z'_ir. now apply H. now apply H1.

    - simpl in H.  rewrite List.in_app_iff in H. apply Decidable.not_or_iff in H. destruct H as [He1 He2].
        pose proof (IHe1 He1). pose proof (IHe2 He2). clear He1 He2 IHe1 IHe2. inversion H0 ; try easy ; subst.
        * apply C_E_BinOpTrue with z0 z' z_ir z'_ir... now apply H. now apply H1.
        * apply C_E_BinOpFalse with z0 z' z_ir z'_ir... now apply H. now apply H1.
Qed.


Fact same_eval_mem : forall Ω M v l (e : gmp_exp)  z z', 
    ~ List.In v (exp_vars e) ->
    (fst Ω) v = Some (VMpz l) ->
    Ω ⋅ M |= e => z ->
    Ω ⋅ (M) {l \ z'} |= e => z.

Proof with try easy.
    intros. generalize dependent Ω.  generalize dependent z. induction e ; intros.
    - inversion H1... now apply C_E_Int.
    - destruct ty; inversion H1 ; subst...
        * now constructor.
        * destruct t... inversion H2. subst. constructor. apply GMP_E_Var with z0... 
            apply Decidable.not_or_iff in H as [H _]. unfold p_map. simpl in *. 
            destruct loc_eq_dec... subst. admit. (* need to show there is no aliasing *)

    - simpl in H.  rewrite List.in_app_iff in H. apply Decidable.not_or_iff in H. destruct H as [He1 He2].
        pose proof (IHe1 He1). pose proof (IHe2 He2). clear He1 He2 IHe1 IHe2. inversion H1... subst. 
        apply C_E_BinOpInt with z_ir z'_ir. now apply H. now apply H2.

    -  simpl in H.  rewrite List.in_app_iff in H. apply Decidable.not_or_iff in H. destruct H as [He1 He2].
        pose proof (IHe1 He1). pose proof (IHe2 He2). clear He1 He2 IHe1 IHe2. inversion H1 ; try easy ; subst.
        * apply C_E_BinOpTrue with z0 z'0 z_ir z'_ir... now apply H. now apply H2.
        * apply C_E_BinOpFalse with z0 z'0 z_ir z'_ir... now apply H. now apply H2.
Admitted.

Corollary same_eval_macro :  forall Ω M v l e z z', 
    ~ List.In v (exp_vars e) ->
    (fst Ω) v = Some (VMpz l) ->
    Ω ⋅ M |= e ⇝ z ->
    Ω ⋅ (M) {l \ z'} |= e ⇝ z.

Proof.
    intros. inversion H1.
    * constructor. apply same_eval_mem with v ; assumption.
    * apply M_Mpz with l0. subst.
        + apply same_eval_mem with v ; assumption.
        + subst. rewrite <- H3. apply p_map_not_same. inversion H2. destruct e ; try easy. destruct ty ; try easy.
            subst. inversion H4. subst. admit. (* need to show there is no aliasing *)
Admitted.

Lemma semantics_of_the_mpz_assgn_macro :
    forall funs procs e z Ω M v (y:location),
    Ω ⋅ M |= e ⇝ z ->
    (fst Ω) v = Some (VMpz y) ->
    gmp_stmt_sem funs procs Ω M (mpz_ASSGN v e) Ω M{y\z} 
.
Proof.
    intros. 
    unfold mpz_ASSGN. destruct (ty e) eqn:TY.
    - inversion H ; constructor.
        * now apply S_set_i.
        * inversion H1. subst. destruct e ; try easy ; destruct ty ; try easy.
    - unfold ty in TY. destruct e; try easy. subst. inversion H ; inversion H1 ; now inversion H1.
    - destruct t.
        * destruct H; destruct H ; try easy ; destruct e ; destruct ty ; try easy ; inversion H ; now subst. 
        * destruct e; try easy. inversion H.
            ** inversion H1 ; subst.
                + discriminate.
                + destruct ty ; try easy.
            ** inversion H1 ; subst. destruct ty ; try easy.
                inversion H4. constructor. now apply S_set_z with l.
Qed.

Lemma semantics_of_the_int_assgn_macro :
    forall funs procs e z (ir: Int.inRange z) Ω M v,
    Ω ⋅ M |= e ⇝ z ->
    type_of_value ((fst Ω) v) = Some C_Int ->
    gmp_stmt_sem funs procs Ω M (int_ASSGN v e) ((fst Ω){v\z ⁱⁿᵗ ir : 𝕍}, snd Ω)  M
.
Proof with eauto with rac_hint.
    intros. 
    unfold int_ASSGN. destruct e eqn:E.
    - inversion H. simpl.
        * apply S_Assign... subst. rewrite (x_of_z_to_z_is_x x ir). inversion H1 ; subst.
            ** constructor.
            ** constructor... 
        * now  inversion H1. 

    -  destruct ty ; simpl ; inversion H ; inversion H1 ; inversion H3 ; subst ; try easy.
        + apply S_Assign... rewrite x_of_z_to_z_is_x...
        + destruct t eqn:T.
            ++inversion H4. 
            ++ inversion H4 ; subst. constructor. simpl. apply S_get_int with l...
    
    - simpl ; constructor... inversion H ; inversion H1 ; subst...
        eapply C_E_BinOpInt with z_ir z'_ir ; (* apply H6. *) admit.
    -  simpl ; constructor... inversion H ; inversion H1 ; subst...
        + rewrite x_of_z_to_z_is_x. apply C_E_BinOpTrue with (z_ir:=z_ir) (z'_ir:=z'_ir)...
        (* apply H7. *) admit.
        (* apply H8*) admit.
        + rewrite x_of_z_to_z_is_x. apply C_E_BinOpFalse with (z_ir:=z_ir) (z'_ir:=z'_ir)...
        (* apply H7. *) admit.
        (* apply H8*) admit.
Admitted.

Lemma semantics_of_the_Z_assgn_macro_tint :
    forall funs procs z (ir: Int.inRange z) Ω M v,
    type_of_value ((fst Ω) v) = Some C_Int ->
    gmp_stmt_sem funs procs Ω M (Z_ASSGN C_Int v z) ((fst Ω){v\z ⁱⁿᵗ ir : 𝕍}, snd Ω) M
.
Proof.
    intros.  constructor ; auto with rac_hint.
Qed.

Lemma semantics_of_the_Z_assgn_macro_tmpz :
    forall funs procs y (z:ℤ) Ω M v,
    (fst Ω) v = Some (VMpz y) ->
    gmp_stmt_sem funs procs Ω M (Z_ASSGN Mpz v z) Ω M{y\z}
.
Proof with auto using BinaryString.Z_of_of_Z.
    intros. simpl. constructor. apply S_set_s...
Qed.


Lemma semantics_of_the_cmp_macro :
    forall funs procs (Ω:Ω) (M:𝓜) c e1 e2 v1 v2 z1 z2 l1 l2 a,
    type_of_value ((fst Ω) c) = Some C_Int ->
    Ω ⋅ M |= e1 ⇝ z1 ->
    Ω ⋅ M |= e2 ⇝ z2 ->
    (
        (a = VInt sub_one <-> Z.lt z1 z2 ) /\
        (a = VInt zero <-> z1 = z2) /\
        (a = VInt one <-> Z.gt z1 z2)
    ) -> 
    (fst Ω) v1 = Some (VMpz l1) /\ ( (fst Ω) v2 = Some (VMpz l2)) ->
    exists M', (forall v n, (fst Ω) v = Some (VMpz n) ->
    ~ ((fst Ω) v1 = (fst Ω) v) /\ ~ ((fst Ω) v2 = (fst Ω) v)  -> M n = M' n) -> 
    ~ List.In v1 (exp_vars e2) ->  (* not in paper proof *)
    l1 <> l2 ->  (* not in paper proof *)
    gmp_stmt_sem funs procs Ω M (CMP c e1 e2 v1 v2) ((fst Ω){c\a}, snd Ω) M'
    .

Proof with try easy ; auto with rac_hint ; unshelve eauto using Z.ltb_irrefl,Z.gtb_ltb,Z.ltb_lt with rac_hint; auto with rac_hint.
    intros. destruct H2 as (inf & eq & sup), H3.
    
    assert (NotInt : 
        exists M', (forall (v : 𝓥) n,
        fst Ω v = Some (VMpz n) ->
        fst Ω v1 <> fst Ω v /\ fst Ω v2 <> fst Ω v ->
        M n = M' n) ->
        ~ List.In v1 (exp_vars e2) ->  (* not in paper proof *)
        l1 <> l2 ->  (* not in paper proof *)
        gmp_stmt_sem funs procs Ω M <{(mpz_ASSGN v1 e1); (mpz_ASSGN v2 e2); <c = cmp (v1, v2)>}> ((fst Ω) {c \ a}, snd Ω)  M'
    ). {
        exists M{l2 \ z2, l1 \ z1}. intros VN Hv1NotIne2 Hl1Notl2.
        apply S_Seq with Ω M{l1\z1}.
        - apply semantics_of_the_mpz_assgn_macro...
        - apply S_Seq with Ω M{l2\z2,l1\z1}.  
            + apply semantics_of_the_mpz_assgn_macro... inversion H1.
                * subst. constructor. apply same_eval_mem with v1...
                * subst. econstructor. apply same_eval_mem with v1... rewrite <- H5. apply p_map_not_same. admit. (* need to show there is no aliasing *)
            + constructor. apply S_cmp with (vx:=l1) (vy:=l2) (lx:=z1) (ly:=z2)...
                * constructor. apply GMP_E_Var with z1. assumption. apply p_map_not_same_eq ; [easy|apply p_map_same] .
                * constructor. simpl. apply GMP_E_Var with z2. assumption. apply p_map_same.
                * apply p_map_not_same_eq;[ easy|apply p_map_same].
    }
    
     unfold CMP. destruct (ty e1) eqn:T1, (ty e2) eqn:T2 ; try apply NotInt ; clear NotInt.
         
     (* both ty(e1) = int and ty(e2) = int *)
     - inversion H0 ; inversion H1 ; try 
            match goal with 
            | Contra :  _ ⋅ _ |= _ => VMpz _ |- _ => 
                inversion Contra ; match goal with 
                | Contra : _gmp_exp_sem _ _ _ _ |- _ => inversion Contra ; now subst
                end
            end.
        exists M. intros _ _ _. destruct (Z.lt_trichotomy z1 z2) as [inf' | [ eq' | sup']].
        
        (* z1 < z2 *)
        * assert (cmp := inf'). apply <- inf in inf'. clear eq inf sup. rewrite <- H5, <-H7 in cmp.
            destruct x,x0. subst. apply S_IfTrue with one.
            + split... apply C_E_BinOpTrue with val val0 in_range in_range0. admit. admit. apply Z.ltb_lt. apply cmp.
            + constructor... eapply (C_E_BinOpInt Ω M 0 1 0 1)...

        (* z1 = z2 *)
        * assert (cmp := eq'). rewrite <- eq in eq'. clear eq inf sup. rewrite <- H5, <-H7 in cmp.
            destruct x,x0. apply Int.mi_eq in cmp. injection cmp as cmp. subst. constructor.
                + eapply C_E_BinOpFalse... admit. admit.
                + constructor... eapply C_E_BinOpFalse... admit. admit. 

        (* z1 > z2 *)
        * assert (cmp := sup').  apply Z.lt_gt in sup'. apply <- sup in sup'.  clear inf eq sup. rewrite <- H5, <- H7 in cmp.
          destruct x, x0. subst. constructor ; simpl in *.
            + eapply C_E_BinOpFalse... admit. admit.
            + apply S_IfTrue with one.
                ++  subst. split... apply C_E_BinOpTrue with val val0 in_range in_range0. admit. admit. simpl.  now apply Z.gtb_lt.
                ++  constructor...
Admitted.




Lemma semantics_of_the_binop_macro_int :
    forall funs procs (Ω:Ω) (M:𝓜) (op:fsl_binop_int) c r e1 e2 v1 v2 z1 z2 (ir: Int.inRange (⋄ (□ op) z1 z2) ) l1 l2 lr,
    type_of_value ((fst Ω) c) = Some C_Int ->
    Ω ⋅ M |= e1 ⇝ z1 ->
    Ω ⋅ M |= e2 ⇝ z2 ->
    let zr := ⋄ (□ op) z1 z2 in

    (fst Ω) v1 = Some (VMpz l1) /\  (fst Ω) v2 = Some (VMpz l2) /\ ( (fst Ω) r = Some (VMpz lr) ) ->
    exists M', (forall v n, (fst Ω) v = Some (VMpz n) ->
    ~ ((fst Ω) v1 = (fst Ω) v) /\ ~ ((fst Ω) v2 = (fst Ω) v)  -> M n = M' n) -> 
    ~ List.In v1 (exp_vars e2) -> (* not in paper proof *)
    l1 <> l2 -> (* not in paper proof *)
    gmp_stmt_sem funs procs Ω M (binop_ASSGN op (C_Int,c) e1 e2 r v1 v2) ((fst Ω){c\zr ⁱⁿᵗ ir : 𝕍}, snd Ω) M'
    .

Proof with eauto with rac_hint.
    intros. destruct H2 as (v1l & v2l & rl).  
    assert (NotInt : 
        exists M',
        (forall (v : 𝓥) (n : location),
        fst Ω v = Some (VMpz n) ->
        fst Ω v1 <> fst Ω v /\ fst Ω v2 <> fst Ω v ->
        M n = M' n) ->
        ~ List.In v1 (exp_vars e2) -> (* not in paper proof *)
        l1 <> l2 -> (* not in paper proof *)
        gmp_stmt_sem funs procs Ω M <{
            (mpz_ASSGN v1 e1);
            (mpz_ASSGN v2 e2);
            (Definitions.op op r v1 v2);
            (int_ASSGN c (C_Id r Mpz))
        }> ((fst Ω) {c \ zr ⁱⁿᵗ ir : 𝕍}, snd Ω)  M'
    ). {
        exists M{lr\zr,l2\z2,l1\z1}. intros. 
    apply S_Seq with Ω M{l1\z1}. 
    - apply semantics_of_the_mpz_assgn_macro...
    - apply S_Seq with Ω M{l2\z2,l1\z1}.
     + apply semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
     + apply S_Seq with Ω M{lr\zr,l2\z2,l1\z1}.
        * constructor. pose proof (p_map_not_same M{l1 \ z1}) l1 l2 z2 H4. simpl. apply S_op with l1 l2...
            ** constructor. apply GMP_E_Var with z1...  rewrite H5. apply p_map_same.
            ** apply p_map_not_same_eq ; [easy|apply p_map_same].
            ** constructor. apply GMP_E_Var with z2...
        * apply semantics_of_the_int_assgn_macro...  apply M_Mpz with lr...
            constructor. apply GMP_E_Var with zr... 
    }
    
    unfold binop_ASSGN. destruct (ty e1) eqn:T1, (ty e2) eqn:T2 ; try apply NotInt. clear NotInt.
    exists M. intros. inversion H0 ; inversion H1; try 
    match goal with 
    | Contra :  _ ⋅ _ |= _ => VMpz _ |- _ => 
        inversion Contra ; match goal with 
        | Contra : _gmp_exp_sem _ _ _ _ |- _ => inversion Contra ; now subst
        end
    end.
    - destruct x,x0. constructor... eapply C_E_BinOpInt. admit. admit.
    - admit. 
Admitted.



Lemma semantics_of_the_binop_macro_mpz :
    forall funs procs (Ω:Ω) (M:𝓜) (op:fsl_binop_int) c y r e1 e2 v1 v2 z1 z2 l1 l2,
    type_of_value ((fst Ω) c) = Some C_Int ->
    Ω ⋅ M |= e1 ⇝ z1 ->
    Ω ⋅ M |= e2 ⇝ z2 ->
   
    let zr := ⋄ (□ op) z1 z2 in
    (fst Ω) v1 = Some (VMpz l1) /\  (fst Ω) v2 = Some (VMpz l2) /\  (fst Ω) c = Some (VMpz y) ->
    ~ List.In v1 (exp_vars e2) -> (* not in paper proof *)
    exists M', (forall v n, (fst Ω) v = Some (VMpz n) ->
    ~ ((fst Ω) v1 = (fst Ω) v) /\ ~ ((fst Ω) v2 = (fst Ω) v)  -> M n = M' n) -> 
    l1 <> l2 -> (* not in paper proof *)
    gmp_stmt_sem funs procs Ω M (binop_ASSGN op (T_Ext Mpz,c) e1 e2 r v1 v2) Ω  M'{y\zr}
    .
Proof with eauto using p_map_same with rac_hint.
    intros. exists M{l2\z2,l1\z1}. intros. destruct H2 as (v1l & v2l & rl). unfold binop_ASSGN.
    apply S_Seq with Ω M{l1\z1}.
    - apply semantics_of_the_mpz_assgn_macro...
    - apply S_Seq with Ω M{l2\z2,l1\z1}. 
        * apply semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
        * constructor. pose proof (p_map_not_same M{l1 \ z1}) l1 l2 z2 H5. simpl. apply S_op with l1 l2...
            + constructor. simpl. apply GMP_E_Var with z1... rewrite H2...
            + rewrite H2...
            + constructor. simpl.  apply GMP_E_Var with z2...
Qed.

(* Preservation of the semantics *)

Open Scope fsl_sem_scope.

Lemma semantics_of_term_translation : 
    forall (t:fsl_term) Ω Γ Ψ z, 
    I1 Ω Γ -> I2 Ψ ->
    (Ω |= t => z <-> True)
    .
Proof.
    intros. split.
    - induction t eqn:T ; intro Hi.
        * admit.
        * admit.
        * admit.
        * admit.
    - induction t eqn:T; intro Hi.
        * admit.
        * admit.
        * admit.
        * admit.
Admitted.
