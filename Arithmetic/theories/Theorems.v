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



Definition _no_env_mpz_aliasing (env : Ω) : Prop := 
    forall v v' l l', 
    v <> v' ->
    (fst env) v = Some (Def (VMpz (Some l)))  ->
    (fst env) v' = Some (Def (VMpz (Some l'))) -> 
    l <> l'.

Definition _no_mem_aliasing {S T : Set} (stmt_sem : @stmt_sem_sig S T)  : Prop := 
    forall (exp_sem:@exp_sem_sig T) funs procs env mem s env' mem', 
    _no_env_mpz_aliasing env 
    -> stmt_sem funs procs env mem s env' mem' 
    -> _no_env_mpz_aliasing env'.


Fact _no_mem_aliasing_gmp : _no_mem_aliasing _gmp_stmt_sem.
Proof with auto with rac_hint.
    intros exp_sem funs procs env mem s env' mem' Hnoalias H. induction H
    ; auto ;  try (rename v into l1) ;
    intros v v' ll l' Hvv' Hl Hl' leq ; subst ; simpl in *.
    - destruct (eq_dec x v).
        + subst. rewrite p_map_same in Hl. rewrite p_map_not_same in Hl'... inversion Hl. 
            subst. now  destruct H0 with v'.
        + rewrite p_map_not_same in Hl... destruct (eq_dec x v').
            * subst. rewrite p_map_same in Hl'. inversion Hl'. subst. now destruct H0 with v.
            * rewrite p_map_not_same in Hl'... destruct Hnoalias with v v' l' l'...
    - destruct (eq_dec x v).
        + subst. now rewrite p_map_same in Hl.
        + rewrite p_map_not_same in Hl... destruct (eq_dec l' a).
            * destruct Hnoalias with v x l' a... 
            * destruct (eq_dec x v').
                ** subst. rewrite p_map_same in Hl'... easy.
                ** rewrite p_map_not_same in Hl'... destruct Hnoalias with v v' l' l'...     
    - destruct (string_dec x v').
        + subst. rewrite p_map_same in Hl'. discriminate.
        + rewrite p_map_not_same in Hl'... destruct (string_dec x v).
            * subst. rewrite p_map_same in Hl... discriminate.
            * rewrite p_map_not_same in Hl... destruct Hnoalias with v v' l' l'...
    - assert (type_of_value (Some b) = Some C_Int). {
        destruct H3 as [sup [inf eq]]. destruct (Z.lt_trichotomy lx ly) as [Hinf | [Heq | Hsup]].
        - apply inf in Hinf. now subst.
        - apply eq in Heq. now subst.
        - apply Z.lt_gt in Hsup.  apply sup in Hsup. now subst. 
        } 
        destruct (string_dec c v').
        + subst. rewrite p_map_same in Hl'. injection Hl' as Hl'. now subst. 
        + rewrite p_map_not_same in Hl'... destruct (string_dec c v).
            * subst. rewrite p_map_same in Hl. injection Hl as Hl. now subst.
            * rewrite p_map_not_same in Hl... destruct Hnoalias with v v' l' l'...
Qed.
    

(* probably incorrect*)
(* Fact no_mem_aliasing { S T : Set} : 
    forall exp_sem stmt_sem, 
    @_no_mem_aliasing S T stmt_sem -> @_no_mem_aliasing S T (@generic_stmt_sem S T exp_sem stmt_sem).
Proof with auto with rac_hint.
    intros exp_sem stmt_sem H e funs procs env mem s env' mem' Hnoalias Hderiv. induction Hderiv ; auto ;
        intros v v' l l' Hvv' Hl Hl' leq ; subst ; simpl in *.
    
    (* int assign *)  
    - destruct (string_dec x v') .
        + subst. rewrite p_map_same in Hl'. rewrite p_map_not_same in Hl...
            injection Hl' as Hl'. subst. inversion H1.
            
        + rewrite p_map_not_same in Hl'... rewrite p_map_not_same in Hl. 
            * destruct Hnoalias with v v' l' l'...
            * intro Hvx. subst. rewrite p_map_same in Hl. injection Hl as Hl. subst.
                inversion H1.
    (* fcall *) 
    - destruct (eq_dec c v). 
        * subst. rewrite p_map_not_same in Hl'... rewrite p_map_same in Hl. injection Hl as Hl. subst.
            assert (Hargs : _no_env_mpz_aliasing (p_map_addall ⊥ xargs zargs, ⊥)) (* using H3 *). admit.
            apply IHHderiv in Hargs. destruct (eq_dec v' resf).
            + subst.  admit.
            + admit.
        * rewrite p_map_not_same in Hl... destruct (eq_dec c v').
            + subst. rewrite p_map_same in Hl'. injection Hl' as Hl'. subst. admit.
            + rewrite p_map_not_same in Hl'... destruct Hnoalias with v v' l' l'...

    (* return *)
    -  destruct (eq_dec resf v). 
        * subst. rewrite p_map_same in Hl. injection Hl as Hl. subst. inversion H0. subst.
            rewrite p_map_not_same in Hl'...  admit.
        * rewrite p_map_not_same in Hl... destruct (eq_dec resf v')...
            + subst. rewrite p_map_same in Hl'. injection Hl' as Hl'. subst. inversion H0. subst.
                admit.
            + rewrite p_map_not_same in Hl'... destruct Hnoalias with v v' l' l'...
    - apply H in H0... destruct H0 with v v' l' l'...
Admitted. *)

Fact eq_env_partial_order :  forall e e' v z, e ⊑ e' ->  
    (fst e) v = Some (Def z) -> (fst e') v = Some (Def z).
Proof.
    intros e e' v z Hrel He. destruct Hrel with v; congruence.
    
    Qed.
Fact sym_env_cond : forall env env', 
(forall v, (dom (fst env) - dom (fst env')) v ) -> (env ⊑ env') -> (env' ⊑ env).

Proof.
    intros env env' H rel v ; destruct H with v as [Hin Hnotin] ; destruct Hnotin ; destruct rel with v.
    - now exists n. 
    - now exists (VMpz l).
    - destruct H1.
        + now exists (UInt n). 
        + destruct H1. now exists x. 
    - destruct H1.
        + now exists (UMpz n).
        + destruct H1 as [x]. now exists (VMpz x).
    - destruct Hin. destruct env. simpl in *. congruence.
Qed.

Corollary sym_env_cond_mem : forall (env : Ω) env' mem mem', 
(forall v, (dom (fst env) - dom (fst env')) v ) -> (env,mem) ⊑ (env',mem') ->  (env',mem) ⊑ (env,mem').
Proof.
    intros. split. apply sym_env_cond ; easy. now destruct H0.
Qed.




Corollary eq_env_partial_order_add :  forall e e' v v' z z',  e ⊑ e' ->  
    v <> v' ->
    (fst e) v = Some (Def z) -> ((fst e'){v'\z'}) v = Some (Def z).
Proof.
    intros [v l] [v' l'] var var' z z' Hrel Hneq H. 
    pose proof (eq_env_partial_order (v,l) (v',l') var z Hrel H).
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
Proof with auto with rac_hint.
    intros [v l][v' l'] H x z var. destruct (string_dec x var) as [Heq|Hneq].
    - subst. simpl. specialize (H var). destruct z. 
        + destruct v0.
            * apply EsameInt with n ;  apply p_map_same.
            * apply EsameMpz with l0; apply p_map_same.
        + destruct uv.
            ++ apply EundefInt with n ; simpl...
            ++ apply EundefMpz with l0 ; simpl...

    - apply not_eq_sym in Hneq. epose proof (p_map_not_same v var x ?[z] Hneq) as H0. simpl. remember (v var) as res. destruct res as [z'|].
        * destruct z'.
            + destruct v0.
                ++ apply EsameInt with n ; simpl.
                    +++ apply H0.
                    +++ apply p_map_not_same_eq in H0... epose proof (eq_env_partial_order_add  _ _ _ _ _ _ H). 
                        now apply H1.
                ++ apply EsameMpz with l0; simpl... epose proof (eq_env_partial_order_add  _ _ _ _ _ _ H).
                    symmetry in Heqres. specialize (H1 Hneq Heqres). simpl in H1. apply H1.

            + destruct uv.
                ++ eapply EundefInt ;subst ;simpl.
                    +++ apply H0.
                    +++ destruct H with var ; pose proof (p_map_not_same_eq v' var x z) as Hres; simpl in *; try congruence.
                        destruct H2.
                    ++++ specialize (Hres  (Some (Undef (UInt n))) Hneq). left. apply Hres. congruence.
                    ++++ destruct H2 as [x0]. specialize (Hres  (Some (Def (VInt x0))) Hneq). right. exists x0. now apply Hres.

                ++ eapply EundefMpz ; subst ; simpl.
                    +++ apply H0.
                    +++ destruct H with var ; pose proof (p_map_not_same_eq v' var x z) as Hres; simpl in * ; try congruence.
                        destruct H2.
                        ++++ specialize (Hres  (Some (Undef (UMpz l0))) Hneq). left.  apply Hres. congruence.
                        ++++ destruct H2 as [l0']. specialize (Hres  (Some (Def (VMpz l0'))) Hneq). right. exists l0'. now apply Hres.
        * now apply Enone.
Qed.

Fact mems_partial_order_add : forall M₀ M₀', mems_partial_order M₀ M₀' -> 
    (forall l mi, mems_partial_order ((M₀) {l \ mi}) ((M₀') {l \ mi})).
Proof.
    intros mem mem' H l mi. intros l' i H1. destruct (eq_dec l' l).
    - subst. pose proof (p_map_same mem l mi). rewrite H0 in H1. injection H1 as eq. subst.  apply p_map_same.
    - pose proof (p_map_not_same mem l' l mi n). rewrite H0 in H1. apply p_map_not_same_eq ; auto.
Qed.


Fact env_same_ty : forall  (Ω Ω' : Ω) v t, Ω ⊑ Ω' -> t <> None -> type_of_value (fst Ω v) = t -> type_of_value (fst Ω' v) = t.
Proof.
    intros. 
    match goal with | IncRel : _ ⊑ _ |- _ =>  destruct IncRel with v ; subst end ;
    match goal with 
    | L : fst Ω v = _,  R : fst Ω' v = _  |- _ => now rewrite L,R 
    | L : fst Ω v = _,  R : fst Ω' v = _ \/ _ |- _ => destruct R as [SomeUInt | [ x Some_n ]]; [now rewrite L,SomeUInt | now rewrite L,Some_n] 
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
    - destruct ty. easy. 1,2: apply ext_inj in H6 ; now apply H6 in H12.
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
    - inversion H ; inversion H0 ; subst ; try easy. congruence. 
    - inversion H.
    - inversion H.
Qed.

Definition determinist_gmp_exp_eval := determinist_exp_eval _gmp_exp_sem _determinist_gmp_exp_eval.


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



(* Definition _determinist_stmt_eval {S T : Set} (exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) : Prop := 
    @_determinist_exp_eval T exp_sem  -> 
    forall funs procs s env mem env' mem',  stmt_sem funs procs env mem s env' mem' ->  (forall env'' mem'', stmt_sem funs procs env mem s env'' mem'' -> env' = env'' /\ mem' = mem'').




Fact determinist_stmt_eval {S T : Set}: 
    forall  exp_sem stmt_sem, 
    @_determinist_stmt_eval S T exp_sem stmt_sem -> 
    _determinist_stmt_eval exp_sem (@generic_stmt_sem S T exp_sem stmt_sem).
Proof with auto. 
    intros exp_sem stmt_sem Hds Hde funs procs s env mem env' mem' Hderiv. induction Hderiv ; intros.
    - inversion H... 
    - inversion H2 ; subst ; split... repeat f_equal. apply determinist_exp_eval in H1...
    - inversion H1 ; subst...  apply determinist_exp_eval in H7... destruct H. apply H7 in H. now symmetry in H.
    - inversion H1 ; subst... apply determinist_exp_eval in H... destruct H7. apply H in H2. now symmetry in H2. 
    - inversion H0... 
    - inversion H1 ; subst... apply IHHderiv in H4 as [Eq1 Eq2]. subst. apply IHHderiv0 in H7. now subst. 
    - inversion H5 ; subst. 
       (* same args, same body *) 
            rewrite H11 in H0. injection H0 as H0. subst.
            (* same args eval *) 
            assert (zargs = zargs0) by auto using (@Forall2_same_zargs T env mem eargs zargs zargs0 exp_sem). 
            subst. apply IHHderiv in H15 as [Eq1 Eq2]. subst. rewrite H4 in H17. injection H17 as H17. now subst.
    - inversion H3.  subst. split... rewrite H7 in H0. injection H0 as Eq1. subst. 
            assert (zargs = zargs0) by auto using (@Forall2_same_zargs T env'' mem eargs zargs zargs0 exp_sem). subst. 
            now apply IHHderiv in H11.
    - inversion H0 ; subst... apply determinist_exp_eval in H... apply H in H5. now subst.
    - inversion H1...
    - inversion H0. subst. unfold _determinist_stmt_eval in Hds. eapply Hds... apply H. apply H2.
Qed.


Fact _determinist_gmp_stmt_eval :  _determinist_stmt_eval _gmp_exp_sem _gmp_stmt_sem.
Proof with auto.
    intros Hde funs procs s. induction s 
    ; intros ; inversion H ; inversion H0; subst ; split ; try easy ; try now destruct bop.
    - assert (l = l0) by eauto using fresh_location_deterministic. subst. inversion H7. subst. easy.
    - assert (l = l0) by eauto using fresh_location_deterministic. now subst.
    - congruence.
    - congruence.
    - injection H6 as H6. subst. rewrite H2 in H7. apply determinist_gmp_exp_eval in H3. apply H3 in H8. congruence.
    - injection H7 as H7. subst. rewrite H3 in H9. inversion H9. subst. rewrite H8 in H2. inversion H2.  congruence.
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
            apply determinist_gmp_exp_eval in H4; apply H4 in H12 ;
            inversion H10 ; inversion H11 ; inversion H12 ; subst ;
                rewrite H8 in H3 ; inversion H3 ; subst ; congruence).
Qed.


Definition determinist_gmp_stmt_eval := determinist_stmt_eval _gmp_exp_sem _gmp_stmt_sem _determinist_gmp_stmt_eval. *)


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
        + constructor. eapply eq_env_partial_order... easy.
        + unfold _weakening_of_expression_semantics in H. eapply  H in H2...
            constructor... inversion H3. apply eq_env_partial_order with env... 
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

Definition _untouched_var_same_eval_exp {T : Set} (exp_sem : @exp_sem_sig T) := 
    forall env mem (e: @_c_exp T) v x,
    ~ List.In v (exp_vars e) -> 
    exp_sem env mem e x ->
    (forall x', exp_sem((fst env){v\x'},snd env) mem e x)
    /\ 
    (forall l z', 
    _no_env_mpz_aliasing env ->
    (fst env) v = Some (Def (VMpz (Some l))) -> exp_sem env mem{l\z'} e x).

Fact untouched_var_same_eval_exp {T : Set} : forall exp_sem, 
    _untouched_var_same_eval_exp exp_sem ->
    _untouched_var_same_eval_exp (@generic_exp_sem T exp_sem).
Proof with eauto with rac_hint.
    intros exp_sem Hext env mem e v x Hnotin Hderiv. induction Hderiv ; simpl in Hnotin...
    - split... constructor. simpl. apply p_map_not_same_eq...
    - rewrite List.in_app_iff in Hnotin ; apply Decidable.not_or_iff in Hnotin as [Hxnotine Hxnotine'].  split ; 
        intro x';  econstructor...
        + apply IHHderiv1...
        + apply IHHderiv2...
        + apply IHHderiv1...
        + apply IHHderiv2...
    - rewrite List.in_app_iff in Hnotin ; apply Decidable.not_or_iff in Hnotin as [Hxnotine Hxnotine'].  split ; 
        intro x';  econstructor...
        + apply IHHderiv1...
        + apply IHHderiv2...
        + apply IHHderiv1...
        + apply IHHderiv2...
    - rewrite List.in_app_iff in Hnotin ; apply Decidable.not_or_iff in Hnotin as [Hxnotine Hxnotine'].  split ; 
        intro x';  econstructor...
        + apply IHHderiv1...
        + apply IHHderiv2...
        + apply IHHderiv1...
        + apply IHHderiv2... 
    -  split.
        + constructor... apply p_map_not_same_eq... apply Hext...
        + intros l z' Hmem. constructor... edestruct Hext... now simpl. 
Qed.

Fact _untouched_var_same_eval_exp_gmp : @_untouched_var_same_eval_exp _gmp_t _gmp_exp_sem.
Proof.
    intros env mem e v x Hnotin Hderiv. inversion Hderiv. subst. simpl in Hnotin.
    apply Decidable.not_or_iff in Hnotin as [Hdiff _]. split...
    - econstructor. 
        * now apply p_map_not_same_eq.
        * apply H0.
    - intros l' z' Hnoalias Hmem. apply GMP_E_Var with z.
        * apply H.
        * destruct (eq_dec l' l).
            + edestruct Hnoalias with x0 v l l' ; eauto with rac_hint.
            + subst. apply p_map_not_same_eq; auto.
Qed.

Definition untouched_var_same_eval_exp_gmp := untouched_var_same_eval_exp _gmp_exp_sem _untouched_var_same_eval_exp_gmp.


Definition _untouched_var_same_eval_stmt {S T : Set} (exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) := 
    forall funs procs env mem env' mem' (s: @_c_statement S T) x, 
    stmt_sem funs procs env mem s env' mem' ->

    (* doesn't work for a function call or a return if x = resf but 
        induction doesn't remember the shape of s, so I can't add a constraint like 
        (forall e res, s <> Return e res)
        I tried 'dependent induction', and 'remember s in Hderiv' 
     *) 
    ~ List.In x (stmt_vars s) -> 
    (fst env) x = (fst env') x
    .

    
Fact untouched_var_same_eval_stmt {S T : Set} : 
    forall exp_sem stmt_sem, 
    _untouched_var_same_eval_stmt exp_sem stmt_sem ->
    _untouched_var_same_eval_stmt exp_sem (@generic_stmt_sem S T exp_sem stmt_sem).
Proof.
    intros exp_sem stmt_sem Hext funs procs env mem env' mem' s x Hderiv Hnotin. induction Hderiv ; simpl in Hnotin; trivial.
    - subst. apply Decidable.not_or_iff in Hnotin as [Hdiffxresf]. simpl. rewrite p_map_not_same.
        * easy.
        * congruence.
    -  apply IHHderiv. 
        intro Hcontra. apply Hnotin. apply List.in_app_iff. right. 
        apply List.in_app_iff. now left.
    - apply IHHderiv. intro Hcontra. apply Hnotin. apply List.in_app_iff. right. 
        apply List.in_app_iff. now right.
    - apply IHHderiv. simpl. intro contra. rewrite List.app_nil_r in contra. apply Hnotin. apply List.in_app_iff in contra as [Hine | Hinses].
        * apply List.in_app_iff. now left.
        * apply List.in_app_iff in Hinses as [Hins | Hins].
            + apply List.in_app_iff. now right.
            + assumption.
    - destruct IHHderiv.
        + intro Hcontra. apply Hnotin. apply  List.in_app_iff. now left.
        + apply IHHderiv0. intro Hcontra. apply Hnotin. apply List.in_app_iff. now right.
    - destruct IHHderiv.
      destruct Hnotin.
      destruct H3.

      
      admit. (* fcall *)
    - admit. (* ret *)
    - eapply Hext in H ; eauto.
Admitted.




Definition _weakening_of_statement_semantics_1  {S T : Set} (exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) := 
    _weakening_of_expression_semantics exp_sem ->
    (* _determinist_stmt_eval exp_sem stmt_sem ->  *)
    forall (funs : @𝓕 S T) (procs : @𝓟 S T) Ω₀ M₀ s Ω₁ M₁,
    stmt_sem funs procs Ω₀ M₀ s Ω₁ M₁ <->
    ( forall Ω₀' M₀', (Ω₀ , M₀) ⊑ (Ω₀', M₀') ->
    exists Ω₁' M₁', (Ω₁ , M₁) ⊑ (Ω₁', M₁') /\ stmt_sem funs procs Ω₀' M₀' s Ω₁' M₁').
    

Lemma weakening_of_statement_semantics_1 {S T : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_statement_semantics_1 exp_sem stmt_sem 
    (* -> _determinist_stmt_eval exp_sem stmt_sem *)
    -> _weakening_of_statement_semantics_1 exp_sem (@generic_stmt_sem S T exp_sem stmt_sem)
.
Proof with eauto using refl_env_mem_partial_order,env_partial_order_add with rac_hint.
    intros exp_sem stmt_sem Hext_stmt Hext_exp funs procs Ω₀ M₀ s Ω₁ M₁. 
    pose proof (weakening_of_expression_semantics exp_sem Hext_exp) as exp_weak.
    split.
    - intro Hderiv. induction Hderiv ; intros Ω₀' M₀' [Henv Hmem].
        (* skip *)
        * exists Ω₀',M₀'... 
        
        (* assign *) 
        * exists ((fst Ω₀') {x \ z}, (snd Ω₀')) , M₀'. split.
            + split...
            + apply S_Assign...
                *** now apply env_same_ty with env. 
                *** rewrite (exp_weak e) in H1. specialize (H1 Ω₀' M₀'). apply H1...


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
        * specialize (Hext_stmt Hext_exp funs procs env mem (S_Ext s) env' mem').
            apply Hext_stmt with Ω₀' M₀' in H. destruct H as [env'' [mem'' [Hrel2 Hderiv]]]... easy.
                
    - intros H. admit. (* ??? *)
        
Admitted.


Fact _weakening_of_c_statements_semantics_1 : _weakening_of_statement_semantics_1 Empty_exp_sem Empty_stmt_sem. 
Proof.
    unfold _weakening_of_statement_semantics_1. intros. split; unfold Empty_stmt_sem.
    - intros [].
    - intro H2. destruct H2 with Ω₀ M₀.
        + apply refl_env_mem_partial_order.
        + destruct H0 as [_ [_ []]]. 
Qed.


Lemma _weakening_of_gmp_statements_semantics_1 : 
    _weakening_of_statement_semantics_1 _gmp_exp_sem _gmp_stmt_sem
.
Proof with eauto using eq_env_partial_order, eq_mem_partial_order,refl_env_mem_partial_order with rac_hint ; try easy.
    intros Hweak funs procs Ω₀ M₀ s Ω₁ M₁. split.
    - intro Hderiv. induction Hderiv; intros Ω₀' M₀' [Henv Hmem] ;
        pose proof (fun y => weakening_of_gmp_expression_semantics y Ω₀ M₀) as weak_exp. 
        * exists (p_map (fst Ω₀') (x, (Def (VMpz (Some l)))), snd Ω₀'). exists M₀'{l \Defined 0}. split...
            + split. 
                ++ apply env_partial_order_add... 
                ++ apply mems_partial_order_add...
            + apply S_init.
                ++ admit.
                ++ apply fresh_location_no_alias in H. intros v Heq.  admit.
                ++ destruct H1. exists x0. admit.
        * exists (p_map (fst Ω₀') (x, Def (VMpz None)), snd Ω₀'). exists M₀' {a \ Undefined z}. split.
            + split.
                ++ apply env_partial_order_add...
                ++ apply mems_partial_order_add...
            + constructor... 

        * exists Ω₀',(M₀') {a \ Defined (z) ̇}. split.
            + split... intro n. apply (mems_partial_order_add M₀ M₀' Hmem a (Int.to_z z)). 
            + apply S_set_i. eapply eq_env_partial_order... apply weak_exp...

        * exists Ω₀', M₀' {a \ z}. split.
            + split... intro n0.  apply (mems_partial_order_add M₀ M₀' Hmem a). 
            + apply S_set_z with n.
                ++ eapply eq_env_partial_order...
                ++ eapply eq_env_partial_order...
                ++ apply (eq_mem_partial_order M₀ M₀')...

        * inversion H0. subst. eexists (((fst Ω₀') {x \ Def (VInt (Int.mkMI z  ir))}, snd Ω₀')), M₀'... split.
            + split... pose env_partial_order_add...
            + apply S_get_int with v... apply weak_exp...
        
        * exists Ω₀',M₀' {a \ Defined z}. split. 
            + split... apply (mems_partial_order_add M₀ M₀' Hmem a z). 
            + constructor...

        * inversion H. subst. inversion H8. inversion H0. subst. 
            eexists ((fst Ω₀') {c \ b}, snd Ω₀'),M₀'. split.
            ** split... pose env_partial_order_add...
            ** inversion H13. subst. apply S_cmp with vx vy lx ly...
                + constructor... 
                + constructor...
        
        * eexists Ω₀', M₀' {lr \Defined (⋄ (□ bop) z1 z2)}. split.
            ** split... intro n. apply mems_partial_order_add...
            **  apply S_op with vx vy ; try apply weak_exp...
    
    - intro H. specialize (H Ω₀ M₀ (refl_env_mem_partial_order Ω₀ M₀))...
        destruct H as [Ω₁' [M₁' [Hrel Hderiv ]]]... induction Hderiv.
        + admit. (* non sense ? *)
Admitted.

Definition weakening_of_gmp_statements_semantics_1 := 
    weakening_of_statement_semantics_1 _gmp_exp_sem _gmp_stmt_sem _weakening_of_gmp_statements_semantics_1.


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
        (forall (x:location) (v:𝓥), (fst Ω₀ v) <> Some (Def (VMpz x)) -> M₀' x = M₁' x)
    ).


Lemma weakening_of_statement_semantics_2 {S T : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_statement_semantics_2 exp_sem stmt_sem 
    -> _weakening_of_statement_semantics_2 exp_sem (@generic_stmt_sem S T exp_sem stmt_sem)
.
Proof with auto with rac_hint.
    intros exp_sem stmt_sem ext_stmt_weak funs procs Ω₀ Ω₀' M₀ M₀' s Ω₁ M₁ ext_exp_deter ext_exp_weak  [Hderiv1 Hrel].
    pose proof (weakening_of_expression_semantics exp_sem ext_exp_weak) as exp_weak.
    unfold _weakening_of_expression_semantics in exp_weak.
    unfold _weakening_of_statement_semantics_2 in ext_stmt_weak.
    
    induction Hderiv1 ; intros Ω₁' M₁' Hderiv2 ; inversion Hderiv2 ; subst ; try easy...
    
    (* assign *)
    - split... simpl. intros v H2.  assert (HH: type_of_value (fst env x) <> None) by congruence. apply type_of_value_env in HH.
        apply not_in_diff with (x:=v)  in HH... eapply p_map_not_same_eq... intro neq...

    (* if false *)
    - apply IHHderiv1... destruct H. specialize (exp_weak e env mem z). rewrite exp_weak in H. specialize (H Ω₀' M₀' Hrel). 
            apply determinist_exp_eval in H. apply H in H6. now subst. assumption.

    (* if true *)
    -  destruct H6. specialize (exp_weak e env mem zero). rewrite exp_weak in H. specialize (H Ω₀' M₀' Hrel).
            apply determinist_exp_eval in H. apply H in H1. now subst. assumption.

    (* seq *)
    -  admit.
    
    (* fcall *)
    - admit.

    (* pcall *)
    -  rewrite H6 in H0. injection H0 as H0. subst. edestruct IHHderiv1... admit. admit.
        epose proof (List.Forall2_impl (R1:=generic_exp_sem env mem) (generic_exp_sem env mem)) as Hforall. admit.

    (* return *)
    - split ; intros... simpl. unfold "∉" in H0.  destruct (string_dec resf v).
        + apply exp_weak with (env':=Ω₀') (mem':=M₁') in H...
            apply determinist_exp_eval in H... apply H in H4. subst. admit. (* can't happen *)
        +  symmetry. apply p_map_not_same...
            
    (* assert *)
    - eapply ext_stmt_weak with ( Ω₀:=env) ( M₀:=mem) (Ω₁:=env') (M₁:=mem') in H1...
Admitted.


(* 3 *)

Definition _weakening_of_expression_semantics_3 {T : Set} (exp_sem : @exp_sem_sig T) := 
    forall env mem e z Ω₀ M₀,
    exp_sem env mem e z ->
    forall Ω₀' M₀', (Ω₀', M₀') ⊑ (Ω₀, M₀) ->
    (
        (forall v, (dom (fst Ω₀) - dom (fst Ω₀')) v /\ ~ List.In v (exp_vars e))
        /\
        (forall x v, (dom M₀ - dom M₀') x -> (fst Ω₀) v = Some (Def (VMpz x)) /\ ~ List.In v (exp_vars e))
    ) ->

    exp_sem  Ω₀' M₀' e z
.

Fact weakening_of_expression_semantics_3 {S T : Set} : forall exp_sem, 
    _weakening_of_expression_semantics exp_sem
    -> _weakening_of_expression_semantics_3 (@generic_exp_sem T exp_sem)
.
Proof with auto.
    intros exp Hweak env mem e v env1 mem1 Hderiv env2 mem2 Hrel [Henv Hmem]. induction Hderiv.
    - constructor.
    - constructor. destruct Henv with x. simpl in H1. destruct H1. now left.
    - econstructor.
        + apply IHHderiv1.
            * intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                intros Hine. apply He2. apply List.in_app_iff...
            * intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                intro Hin. apply Hm2. apply List.in_app_iff... 
        + apply IHHderiv2.
            * intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                intros Hine. apply He2. apply List.in_app_iff. now right.
            * intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                intro Hin. apply Hm2. apply List.in_app_iff... 
    - apply C_E_BinOpTrue with z z' z_ir z'_ir...
        + apply IHHderiv1.
            * intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                intros Hine. apply He2. apply List.in_app_iff...
            * intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                intro Hin. apply Hm2. apply List.in_app_iff...
        + apply IHHderiv2.
            * intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                intros Hine. apply He2. apply List.in_app_iff...
            * intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                intro Hin. apply Hm2. apply List.in_app_iff...

    - apply C_E_BinOpFalse with z z' z_ir z'_ir...
        + apply IHHderiv1.
            * intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                intros Hine. apply He2. apply List.in_app_iff...
            * intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                intro Hin. apply Hm2. apply List.in_app_iff...
        + apply IHHderiv2.
            * intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                intros Hine. apply He2. apply List.in_app_iff...
            * intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                intro Hin. apply Hm2. apply List.in_app_iff...
    - constructor...
        + destruct Henv with x. simpl in H3. destruct H3. now left.
        + destruct Henv with x. simpl in H3. destruct H3. now left. 
Qed.

Definition _weakening_of_statement_semantics_3  {S T : Set} (stmt_sem : @stmt_sem_sig S T) := 
    forall funs procs Ω₀ M₀  s Ω₁ M₁,
    stmt_sem funs procs Ω₀ M₀ s Ω₁ M₁ -> 
    (
        forall Ω₀' M₀', (Ω₀', M₀') ⊑ (Ω₀, M₀) ->
        (
            (forall v, (dom (fst Ω₀) - dom (fst Ω₀')) v /\ ~ List.In v (stmt_vars s))
            /\
            (forall x v, (dom M₀ - dom M₀') x -> (fst Ω₀) v = Some (Def (VMpz x)) /\ ~ List.In v (stmt_vars s))
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
    intros exp_sem stmt_sem ext_exp_weak ext_stmt_weak funs procs Ω₀ M₀ s Ω₁ M₁ Hderiv Ω₀' M₀' Hrel [Henv Hmem].
    induction Hderiv.
    (* skip *)
    - exists Ω₀', M₀'. constructor.
    (* assign *)
    - destruct Henv with x. simpl in H3. destruct H3...  
    (* if true *)
    - destruct IHHderiv as [env'' [mem'' Hx]]...
        + intro v. destruct Henv with v. split... intros Hin. apply H2.
            apply List.in_app_iff. right. apply List.in_app_iff...
        + intros l v Hdom. destruct Hmem with l v... split... intros Hin. apply H2.  
            apply List.in_app_iff. right. apply List.in_app_iff...
        + exists env'', mem''. apply S_IfTrue with z... destruct H as [He Hzero]. split...
            eapply weakening_of_expression_semantics_3 in He... specialize He with Ω₀' M₀'. apply He.
            * apply Hrel.
            * split ; simpl in Henv,Hmem.
                ** intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                    intros Hine. apply He2. apply List.in_app_iff...
                ** intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                    intro Hin. apply Hm2. apply List.in_app_iff...

    (* if false *)
    - destruct IHHderiv as [env'' [mem'' Hx]]...
        + intro v. destruct Henv with v. split... intros Hin. apply H2.
            apply List.in_app_iff. right. apply List.in_app_iff...
        + intros l v Hdom. destruct Hmem with l v... split... intros Hin. apply H2.  
            apply List.in_app_iff. right. apply List.in_app_iff...
        + exists env'', mem''. apply S_IfFalse... 
            eapply weakening_of_expression_semantics_3 in H... specialize H with Ω₀' M₀'. apply H.
            * apply Hrel.
            * split ; simpl in Henv,Hmem.
                ** intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                    intros Hine. apply He2. apply List.in_app_iff...
                ** intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                    intro Hin. apply Hm2. apply List.in_app_iff...
    (* while *)
    - destruct IHHderiv as [env'' [mem'' Hx]]...
        + intro v. destruct Henv with v. split... intros Hin. simpl in H1,Hin. apply H1. rewrite List.app_nil_r in Hin.
            apply List.in_app_iff in Hin. destruct Hin.
            * apply List.in_app_iff...
            * apply List.in_app_iff in H2. destruct H2... apply List.in_app_iff...
        + intros l v Hdom. destruct Hmem with l v... split... intros Hin. apply H1. simpl in Hin. rewrite List.app_nil_r in Hin.
            apply List.in_app_iff in Hin. destruct Hin.
            * apply List.in_app_iff...
            * apply List.in_app_iff in H2. destruct H2... apply List.in_app_iff...
        +  exists env'', mem''. constructor... 

    (* seq *)
    - destruct IHHderiv as [env0 [mem0 Hx]]...
        + intro v. destruct Henv with v. split... intros Hin. simpl in H2,Hin. apply H2. 
            apply List.in_app_iff...
        + intros l v Hdom. destruct Hmem with l v... split... intros Hin. apply H2. simpl in Hin.
            apply List.in_app_iff...
        + eexists. eexists. apply S_Seq with env0 mem0... admit.        

    (* fcall *)
    - eexists. eexists. apply S_FCall with b env' xargs zargs...
        * admit.
        * admit.
        * apply H4.

    (* pcall *)
    - repeat eexists. apply S_PCall with b env' xargs zargs...
        * admit.
        * admit.

    (* return *)
    - exists ((fst Ω₀'){resf\z},snd Ω₀').  eexists M₀'. apply S_Return.
        eapply weakening_of_expression_semantics_3 in H... specialize H with Ω₀' M₀'. apply H...
        * apply Hrel.
        * easy. 
        
    (* assert *)
    - exists Ω₀'. exists M₀'. apply S_PAssert with z... 
        eapply weakening_of_expression_semantics_3 in H... specialize H with Ω₀' M₀'. apply H...
        * apply Hrel.
        * easy.

    (* other cases *)
    - unfold _weakening_of_statement_semantics_3 in ext_stmt_weak.
        specialize (ext_stmt_weak funs procs  env mem (S_Ext s) _ _ H Ω₀' M₀' Hrel).
        destruct ext_stmt_weak as [env'' [mem'' Hd]]... exists env'', mem''...
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

Corollary same_eval_macro :  forall Ω M v l e z z', 
    _no_env_mpz_aliasing Ω ->
    ~ List.In v (exp_vars e) ->
    (fst Ω) v = Some (Def (VMpz (Some l))) ->
    Ω ⋅ M |= e ⇝ z ->
    Ω ⋅ (M) {l \ Defined z'} |= e ⇝ z.

Proof.
    intros. inversion H2.
    * constructor. apply untouched_var_same_eval_exp_gmp with v ; assumption.
    * apply M_Mpz with l0 ; subst.
        + apply untouched_var_same_eval_exp_gmp with v ; assumption.
        + inversion H3. inversion H9. subst. simpl in H0. apply Decidable.not_or_iff in H0 as [Hdiff _].
            destruct (eq_dec l l0).
            ++ subst. destruct H with v x l0 l0 ; congruence.
            ++ apply p_map_not_same_eq ; congruence.
Qed.

Lemma semantics_of_the_mpz_assgn_macro :
    forall funs procs e z Ω M v (y:location),
    Ω ⋅ M |= e ⇝ z ->
    (fst Ω) v = Some (Def (VMpz y)) ->
    gmp_stmt_sem funs procs Ω M (mpz_ASSGN v e) Ω M{y\Defined z} 
.
Proof.
    intros. 
    unfold mpz_ASSGN. destruct (ty e) eqn:TY.
    - inversion H ; constructor.
        * now apply S_set_i.
        * inversion H1. inversion H8. now subst. 
    - unfold ty in TY. destruct e; try easy. inversion H ;inversion H1 ; now subst.
    - destruct t ; destruct e ; try easy; destruct ty ; try easy ; destruct t ; try easy ;
        inversion H ; inversion H1 ; try easy. inversion H8. subst. 
        constructor.  now apply S_set_z with l.
Qed.

Lemma semantics_of_the_int_assgn_macro :
    forall funs procs e z (ir: Int.inRange z) Ω M v,
    Ω ⋅ M |= e ⇝ z ->
    type_of_value ((fst Ω) v) = Some C_Int ->
    gmp_stmt_sem funs procs Ω M (int_ASSGN v e) ((fst Ω){v\z ⁱⁿᵗ ir : 𝕍}, snd Ω)  M
.
Proof with eauto with rac_hint.
    intros funs procs e z ir Ω M v H H0. 
    unfold int_ASSGN.
    destruct (ty e)  eqn:EqTY.
    - constructor... inversion H ; subst.
        +  now rewrite (x_of_z_to_z_is_x x ir). 
        + inversion H1. subst. now inversion t.
    - inversion H ; inversion H1 ; subst ; try easy. inversion H8. now subst. 
    - inversion H ; inversion H1 ; subst ; try easy. simpl in EqTY. subst.
        destruct t ; try easy. constructor...
Qed.

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
    (fst Ω) v = Some (Def (VMpz (Some y))) ->
    gmp_stmt_sem funs procs Ω M (Z_ASSGN Mpz v z) Ω M{y\Defined z}
.
Proof with auto using BinaryString.Z_of_of_Z.
    intros. simpl. constructor. apply S_set_s...
Qed.


Lemma semantics_of_the_cmp_macro :
    forall funs procs (Ω:Ω) (M:𝓜) c e1 e2 v1 v2 z1 z2 a,
    _no_env_mpz_aliasing Ω ->
    type_of_value ((fst Ω) c) = Some C_Int ->
    Ω ⋅ M |= e1 ⇝ z1 ->
    Ω ⋅ M |= e2 ⇝ z2 ->

    (
        (Def a = VInt sub_one <-> Z.lt z1 z2 ) /\
        (Def a = VInt zero <-> z1 = z2) /\
        (Def a = VInt one <-> Z.gt z1 z2)
    ) -> 

    (* v1 and v2 must be bound to a mpz location (implied by mpz_assign ) *)
    forall (l1 l2 : location),
    (fst Ω) v1 = Some (Def (VMpz l1)) /\  (fst Ω) v2 = Some (Def (VMpz l2))->
    
    ~ List.In v1 ((exp_vars e2)) /\  l1 <> l2   -> (* not in paper proof *)

    exists M', (
        forall v (n:location), 
        (fst Ω) v = Some (Def (VMpz n)) ->
        (fst Ω) v <> (fst Ω) v1 /\ (fst Ω) v <> (fst Ω) v2  -> 
        M n = M' n
    ) -> 
    
    gmp_stmt_sem funs procs Ω M (CMP c e1 e2 v1 v2) ((fst Ω){c\Def a}, snd Ω) M'
.

Proof with try easy ; auto with rac_hint ; unshelve eauto using Z.ltb_irrefl,Z.gtb_ltb,Z.ltb_lt with rac_hint; auto with rac_hint.
    intros funs procs Ω M c e1 e2 v1 v2 z1 z2 a Hnoalias H H0 H1 (inf & eq & sup) l1 l2 (Hv1 & Hv2) (Hv1NotIne2 & Hdiffl1l2).
    
    assert (NotInt : 
        exists M', (
            forall v (n:location), 
            (fst Ω) v = Some (Def (VMpz n)) ->
            (fst Ω) v <> (fst Ω) v1 /\ (fst Ω) v <> (fst Ω) v2  -> 
                M n = M' n
        ) -> 
        gmp_stmt_sem funs procs Ω M <{(mpz_ASSGN v1 e1); (mpz_ASSGN v2 e2); <c = cmp (v1, v2)>}> ((fst Ω) {c \Def a}, snd Ω)  M'
    ). {
        exists M{l2 \Defined z2, l1 \Defined  z1}. intros Hvdiff. apply S_Seq with Ω M{l1\Defined z1}.
        - apply semantics_of_the_mpz_assgn_macro...
        - eapply S_Seq with Ω M{l2\Defined z2,l1\Defined z1}.
            + apply semantics_of_the_mpz_assgn_macro... inversion H1 ; subst. 
                * constructor. eapply untouched_var_same_eval_exp_gmp...
                * inversion H2. subst.   assert (Hdiffxv1: x <> v1). { simpl in Hv1NotIne2. now apply Decidable.not_or_iff in Hv1NotIne2 as [Hv1NotIne2 _]. }
                    econstructor. eapply untouched_var_same_eval_exp_gmp... assert (Hdiffll1: l <> l1)... apply p_map_not_same_eq...

            + constructor. apply S_cmp with (vx:=l1) (vy:=l2) (lx:=z1) (ly:=z2)...
                * constructor... constructor 1 with z1...  apply p_map_not_same_eq...
                * constructor...
                * apply p_map_not_same_eq...
    }
    unfold CMP. destruct (ty e1) eqn:T1, (ty e2) eqn:T2 ; try apply NotInt ; clear NotInt.
    
     (* both ty(e1) = int and ty(e2) = int *)
    - inversion H0 ; inversion H1 ; try 
            match goal with 
            | Contra :  _ ⋅ _ |= _ => Def (VMpz _) |- _ => 
                inversion Contra ; match goal with 
                | Contra : _gmp_exp_sem _ _ _ _ |- _ => inversion Contra ; now subst
                end
            end.
        exists M. intros Hvdiff. clear Hvdiff (* not needed *). destruct (Z.lt_trichotomy z1 z2) as [inf' | [ eq' | sup']].
        
        (* z1 < z2 *)
        * assert (cmp := inf'). apply <- inf in inf'. clear eq inf sup. subst.
            destruct x,x0. subst. apply S_IfTrue with one.
            + split... apply C_E_BinOpTrue with val val0 in_range in_range0... apply Z.ltb_lt. apply cmp.
            + inversion inf'. constructor...  apply (C_E_BinOpInt Ω M 0 1 0 1) with zeroinRange oneinRange...

        (* z1 = z2 *)
        * assert (cmp := eq'). rewrite <- eq in eq'. clear eq inf sup. subst.
            destruct x,x0. apply Int.mi_eq in cmp. injection cmp as cmp. inversion eq'. subst. constructor...

        (* z1 > z2 *)
        * assert (cmp := sup').  apply Z.lt_gt in sup'. apply <- sup in sup'.  clear inf eq sup. subst.
          destruct x, x0. subst. constructor ; simpl in *.
            + eapply C_E_BinOpFalse... apply Z.ltb_ge. unfold Z.le. now rewrite cmp.  
            + inversion sup'. subst. apply S_IfTrue with one.
                ++  subst. split... apply C_E_BinOpTrue with val val0 in_range in_range0... now apply Z.gtb_lt.
                ++  constructor... 
Qed.




Lemma semantics_of_the_binop_macro_int :
    forall funs procs (Ω:Ω) (M:𝓜) (op:fsl_binop_int) c r e1 e2 v1 v2 z1 z2 (ir: Int.inRange (⋄ (□ op) z1 z2) ) l1 l2 lr,
    _no_env_mpz_aliasing Ω ->
    type_of_value ((fst Ω) c) = Some C_Int ->
    Ω ⋅ M |= e1 ⇝ z1 ->
    Ω ⋅ M |= e2 ⇝ z2 ->
    let zr := ⋄ (□ op) z1 z2 in

    (fst Ω) v1 = Some (Def (VMpz (Some l1))) /\  
    (fst Ω) v2 = Some (Def (VMpz (Some l2))) /\
    (fst Ω) r = Some (Def (VMpz (Some lr))) ->
    exists M', (forall v n, (fst Ω) v = Some (Def (VMpz (Some n))) ->
    ~ ((fst Ω) v1 = (fst Ω) v) /\ ~ ((fst Ω) v2 = (fst Ω) v)  -> M n = M' n) -> 

    ~ List.In v1 ((exp_vars e2)) /\  l1 <> l2   -> (* not in paper proof *)

    gmp_stmt_sem funs procs Ω M (binop_ASSGN op (C_Int,c) e1 e2 r v1 v2) ((fst Ω){c\zr ⁱⁿᵗ ir : 𝕍}, snd Ω) M'
    .

Proof with eauto with rac_hint.
    intros funs procs Ω M op c r e1 e2 v1 v2 z1 z2 ir l1 l2 lr Hnoalias H H0 H1 zr H2. destruct H2 as (v1l & v2l & rl).  
    assert (NotInt : 
        exists M',
        (forall (v : 𝓥) (n : location),
        fst Ω v = Some (Def (VMpz n)) ->
        fst Ω v1 <> fst Ω v /\ fst Ω v2 <> fst Ω v ->
        M n = M' n) ->
        ~ List.In v1 ((exp_vars e2)) /\  l1 <> l2   -> (* not in paper proof *)
        gmp_stmt_sem funs procs Ω M <{
            (mpz_ASSGN v1 e1);
            (mpz_ASSGN v2 e2);
            (Definitions.op op r v1 v2);
            (int_ASSGN c (C_Id r Mpz))
        }> ((fst Ω) {c \ zr ⁱⁿᵗ ir : 𝕍}, snd Ω)  M'
    ). {
    exists M{lr\Defined zr,l2\Defined z2,l1\Defined z1}. intros H2 [H3 H4].  apply S_Seq with Ω M{l1\Defined z1}. 
    - apply semantics_of_the_mpz_assgn_macro...
    - apply S_Seq with Ω M{l2\Defined z2,l1\Defined z1}.
        + apply semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
        + apply S_Seq with Ω M{lr\Defined zr,l2\Defined z2,l1\Defined z1}.
            * constructor. apply S_op with l1 l2...
                ** constructor... easy. apply GMP_E_Var with z1... destruct (eq_dec l1 l2).
                    *** subst. edestruct Hnoalias...
                    *** apply p_map_not_same_eq...
                ** destruct (eq_dec l1 l2).
                    *** subst. edestruct Hnoalias...
                    *** apply p_map_not_same_eq...
                ** constructor... easy.
            * apply semantics_of_the_int_assgn_macro...  apply M_Mpz with lr...
                constructor... easy. 
    }
    
    unfold binop_ASSGN. destruct (ty e1) eqn:T1, (ty e2) eqn:T2 ; try apply NotInt. clear NotInt.
    exists M. intros. inversion H0 ; inversion H1; try 
    match goal with 
    | Contra :  _ ⋅ _ |= _ => Def (VMpz _) |- _ => 
        inversion Contra ; match goal with 
        | Contra : _gmp_exp_sem _ _ _ _ |- _ => inversion Contra ; now subst
        end
    end.
    - subst. constructor... destruct x,x0. econstructor...
Qed.



Lemma semantics_of_the_binop_macro_mpz :
    forall funs procs (Ω:Ω) (M:𝓜) (op:fsl_binop_int) c y r e1 e2 v1 v2 z1 z2 l1 l2,
    _no_env_mpz_aliasing Ω ->
    type_of_value ((fst Ω) c) = Some C_Int ->
    Ω ⋅ M |= e1 ⇝ z1 ->
    Ω ⋅ M |= e2 ⇝ z2 ->

    let zr := ⋄ (□ op) z1 z2 in
    (fst Ω) v1 = Some (Def (VMpz (Some l1))) /\  (fst Ω) v2 = Some (Def (VMpz (Some l2))) /\  (fst Ω) c = Some (Def (VMpz (Some y))) ->
    ~ List.In v1 (exp_vars e2) -> (* not in paper proof *)
    exists M', (forall v n, (fst Ω) v = Some (Def (VMpz (Some n))) ->
    ~ ((fst Ω) v1 = (fst Ω) v) /\ ~ ((fst Ω) v2 = (fst Ω) v)  -> M n = M' n) -> 
    l1 <> l2 -> (* not in paper proof *)
    gmp_stmt_sem funs procs Ω M (binop_ASSGN op (T_Ext Mpz,c) e1 e2 r v1 v2) Ω  M'{y\Defined zr}
    .
Proof with eauto using p_map_same with rac_hint.
    intros funs procs Ω M op c y r e1 e2 v1 v2 z1 z2 l1 l2 Hnoalias H H0 H1 zr H2 H3. exists M{l2\Defined z2,l1\Defined z1}. intros. destruct H2 as (v1l & v2l & rl). unfold binop_ASSGN.
    apply S_Seq with Ω M{l1\Defined z1}.
    - apply semantics_of_the_mpz_assgn_macro...
    - apply S_Seq with Ω M{l2\Defined z2,l1\Defined z1}. 
        * apply semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
        * constructor. pose proof (p_map_not_same M{l1 \Defined z1}) l1 l2 z2 H5. simpl. apply S_op with l1 l2...
            + constructor... easy. apply GMP_E_Var with z1... rewrite H2...
            + rewrite H2...
            + constructor... easy.
Qed.

(* Preservation of the semantics *)

Open Scope fsl_sem_scope.

(* Lemma semantics_of_term_translation : 
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
Admitted. *)
