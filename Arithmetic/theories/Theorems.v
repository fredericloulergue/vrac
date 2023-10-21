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

Fact eq_env_partial_order :  forall e e' v z, e ⊑ e' ->  z <> UInt /\ z <> UMpz -> (fst e) v = Some z -> (fst e') v = Some z.
Proof.
    intros. destruct H with v ; try assumption ; try rewrite H2 in H1 ; try injection H1 as Eq ; subst ; now try assumption.
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
    - destruct ty. 2,3: specialize (H1 I) ; specialize (H4 I) ; apply ext_inj in H1 ; now apply H1 in H4. easy.
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


(* todo : also prove statements are deterministic *)

Definition _determinist_stmt_eval {S T : Set} (exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) : Prop := 
    @_determinist_exp_eval T exp_sem  -> 
    forall s env mem env' mem',  stmt_sem env mem s env' mem' ->  (forall env'' mem'', stmt_sem env mem s env'' mem'' -> env' = env'' /\ mem' = mem'').


Fact determinist_stmt_eval {S T : Set}: 
    forall exp_sem stmt_sem , @_determinist_stmt_eval S T exp_sem stmt_sem -> 
    _determinist_stmt_eval exp_sem (@generic_stmt_sem S T exp_sem stmt_sem).
Proof with auto.
    intros exp_sem stmt_sem Hds. unfold _determinist_stmt_eval. intros Hde s. induction s ; intros  ; inversion H ; inversion H0 ;  subst ; try easy. 
    -  apply determinist_exp_eval in H6... apply H6 in H12. now subst.
    - admit. (* need same function maps *)
    - admit. (* need same predicate maps *)
    - apply IHs1 with (env':=env'0)  (mem':=mem'0) in H9...
        apply IHs2 with (env':=env')  (mem':=mem') in H12... destruct H9. now  subst.
    - now apply IHs1 with (env':=env'')  (mem':=mem'') in H7...
    - destruct H6. apply determinist_exp_eval in H1... apply H1 in H13. now subst.
    - destruct H13. apply determinist_exp_eval in H6... apply H6 in H1. now subst.
    - apply IHs2 with (env':=env')  (mem':=mem') in H14...
    - inversion H5; inversion H10 ; subst ; try easy.
        + inversion H8 ;  inversion H16 ; subst ; try easy.
            apply IHs with (env':=env'1)  (mem':=mem'1) in H3 as [He hm]... subst. admit. (* not sure what the problem is *)
        + destruct H7. apply determinist_exp_eval in H1... apply H1 in H15. now subst.
        + destruct H15. apply determinist_exp_eval in H1... apply H1 in H7. now subst.
        + inversion H8 ; inversion H16 ; now subst.
    - split... apply determinist_exp_eval in H2... apply H2 in H6. subst. f_equal. f_equal. f_equal.  admit. (* same functions must use same return variable*)
    - specialize (H1 I).  apply Hds in H1...
    - specialize (H1 I). apply Hds in H1...
Admitted.

Fact _determinist_gmp_stmt_eval :  _determinist_stmt_eval _gmp_exp_sem _gmp_stmt_sem.
Proof with auto.
    intros Hde s. induction s ; intros ; inversion H ; inversion H0; subst ; split ; try easy ; try now destruct bop.
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
            ++ intros []. apply H...
            ++ intros []. apply H...
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

Definition _weakening_of_statement_semantics_1  {T S : Set} (stmt_sem : @stmt_sem_sig T S) := 
    forall Ω₀ M₀ s Ω₁ M₁,
    stmt_sem Ω₀ M₀ s Ω₁ M₁ <->
    ( forall Ω₀' M₀', (Ω₀ , M₀) ⊑ (Ω₀', M₀') ->
    exists Ω₁' M₁', (Ω₁ , M₁) ⊑ (Ω₁', M₁') /\ stmt_sem Ω₀' M₀' s Ω₁' M₁').
    

Lemma weakening_of_statement_semantics_1 {T S : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_expression_semantics exp_sem
    -> _weakening_of_statement_semantics_1 stmt_sem 
    -> _weakening_of_statement_semantics_1 (@generic_stmt_sem T S exp_sem stmt_sem)
.
Proof with eauto using refl_env_mem_partial_order,env_partial_order_add with rac_hint.
    intros exp_sem stmt_sem Hext_exp Hext_stmt  Ω₀ M₀ s Ω₁ M₁. 
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
        *   destruct IHHderiv1 with Ω₀' M₀' as [I1env [I1mem [I1Hrel I1Hderiv]]]...
            destruct IHHderiv2 with I1env I1mem as [I2env [I2mem [I2Hrel I2Hderiv]]]... 

        (* f call *)
         * specialize IHHderiv with (p_map_addall (H:=eqdec_v) ⊥ xargs zargs, ⊥)  M₀'. destruct IHHderiv as [env_s [mem_s [Hrel Hderiv2]]].
            + now split.
            + eexists ?[env],?[mem]. split.
                ++ instantiate (env:=((fst Ω₀') {c \ z}, snd Ω₀')). instantiate (mem:=mem_s (* or mem' ? *) ). split... easy. 
                ++ eapply S_FCall with (resf:=resf)... 
                    +++ epose proof (List.Forall2_impl (R1:=generic_exp_sem env mem) (generic_exp_sem Ω₀' M₀')) as Hforall. destruct Hforall with eargs zargs... intros.
                        apply exp_weak with env mem...
                    +++ admit.

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
        * unfold _weakening_of_statement_semantics_1 in *. specialize (Hext_stmt env mem s env' mem') .
            destruct Hext_stmt as [Hext_stmt _]. destruct s...
            + apply Hext_stmt with Ω₀' M₀' in H. destruct H as [env'' [mem'' [Hrel2 Hderiv]]]... easy. easy.   
            + apply Hext_stmt with Ω₀' M₀' in H. destruct H as [env'' [mem'' [Hrel2 Hderiv]]]... easy. easy.            
    
    - intros H. destruct H with Ω₀ M₀ as [Ω₁' [M₁' [Hrel Hderiv ]]]...
Admitted.


Fact _weakening_of_c_statements_semantics_1 : _weakening_of_statement_semantics_1 Empty_stmt_sem. 
Proof.
    unfold _weakening_of_statement_semantics_1. intros. split; unfold Empty_stmt_sem.
    - intros [].
    - intro H. destruct H with Ω₀ M₀.
        + apply refl_env_mem_partial_order.
        + destruct H0 as [_ [_ []]]. 
Qed.


Lemma _weakening_of_gmp_statements_semantics : 
    _weakening_of_statement_semantics_1 _gmp_stmt_sem
.
Proof with eauto using eq_env_partial_order, eq_mem_partial_order,refl_env_mem_partial_order with rac_hint ; try easy.
    split.
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

        * inversion H. subst. eexists (((fst Ω₀') {x \ VInt (Int.mkMI z  ir)}, snd Ω₀')), M₀'... split.
            + split... pose env_partial_order_add...
            + apply S_get_int with v... apply weak_exp...
        
        * exists Ω₀',M₀' {a \ z}. split. 
            + split... apply (mems_partial_order_add M₀ M₀' Hmem a z). 
            + constructor... eapply eq_env_partial_order...

        * inversion H. simpl in H4. simpl in H4. specialize (H4 I). inversion H4. inversion H0. simpl in H11. specialize (H11 I). inversion H11. subst. 
            eexists ((fst Ω₀') {c \ b}, snd Ω₀'),M₀'. split.
            ** split... pose env_partial_order_add...
            ** apply S_cmp with vx vy lx ly...
                + constructor. simpl. intros []. apply GMP_E_Var with z.
                    ++ eapply eq_env_partial_order...
                    ++ apply (eq_mem_partial_order M₀ M₀')...
                + constructor. simpl. intros []. apply GMP_E_Var with z0.
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
    
    - intro H. induction s ; specialize H with Ω₀ M₀ ; destruct H as [env [mem [Hrel Hderiv]]]... induction Hderiv...
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
Admitted.

Definition weakening_of_gmp_statements_semantics := 
    weakening_of_statement_semantics_1 _gmp_exp_sem _gmp_stmt_sem _weakening_of_gmp_expression_semantics _weakening_of_gmp_statements_semantics
.


(* 2 *)


Definition _weakening_of_statement_semantics_2  {T S : Set} (stmt_sem : @stmt_sem_sig T S) := 
    forall Ω₀ Ω₀' M₀ M₀' s Ω₁ M₁,
    stmt_sem Ω₀ M₀ s Ω₁ M₁ /\ (Ω₀, M₀) ⊑ (Ω₀', M₀')  ->
    (
        forall Ω₁' M₁',
        stmt_sem Ω₀' M₀' s Ω₁' M₁'->
        (forall (v:𝓥),v ∉ fst Ω₀ -> fst Ω₀' v = fst Ω₁' v) 
        /\
        (forall (x:location) (v:𝓥), (fst Ω₀ v) <> Some (VMpz x) -> M₀' x = M₁' x)
    ).
    

Lemma weakening_of_statement_semantics_2 {T S : Set} : 
    forall exp_sem stmt_sem, 
    _determinist_exp_eval exp_sem ->
    _weakening_of_expression_semantics exp_sem
    -> _weakening_of_statement_semantics_2 stmt_sem 
    -> _weakening_of_statement_semantics_2 (@generic_stmt_sem T S exp_sem stmt_sem)
.
Proof with auto with rac_hint.
    intros exp_sem stmt_sem ext_exp_deter ext_exp_weak ext_stmt_weak Ω₀ Ω₀' M₀ M₀' s Ω₁ M₁ [Hderiv1 Hrel]. generalize dependent Ω₀'. generalize dependent M₀'. 
    pose proof (weakening_of_expression_semantics exp_sem ext_exp_weak) as exp_weak.
    unfold _weakening_of_statement_semantics_2 in ext_stmt_weak.
    induction Hderiv1 ; intros M₀' Ω₀' Hrel Ω₁ M₁ Hderiv2 ; inversion Hderiv2 ; subst ; try easy...
    
    (* assign *)
    - admit.
    
    (* specialize ext_stmt_weak with (Ω₀:=env) (M₀:=mem) (Ω₁:= Ω₁) (M₁:=M₁). apply ext_stmt_weak in H. easy. split...   admit. *)

    (* if false *)
    - apply IHHderiv1... destruct H. specialize (exp_weak e env mem z). rewrite exp_weak in H. specialize (H Ω₀' M₀' Hrel). 
            apply determinist_exp_eval in H5. apply H5 in H. now subst. assumption.

    (* if true *)
    -  destruct H5. specialize (exp_weak e env mem zero). rewrite exp_weak in H. specialize (H Ω₀' M₀' Hrel).
            apply determinist_exp_eval in H0. apply H0 in H. now subst. assumption.

    (* seq *)
    - admit. 
    (* fcall *)
    - admit.
    (* pcall *)
    - admit.

    (* return *)
    - unfold _weakening_of_expression_semantics in exp_weak. apply exp_weak with (env':=Ω₀') (mem' := M₁) in H... 
            apply determinist_exp_eval in H... apply H in H1. split. intros. simpl. assert (v <> resf0). admit. symmetry. apply p_map_not_same... easy.
     
    (* assert *)
    - destruct s ; try easy.
        1-2 : (inversion Hderiv2 ; subst ; specialize (H I) ; specialize (H0 I) ; eapply ext_stmt_weak with ( Ω₀:=env) ( M₀:=mem) (Ω₁:=env') (M₁:=mem') in H0)...
Admitted.


(* 3 *)
Definition _weakening_of_statement_semantics_3  {T S : Set} (stmt_sem : @stmt_sem_sig T S) := 
    forall Ω₀ M₀  s Ω₁ M₁,
    stmt_sem Ω₀ M₀ s Ω₁ M₁ -> 
    (
        forall Ω₀' M₀', (Ω₀', M₀') ⊑ (Ω₀, M₀) ->
        (
            (forall v, (dom (fst Ω₀) - dom (fst Ω₀')) v /\ ~ List.In v (stmt_vars s))
            /\
            (forall x v, (dom M₀ - dom M₀') x -> (fst Ω₀) v = Some (VMpz x) /\ ~ List.In v (stmt_vars s))
        ) ->

        exists Ω₁' M₁', stmt_sem Ω₀' M₀' s Ω₁' M₁'
    ).

Lemma weakening_of_statement_semantics_3 {T S : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_expression_semantics exp_sem
    -> _weakening_of_statement_semantics_3 stmt_sem 
    -> _weakening_of_statement_semantics_3 (@generic_stmt_sem T S exp_sem stmt_sem)
.

Proof with auto with rac_hint.
    intros exp_sem stmt_sem ext_exp_weak ext_stmt_weak Ω₀ M₀ s Ω₁ M₁ Hderiv Ω₀' M₀' Hrel [Henv Hmem].  induction Hderiv.
    (* skip *)
    - exists Ω₀', M₀'. constructor.
    (* assign *)
    - destruct Henv with x. destruct H1. destruct H3. admit.
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
    - admit.
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
        * destruct t... inversion H1. subst. constructor. intros []. apply GMP_E_Var with z0... simpl.
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
    - destruct ty; inversion H1 ; subst; try specialize (H2 I)...
        * now constructor.
        * destruct t... inversion H2. subst. constructor. intros []. apply GMP_E_Var with z0... 
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
        + subst. rewrite <- H3. apply p_map_not_same. admit. (* need to show there is no aliasing *)
Admitted.

Lemma semantics_of_the_mpz_assgn_macro :
    forall e z Ω M v (y:location),
    Ω ⋅ M |= e ⇝ z ->
    (fst Ω) v = Some (VMpz y) ->
    Ω ⋅ M |= (mpz_ASSGN v e) => Ω ⋅ M{y\z}
.
Proof.
    intros. 
    unfold mpz_ASSGN. destruct (ty e) eqn:TY.
    - inversion H ; constructor.
        * simpl. intros []. now apply S_set_i.
        * inversion H1. simpl. intros []. subst. destruct e ; try easy ; destruct ty ; try easy.
    - unfold ty in TY. destruct e; try easy. subst. inversion H ; inversion H1.
        + specialize  (H3 I). now inversion H1.
        + specialize (H4 I). now inversion H1.
    - destruct t.
        * destruct H; destruct H ; try easy ; destruct e ; destruct ty ; try easy ; specialize (H I) ; inversion H ; now subst. 
        * destruct e; try easy. inversion H.
            ** inversion H1 ; subst.
                + discriminate.
                + destruct ty ; try easy.  now specialize (H3 I). 
            ** inversion H1 ; subst. destruct ty ; try easy.
                + specialize (H4 I).  inversion H4. constructor. simpl. intros []. now apply S_set_z with l.
Qed.

Lemma semantics_of_the_int_assgn_macro :
    forall e z (ir: Int.inRange z) Ω M v,
    Ω ⋅ M |= e ⇝ z ->
    type_of_value ((fst Ω) v) = Some C_Int ->
    Ω ⋅ M |= (int_ASSGN v e) => ((fst Ω){v\z ⁱⁿᵗ ir : 𝕍}, snd Ω) ⋅ M
.
Proof with eauto with rac_hint.
    intros. 
    unfold int_ASSGN. destruct (ty e) eqn:TY.
    - inversion H.  
        * apply S_Assign... subst. rewrite (x_of_z_to_z_is_x x ir). inversion H1 ; subst.
            ** constructor.
            ** constructor... 
            ** apply C_E_BinOpInt with z_ir z'_ir ; admit.
            ** apply C_E_BinOpTrue with z z' z_ir z'_ir; admit.
            **apply C_E_BinOpFalse with z z' z_ir z'_ir ; admit.
            ** destruct e; try easy. now destruct ty.
        * inversion H1. destruct e ; try  inversion H4 ; subst. destruct ty; try easy.

    -  inversion H. inversion H1 ; subst ; try easy. destruct e; try easy. destruct ty ; try easy.
        + specialize (H3 I). inversion H3.
        + subst. inversion H1. subst. destruct e ; try easy. destruct ty ; try easy. specialize (H3 I). inversion H3.

    - inversion H ; subst. inversion H1; subst ; try easy.
        + destruct e ; try easy. destruct ty ; try easy. specialize (H2 I). inversion H2.
        + inversion H1. subst.  destruct e; try easy. destruct ty ; try easy. specialize (H3 I). inversion H3. subst.
            destruct t ; subst ; try easy. constructor. simpl. intros [].  apply S_get_int with l...
Admitted.

Lemma semantics_of_the_Z_assgn_macro_tint :
    forall z (ir: Int.inRange z) Ω M v,
    type_of_value ((fst Ω) v) = Some C_Int ->
    Ω ⋅ M |= (Z_ASSGN C_Int v z) => ((fst Ω){v\z ⁱⁿᵗ ir : 𝕍}, snd Ω) ⋅ M
.
Proof.
    intros.  constructor ; auto with rac_hint.
Qed.

Lemma semantics_of_the_Z_assgn_macro_tmpz :
    forall y (z:ℤ) Ω M v,
    (fst Ω) v = Some (VMpz y) ->
    Ω ⋅ M |= (Z_ASSGN Mpz v z) => Ω ⋅ M{y\z}
.
Proof with auto using BinaryString.Z_of_of_Z.
    intros. simpl. constructor. simpl. intros []. apply S_set_s...
Qed.


Lemma semantics_of_the_cmp_macro :
    forall (Ω:Ω) (M:𝓜) c e1 e2 v1 v2 z1 z2 l1 l2 a,
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
    Ω ⋅ M |= (CMP c e1 e2 v1 v2) => ((fst Ω){c\a}, snd Ω) ⋅ M'
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
        Ω ⋅ M |= <{(mpz_ASSGN v1 e1); (mpz_ASSGN v2 e2); <c = cmp (v1, v2)>}> => ((fst Ω) {c \ a}, snd Ω) ⋅ M'
    ). {
        exists M{l2 \ z2, l1 \ z1}. intros VN Hv1NotIne2 Hl1Notl2.
        apply S_Seq with Ω M{l1\z1}.
        - apply semantics_of_the_mpz_assgn_macro...
        - apply S_Seq with Ω M{l2\z2,l1\z1}.  
            + apply semantics_of_the_mpz_assgn_macro... inversion H1.
                * subst. constructor. apply same_eval_mem with v1...
                * subst. econstructor. apply same_eval_mem with v1... rewrite <- H5. apply p_map_not_same. admit. (* need to show there is no aliasing *)
            + constructor. simpl. intros []. apply S_cmp with (vx:=l1) (vy:=l2) (lx:=z1) (ly:=z2)...
                * constructor. simpl. intros []. apply GMP_E_Var with z1. assumption. apply p_map_not_same_eq ; [easy|apply p_map_same] .
                * constructor. simpl. intros []. apply GMP_E_Var with z2. assumption. apply p_map_same.
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
    forall (Ω:Ω) (M:𝓜) (op:fsl_binop_int) c r e1 e2 v1 v2 z1 z2 (ir: Int.inRange (⋄ (□ op) z1 z2) ) l1 l2 lr,
    type_of_value ((fst Ω) c) = Some C_Int ->
    Ω ⋅ M |= e1 ⇝ z1 ->
    Ω ⋅ M |= e2 ⇝ z2 ->
    let zr := ⋄ (□ op) z1 z2 in

    (fst Ω) v1 = Some (VMpz l1) /\  (fst Ω) v2 = Some (VMpz l2) /\ ( (fst Ω) r = Some (VMpz lr) ) ->
    exists M', (forall v n, (fst Ω) v = Some (VMpz n) ->
    ~ ((fst Ω) v1 = (fst Ω) v) /\ ~ ((fst Ω) v2 = (fst Ω) v)  -> M n = M' n) -> 
    ~ List.In v1 (exp_vars e2) -> (* not in paper proof *)
    l1 <> l2 -> (* not in paper proof *)
    Ω ⋅ M |= (binop_ASSGN op (C_Int,c) e1 e2 r v1 v2) => ((fst Ω){c\zr ⁱⁿᵗ ir : 𝕍}, snd Ω) ⋅ M'
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
        Ω ⋅ M |= <{
            (mpz_ASSGN v1 e1);
            (mpz_ASSGN v2 e2);
            (Definitions.op op r v1 v2);
            (int_ASSGN c (C_Id r Mpz))
        }> => ((fst Ω) {c \ zr ⁱⁿᵗ ir : 𝕍}, snd Ω) ⋅ M'
    ). {
        exists M{lr\zr,l2\z2,l1\z1}. intros. 
    apply S_Seq with Ω M{l1\z1}. 
    - apply semantics_of_the_mpz_assgn_macro...
    - apply S_Seq with Ω M{l2\z2,l1\z1}.
     + apply semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
     + apply S_Seq with Ω M{lr\zr,l2\z2,l1\z1}.
        * constructor. pose proof (p_map_not_same M{l1 \ z1}) l1 l2 z2 H4. simpl. intros []. apply S_op with l1 l2...
            ** constructor. simpl. intros []. apply GMP_E_Var with z1...  rewrite H5. apply p_map_same.
            ** apply p_map_not_same_eq ; [easy|apply p_map_same].
            ** constructor. simpl. intros []. apply GMP_E_Var with z2...
        * apply semantics_of_the_int_assgn_macro...  apply M_Mpz with lr.
            ++ constructor. simpl. intros []. apply GMP_E_Var with zr... 
            ++ apply p_map_same.
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
    forall (Ω:Ω) (M:𝓜) (op:fsl_binop_int) c y r e1 e2 v1 v2 z1 z2 l1 l2,
    type_of_value ((fst Ω) c) = Some C_Int ->
    Ω ⋅ M |= e1 ⇝ z1 ->
    Ω ⋅ M |= e2 ⇝ z2 ->
   
    let zr := ⋄ (□ op) z1 z2 in
    (fst Ω) v1 = Some (VMpz l1) /\  (fst Ω) v2 = Some (VMpz l2) /\  (fst Ω) c = Some (VMpz y) ->
    ~ List.In v1 (exp_vars e2) -> (* not in paper proof *)
    exists M', (forall v n, (fst Ω) v = Some (VMpz n) ->
    ~ ((fst Ω) v1 = (fst Ω) v) /\ ~ ((fst Ω) v2 = (fst Ω) v)  -> M n = M' n) -> 
    l1 <> l2 -> (* not in paper proof *)
    Ω ⋅ M |= (binop_ASSGN op (T_Ext Mpz,c) e1 e2 r v1 v2) => Ω ⋅ M'{y\zr}
    .
Proof with eauto using p_map_same with rac_hint.
    intros. exists M{l2\z2,l1\z1}. intros. destruct H2 as (v1l & v2l & rl). unfold binop_ASSGN.
    apply S_Seq with Ω M{l1\z1}.
    - apply semantics_of_the_mpz_assgn_macro...
    - apply S_Seq with Ω M{l2\z2,l1\z1}. 
        * apply semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
        * constructor. pose proof (p_map_not_same M{l1 \ z1}) l1 l2 z2 H5. simpl. intros [].  apply S_op with l1 l2...
            + constructor. simpl. intros []. apply GMP_E_Var with z1... rewrite H2...
            + rewrite H2...
            + constructor. simpl. intros []. apply GMP_E_Var with z2...
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
