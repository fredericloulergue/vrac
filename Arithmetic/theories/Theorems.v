Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import RAC.Semantics.
Require Import RAC.Translation.
Require Import  Strings.String.
From Coq Require Import ZArith.ZArith.

Open Scope utils_scope.
Open Scope definition_scope.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.

(* Properties of the semantics *)



Definition _no_env_mpz_aliasing (ev : Ω) : Prop := 
    forall v v' l l', 
    v <> v' ->
    ev v = Some (Def (VMpz (Some l)))  ->
    ev v' = Some (Def (VMpz (Some l'))) -> 
    l <> l'.

Definition _no_mem_aliasing {S T : Set} (stmt_sem : @stmt_sem_sig S T)  : Prop := 
    forall (exp_sem:@exp_sem_sig T) f (ev:Env) s (ev':Env), 
    _no_env_mpz_aliasing ev
    -> stmt_sem f ev s ev' 
    -> _no_env_mpz_aliasing ev'.


Fact _no_mem_aliasing_gmp : _no_mem_aliasing _gmp_stmt_sem.
Proof with auto with rac_hint.
    intros exp_sem f ev s ev' Hnoalias H. induction H
    ; auto ;  try (rename v into l1) ;
    intros v v' ll l' Hvv' Hl Hl' leq ; subst ; autounfold with rac_hint in * ; simpl in *.
    - destruct (eq_dec x v).
        + subst. autounfold with rac_hint in *. rewrite p_map_same in Hl. rewrite p_map_not_same in Hl'... inversion Hl. 
            subst. now destruct H with v'.
        + rewrite p_map_not_same in Hl... destruct (eq_dec x v').
            * subst. rewrite p_map_same in Hl'. inversion Hl'. subst. now destruct H with v.
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
    - destruct (string_dec x v').
        + subst. rewrite p_map_same in Hl'. discriminate.
        + rewrite p_map_not_same in Hl'... destruct (string_dec x v).
            * subst. rewrite p_map_same in Hl. discriminate.
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

Fact eq_env_partial_order :  forall e e' v z, (e ⊑ e')%env ->  
    e v = Some (Def z) -> e' v = Some (Def z).
Proof.
    intros e e' v z Hrel He. destruct Hrel with v; congruence.
Qed.

Fact sym_env_cond : forall (env env' : Ω), 
(forall v, (dom env - dom env') v ) -> (env ⊑ env')%env -> (env' ⊑ env)%env.

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

Corollary sym_env_cond_mem : forall (ev ev' : Env), 
(forall v, (dom ev - dom ev') v ) -> (ev ⊑ ev')%envmem ->  (mkEnv ev' ev ⊑ mkEnv ev ev')%envmem.
Proof.
    intros [env mem]. split. now apply sym_env_cond. now destruct H0.
Qed.




Corollary eq_env_partial_order_add :  forall (e e' :Ω) v v' z z',  (e ⊑ e')%env ->  
    v <> v' ->
    e v = Some (Def z) -> (e'{v'\z'}) v = Some (Def z).
Proof.
    intros [v l] [v' l'] var var' z z' Hrel Hneq H. 
    pose proof (eq_env_partial_order {|vars:=v;binds:=l|} {|vars:=v';binds:=l'|} var z Hrel H).
    pose proof (p_map_not_same {| vars := v'; binds := l' |} var var' z' Hneq). congruence.
Qed.


Fact eq_mem_partial_order :  
    forall mem mem' z l, (mem ⊑ mem')%mem -> z <> None ->  
    mem l = z ->  mem' l = z.
Proof.
    intros. destruct z.
    - edestruct H; eauto.
    - contradiction.
Qed.



Fact env_partial_order_add : forall Ω₀ Ω₀', (Ω₀ ⊑ Ω₀')%env -> 
    (forall var' z, 
    Ω₀ <| vars ::= fun x => x{var' \ z} |> ⊑  Ω₀' <| vars ::= fun x => x{var' \ z} |>
    )%env.
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
            + { 
                destruct v0.
                - apply EsameInt with n ; simpl.
                    + apply H0.
                    + apply p_map_not_same_eq in H0... epose proof (eq_env_partial_order_add  _ _ _ _ _ _ H). 
                        now apply H1.
                - apply EsameMpz with l0; simpl... epose proof (eq_env_partial_order_add  _ _ _ _ _ _ H).
                    symmetry in Heqres. specialize (H1 Hneq Heqres). simpl in H1. apply H1.
            }

            + {
                destruct uv.
                - eapply EundefInt ;subst ;simpl. 
                    + apply H0.
                    + destruct H with var ; pose proof (p_map_not_same_eq v' var x z) as Hres; simpl in *; try congruence.
                        destruct H2.
                        * specialize (Hres  (Some (Undef (UInt n))) Hneq). left. apply Hres. congruence.
                        * destruct H2 as [x0]. specialize (Hres  (Some (Def (VInt x0))) Hneq). right. exists x0. now apply Hres.
                - eapply EundefMpz ; subst ; simpl.
                    + apply H0.
                    + destruct H with var ; pose proof (p_map_not_same_eq v' var x z) as Hres; simpl in * ; try congruence.
                        destruct H2.
                        * specialize (Hres  (Some (Undef (UMpz l0))) Hneq). left.  apply Hres. congruence.
                        * destruct H2 as [l0']. specialize (Hres  (Some (Def (VMpz l0'))) Hneq). right. exists l0'. now apply Hres.
            }
        * now apply Enone.
Qed.

Fact mems_partial_order_add : forall M₀ M₀', mems_partial_order M₀ M₀' -> 
    (forall l mi, mems_partial_order ((M₀) {l \ mi}) ((M₀') {l \ mi})).
Proof.
    intros mem mem' H l mi. intros l' i H1. destruct (eq_dec l' l).
    - subst. pose proof (p_map_same mem l mi). rewrite H0 in H1. injection H1 as eq. subst.  apply p_map_same.
    - pose proof (p_map_not_same mem l' l mi n). rewrite H0 in H1. apply p_map_not_same_eq ; auto.
Qed.


Fact env_same_ty : forall  (Ω Ω' : Ω) v t, (Ω ⊑ Ω')%env -> t <> None -> type_of_value (Ω v) = t -> type_of_value (Ω' v) = t.
Proof.
    intros. 
    match goal with | IncRel : (_ ⊑ _)%env |- _ =>  destruct IncRel with v ; subst end;
    match goal with 
    | L : apply_env Ω v = _,  R : apply_env Ω' v = _  |- _ => now rewrite L,R 
    | L : apply_env Ω v = _,  R : apply_env Ω' v = _ \/ _ |- _ => destruct R as [SomeUInt | [ x Some_n ]]; [now rewrite L,SomeUInt | now rewrite L,Some_n] 
    | L : _ = None,  Contra : _ <> None |- _ =>  now rewrite L in Contra
    end.
Qed.

Definition _determinist_exp_eval {T : Set} (exp_sem : @exp_sem_sig T) : Prop := 
    forall e ev v,  exp_sem ev e v ->  (forall v', exp_sem ev e v' -> v = v')
.

Fact determinist_exp_eval {T : Set}: 
forall ext_exp_sem, _determinist_exp_eval ext_exp_sem -> _determinist_exp_eval (@generic_exp_sem T ext_exp_sem).
Proof.
    intros ext_exp_sem ext_inj. unfold _determinist_exp_eval. intros e. induction e ; intros ; inversion H ; inversion H0 ; subst ; try easy.
    5,6:
        apply IHe1 with (v:=VInt (z ⁱⁿᵗ z_ir)) (v':=VInt (z0 ⁱⁿᵗ z_ir0)) in H11 ; [|assumption] ; injection H11 as eqz ;
        apply IHe2 with (v:=VInt (z' ⁱⁿᵗ z'_ir)) (v':= VInt (z'0 ⁱⁿᵗ z'_ir0)) in H13; [|assumption] ;  injection H13 as eqz' ; subst ; now rewrite H14 in H7.
    - f_equal. f_equal. now apply Int.mi_eq. 
    - congruence.
    - destruct ty. easy. 1,2: apply ext_inj in H6 ; now apply H6 in H12.
    - f_equal. f_equal. apply Int.mi_eq. simpl. f_equal.
        + apply IHe1 with (v:=VInt (z ⁱⁿᵗ z_ir)) (v':= VInt (z0 ⁱⁿᵗ z_ir0)) in H13; [|assumption]. now injection H13. 
        + apply IHe2 with (v:=VInt (z' ⁱⁿᵗ z'_ir)) (v':=VInt (z'0 ⁱⁿᵗ z'_ir0)) in H14; [|assumption]. now injection H14.
Qed.

Fact _determinist_c_exp_eval : _determinist_exp_eval Empty_exp_sem.
Proof. easy. Qed.

Definition determinist_c_exp_eval := determinist_exp_eval Empty_exp_sem _determinist_c_exp_eval.

Fact _determinist_gmp_exp_eval :  _determinist_exp_eval _gmp_exp_sem.
Proof.
    unfold _determinist_exp_eval. intros e. induction e ; intros ev v H v' H0. inversion H ; inversion H0 ; subst.
    - inversion H ; inversion H0 ; subst ; try easy. rewrite H3 in H8.  repeat f_equal. now injection H8. 
    - inversion H.
    - inversion H.
Qed.

Definition determinist_gmp_exp_eval := determinist_exp_eval _gmp_exp_sem _determinist_gmp_exp_eval.

Fact Forall2_same_zargs { T : Set} : forall ev eargs zargs zargs0  exp_sem, 
    _determinist_exp_eval exp_sem
    -> List.Forall2 (@generic_exp_sem T exp_sem ev) eargs zargs 
    -> List.Forall2 (@generic_exp_sem T exp_sem ev) eargs zargs0 -> zargs = zargs0.
Proof.
    intros ev eargs zargs zargs0 exp H  Hderiv. generalize dependent zargs0. induction Hderiv ; intros zargs0 H1.
    - now inversion H1.
    - destruct zargs0. inversion H1. apply List.Forall2_cons_iff in H1 as [H1 Hderiv2].
        apply determinist_exp_eval in H0 ; [|assumption]. apply H0 in H1. subst. f_equal. clear H0.
        now apply IHHderiv in Hderiv2.
Qed.

Definition _determinist_stmt_eval {S T : Set} (ext_exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) : Prop := 
    @_determinist_exp_eval T ext_exp_sem  -> 
    forall f s ev ev',  stmt_sem f ev s ev' ->  (forall ev'', stmt_sem f ev s ev'' -> ev' = ev'').


Fact determinist_stmt_eval {S T : Set}: 
    forall ext_exp_sem ext_stmt_sem, 
    @_determinist_stmt_eval S T ext_exp_sem ext_stmt_sem -> 
    _determinist_stmt_eval ext_exp_sem (@generic_stmt_sem S T ext_exp_sem ext_stmt_sem).
Proof with auto. 
    intros ext_exp_sem ext_stmt_sem Hds Hde f s ev ev' Hderiv. induction Hderiv ; intros.
    - inversion H... 
    - inversion H3 ; subst... repeat f_equal.  apply determinist_exp_eval in H2... apply H2 in H10. now subst.
    - inversion H1 ; subst...  apply determinist_exp_eval in H6... destruct H. apply H6 in H. now symmetry in H.
    - inversion H1 ; subst... apply determinist_exp_eval in H... destruct H6. apply H in H2. now symmetry in H2. 
    - inversion H0... 
    - inversion H1 ; subst... apply IHHderiv in H4. subst. apply IHHderiv0 in H6. now subst. 
    - inversion H5 ; subst. 
       (* same args, same body *) 
            rewrite H10 in H0. injection H0 as H0. subst.
            (* same args eval *) 
            assert (zargs = zargs0) by auto using (@Forall2_same_zargs T ev eargs zargs zargs0 ext_exp_sem). 
            subst. apply IHHderiv in H12. subst. rewrite H4 in H15. injection H15 as H15. now subst.
    - inversion H3.  subst.  rewrite H7 in H0. injection H0 as Eq1. subst. 
            assert (zargs = zargs0) by eauto using (@Forall2_same_zargs T _ eargs zargs zargs0 ext_exp_sem). subst. 
            apply IHHderiv in H10. now subst.
    - inversion H0 ; subst... apply determinist_exp_eval in H... apply H in H2. injection H2 as H2. now subst.
    - inversion H1...
    - inversion H0. subst. unfold _determinist_stmt_eval in Hds. eapply Hds... apply H. apply H2.
Qed.

Fact _determinist_c_stmt_eval : _determinist_stmt_eval Empty_exp_sem Empty_stmt_sem. easy. Qed.

Definition determinist_c_stmt_eval := determinist_stmt_eval Empty_exp_sem Empty_stmt_sem _determinist_c_stmt_eval.


Definition _weakening_of_expression_semantics {T : Set} (exp_sem : @exp_sem_sig T) : Prop := 
    forall e ev (x:𝕍), 
    exp_sem ev e x <-> (forall ev',  (ev ⊑ ev')%envmem -> exp_sem ev' e x).


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
            constructor... inversion H3. apply eq_env_partial_order with ev... 
Qed.

Fact _weakening_of_c_expression_semantics : _weakening_of_expression_semantics Empty_exp_sem. 
Proof.
    unfold _weakening_of_expression_semantics. intros. split ; unfold Empty_exp_sem.
    - intros [].
    - intro H. apply H with ev... apply refl_env_mem_partial_order.
Qed.

Definition weakening_of_c_expression_semantics := 
    weakening_of_expression_semantics Empty_exp_sem _weakening_of_c_expression_semantics.

Lemma _weakening_of_gmp_expression_semantics : 
    _weakening_of_expression_semantics _gmp_exp_sem
.
Proof with (eauto with rac_hint; try easy).
    split.
    - intro H. inversion H. subst. intros. apply GMP_E_Var with z; destruct H2 as [relEnv memEnv]. 
        + eapply eq_env_partial_order...
        + eapply eq_mem_partial_order... 
    - intros. specialize H with ev. now apply H.
Qed.

Definition weakening_of_gmp_expression_semantics := 
    weakening_of_expression_semantics _gmp_exp_sem _weakening_of_gmp_expression_semantics.

Definition _untouched_var_same_eval_exp {T : Set} (exp_sem : @exp_sem_sig T) := 
    forall (ev:Env) (e: @_c_exp T) v x,
    ~ List.In v (exp_vars e) -> 
    exp_sem ev e x ->
    (forall x', exp_sem (ev <| env ; vars ::= {{v\x'}} |>)  e x)
    /\ 
    (forall l z', 
    _no_env_mpz_aliasing ev ->
    ev v = Some (Def (VMpz (Some l))) -> exp_sem (ev <| mstate ::= {{l\z'}} |>) e x).

Fact untouched_var_same_eval_exp {T : Set} : forall exp_sem, 
    _untouched_var_same_eval_exp exp_sem ->
    _untouched_var_same_eval_exp (@generic_exp_sem T exp_sem).
Proof with eauto with rac_hint.
    intros exp_sem Hext ev e v x Hnotin Hderiv. induction Hderiv ; simpl in Hnotin...
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
    intros ev e v x Hnotin Hderiv. inversion Hderiv. subst. simpl in Hnotin.
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
    forall f ev ev' (s: @_c_statement S T) x, 
    stmt_sem f ev s ev' ->
    ~ List.In x (stmt_vars s) /\ is_comp_var x = false -> 
    ev x = ev' x
    .


Fact untouched_var_same_eval_stmt {S T : Set} : 
    forall exp_sem stmt_sem, 
    _untouched_var_same_eval_stmt exp_sem stmt_sem ->
    _untouched_var_same_eval_stmt exp_sem (@generic_stmt_sem S T exp_sem stmt_sem).
Proof.
    intros exp_sem stmt_sem Hext f ev ev' s x Hderiv [Hnotin Huservar]. induction Hderiv ; simpl in Hnotin; trivial.
    - subst. apply Decidable.not_or_iff in Hnotin as [Hdiffxresf]. simpl. autounfold with rac_hint. rewrite p_map_not_same.
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
    - simpl. symmetry. apply p_map_not_same_eq ; auto.
    (* return *)
    - simpl. destruct (eq_dec res_f x). subst. 
        * discriminate.
        * autounfold with rac_hint. symmetry. rewrite p_map_not_same_eq. auto. congruence.  
    - eapply Hext in H ; eauto.
Qed.




Definition _weakening_of_statement_semantics_1  {S T : Set} (exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) := 
    _weakening_of_expression_semantics exp_sem ->
    forall (f : @fenv S T) ev₀ s ev₁,
    stmt_sem f ev₀ s ev₁ <->
    ( forall ev₀', (ev₀  ⊑ ev₀')%envmem ->
    exists ev₁' , (ev₁  ⊑ ev₁')%envmem /\ stmt_sem f ev₀' s ev₁').
    

Lemma weakening_of_statement_semantics_1 {S T : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_statement_semantics_1 exp_sem stmt_sem 
    -> _weakening_of_statement_semantics_1 exp_sem (@generic_stmt_sem S T exp_sem stmt_sem)
.
Proof with eauto using refl_env_mem_partial_order,env_partial_order_add with rac_hint.
    intros exp_sem stmt_sem Hext_stmt Hext_exp f ev₀ s ev₁. 
    pose proof (weakening_of_expression_semantics exp_sem Hext_exp) as exp_weak.
    split.
    - intro Hderiv. induction Hderiv ; intros ev₀' [Henv Hmem].
        (* skip *)
        * exists ev₀'... 
        
        (* assign *) 
        * exists (ev₀' <| env ; vars ::= {{x \ z}} |>). split. 
            + split... simpl. apply env_partial_order_add... 
            + apply S_Assign...
                *** now apply env_same_ty with ev. 
                *** rewrite (exp_weak e) in H2. specialize (H2 ev₀'). apply H2...


        (* if true *)
        * destruct H. destruct (IHHderiv ev₀') as [ev_s [[Henv2 Hmem2] Hderiv2]]... exists ev_s. intros . split...
            apply S_IfTrue with z. split...
            rewrite  (exp_weak e) in H... apply Hderiv2...
        (* if false *)
        * destruct (IHHderiv ev₀') as [ev_s [[Henv2 Hmem2] Hderiv2]]... exists ev_s. split...
            apply S_IfFalse...
            rewrite  (exp_weak e) in H... 


         (* while *)
        * destruct (IHHderiv ev₀') as [ev_s [[Henv2 Hmem2] Hderiv2]]... 


        (* c seq *)
        * destruct IHHderiv with ev₀' as [I1ev [I1Hrel I1Hderiv]]...
            destruct IHHderiv0 with I1ev as [I2ev [I2Hrel I2Hderiv]]... 

        (* f call *)
         * edestruct IHHderiv as [e_s [Hrel Hderiv2]].
            + now split.
            + eexists (ev₀' <| env; vars ::= {{c \Def z}} |> <| mstate := ev' |>). split.
                ++ split... apply env_partial_order_add... easy. 
                ++ eapply S_FCall... 
                    +++ epose proof (List.Forall2_impl (R1:=generic_exp_sem ev) (generic_exp_sem ev₀')) as Hforall. destruct Hforall with eargs zargs...
                        intros...
                    apply exp_weak with ev...
        (* p call *)
        *  edestruct IHHderiv as [ev_s [Hrel Hderiv2]].
            + now split... 
            + eexists (_ <| mstate := _ |>)... simpl. split.
                ++ destruct Hrel. split...
                ++ eapply S_PCall ...
                    +++ epose proof (List.Forall2_impl (R1:=generic_exp_sem ev) (generic_exp_sem ev₀')) as Hforall. destruct Hforall with eargs zargs...
                        intros. apply exp_weak with ev...

        (* return *)
        * exists (ev₀' <| env ; vars ::= {{res_f \Def z}} |>). split.
            + split... apply env_partial_order_add...
            + apply S_Return... apply (exp_weak e ev z)...

        (* assert *)
        * exists ev₀'. split... apply S_PAssert with z...
            apply (exp_weak e ev z)...

        (* other cases *)
        * specialize (Hext_stmt Hext_exp f ev (S_Ext s) ev').
            apply Hext_stmt with ev₀' in H. destruct H as [ev'' [Hrel2 Hderiv]]... easy.
                
    - intros H. admit. (* ??? *)
        
Admitted.


Fact _weakening_of_c_statements_semantics_1 : _weakening_of_statement_semantics_1 Empty_exp_sem Empty_stmt_sem. 
Proof.
    unfold _weakening_of_statement_semantics_1. intros. split; unfold Empty_stmt_sem.
    - intros [].
    - intro H2. destruct H2 with ev₀.
        + apply refl_env_mem_partial_order.
        + destruct H0 as [_  []]. 
Qed.


Lemma _weakening_of_gmp_statements_semantics_1 : 
    _weakening_of_statement_semantics_1 _gmp_exp_sem _gmp_stmt_sem
.
Proof with eauto using eq_env_partial_order, eq_mem_partial_order,refl_env_mem_partial_order with rac_hint ; try easy.
    intros Hweak f ev₀ s ev₁. split.
    - intro Hderiv. induction Hderiv; intros ev₀' [Henv Hmem] ;
        pose proof (fun y => weakening_of_gmp_expression_semantics y ev₀) as weak_exp. 

        (* init *)
        * exists (ev₀' <| env ; vars ::= {{x \ Def (VMpz (Some l))}} |> <| mstate ::= {{l \Defined 0}} |> ). split.
            + split. 
                ++ apply env_partial_order_add... 
                ++ apply mems_partial_order_add...
            + apply S_init.
                ++ intros v Hcontra. 
                    (* the fact v is not bound to mpz location l by Ω₀ doesn't mean 
                        that v will also not be bound to mpz location l by Ω₀' 
                    *) 
                    admit.
                ++ (* the semantic of ⊑ only ensures a defined mpz must stay the same, 
                        but here, x points to an undefined mpz value so it can be either stay like so or
                        be defined 
                    *)
                    admit.
        (* clear *)
        * exists (ev₀' <| env ; vars ::= {{x\Def (VMpz None)}} |><| mstate ::= {{a \ Undefined u}} |>). split.
            + split.
                ++ apply env_partial_order_add...
                ++ apply mems_partial_order_add...
            + constructor... 

        * exists (ev₀' <| mstate ::= {{a \ Defined (z) ̇}} |>). split.
            + split... intro n. apply (mems_partial_order_add ev₀ ev₀' Hmem a z ̇). 
            + apply S_set_i. eapply eq_env_partial_order... apply weak_exp...

        * exists (ev₀' <| mstate ::= {{a \ z}} |>). split.
            + split... intro n0.  apply (mems_partial_order_add ev₀ ev₀' Hmem a). 
            + apply S_set_z with n.
                ++ eapply eq_env_partial_order...
                ++ eapply eq_env_partial_order...
                ++ apply (eq_mem_partial_order ev₀ ev₀')...

        * inversion H0. subst. eexists (ev₀' <| env ; vars ::= fun e =>  e{x \ Def (VInt (z ⁱⁿᵗ ir))} |>)... split.
            + split... simpl. pose proof env_partial_order_add...
            + apply S_get_int with v... apply weak_exp...
        
        * exists (ev₀' <| mstate ::= {{a \ Defined z}} |>). split. 
            + split... apply (mems_partial_order_add ev₀ ev₀' Hmem a z). 
            + constructor...

        * inversion H. subst. inversion H8. inversion H0. subst. 
            eexists (ev₀' <| env ; vars ::= fun e => e{c \ b} |>). split.
            ** split... simpl. pose env_partial_order_add...
            ** inversion H13. subst. apply S_cmp with vx vy lx ly...
                + constructor... 
                + constructor...
        
        * eexists (ev₀' <| mstate ::= {{lr \Defined (⋄ bop z1 z2)}} |>). split.
            ** split... intro n. apply mems_partial_order_add...
            **  apply S_op with vx vy ; try apply weak_exp...

        * exists (ev₀' <| env; vars ::= {{x \ u}} |>)... repeat split... now apply env_partial_order_add.
    
    - intro H. specialize (H ev₀ (refl_env_mem_partial_order ev₀))...
        destruct H as [ev₁' [Hrel Hderiv ]]... induction Hderiv.
        + admit. (* non sense ? *)
Admitted.

Definition weakening_of_gmp_statements_semantics_1 := 
    weakening_of_statement_semantics_1 _gmp_exp_sem _gmp_stmt_sem _weakening_of_gmp_statements_semantics_1.


(* 2 *)

Definition _weakening_of_statement_semantics_2  {S T : Set} (exp_sem : @exp_sem_sig T) (stmt_sem : @stmt_sem_sig S T) := 
    
    forall (f: @fenv S T) ev₀ ev₀' s ev₁,
    _determinist_exp_eval exp_sem ->
    _weakening_of_expression_semantics exp_sem ->
    stmt_sem f ev₀ s ev₁ /\ (ev₀ ⊑ ev₀')%envmem  ->
    (
        forall ev₁',
        stmt_sem f ev₀' s ev₁'->
        (* if v is a compiler variable, i.e. a function return value, v can change*)
        (forall (v:𝓥), (v ∉ ev₀) /\ is_comp_var v = false  -> ev₀' v = ev₁' v) 
        /\
        (forall (x:location) (v:𝓥), ev₀ v <> Some (Def (VMpz x)) -> ev₀'.(mstate) x = ev₁'.(mstate) x)
    ).


Lemma weakening_of_statement_semantics_2 {S T : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_statement_semantics_2 exp_sem stmt_sem 
    -> _weakening_of_statement_semantics_2 exp_sem (@generic_stmt_sem S T exp_sem stmt_sem)
.
Proof with auto with rac_hint.
    intros exp_sem stmt_sem ext_stmt_weak f ev₀ ev₀' s ev₁ ext_exp_deter ext_exp_weak  [Hderiv1 Hrel].
    pose proof (weakening_of_expression_semantics exp_sem ext_exp_weak) as exp_weak.
    unfold _weakening_of_expression_semantics in exp_weak.
    unfold _weakening_of_statement_semantics_2 in ext_stmt_weak.
    
    induction Hderiv1 ; intros ev₁' Hderiv2 ; inversion Hderiv2 ; subst ; try easy...
    
    (* assign *)
    - split... simpl. intros v [Hnotin Hnotcompvar].  assert (HH: type_of_value (ev x) <> None) by congruence. apply type_of_value_env in HH.
        apply not_in_diff with (x:=v)  in HH... autounfold with rac_hint. eapply p_map_not_same_eq...  intro neq...

    (* if false *)
    - apply IHHderiv1... destruct H. specialize (exp_weak e ev z). rewrite exp_weak in H. specialize (H ev₀' Hrel). 
            apply determinist_exp_eval in H. apply H in H5. now subst. assumption.

    (* if true *)
    -  destruct H5. specialize (exp_weak e ev (VInt zero)). rewrite exp_weak in H. specialize (H ev₀' Hrel).
            apply determinist_exp_eval in H. apply H in H1. now subst. assumption.

    (* seq *)
    - admit.
    
    (* fcall *)
    - rewrite H9 in H0. inversion H0. subst. clear H0 H9 H8 H14. split ; admit.

    (* pcall *)
    - rewrite H6 in H0. injection H0 as H0. subst. edestruct IHHderiv1... admit. admit.
        epose proof (List.Forall2_impl (R1:=generic_exp_sem ev) (generic_exp_sem ev)) as Hforall. admit.

    (* return *)
    -  split ; intros v... intros [Hnotin Hnotcomp]. destruct (string_dec res_f v).
        + subst. discriminate. (* v is the function return value*)
        +  symmetry. apply p_map_not_same...
            
    (* assert *)
    - eapply ext_stmt_weak with (ev₀:=ev) (ev₁:=ev')  in H1...
Admitted.


(* 3 *)

Definition _weakening_of_expression_semantics_3 {T : Set} (exp_sem : @exp_sem_sig T) := 
    forall ev e z ev₀,
    exp_sem ev e z ->
    forall ev₀', (ev₀' ⊑ ev₀)%envmem ->
    (
        (forall v, (dom ev₀ - dom ev₀') v /\ ~ List.In v (exp_vars e))
        /\
        (forall x v, (dom ev₀.(mstate) - dom ev₀'.(mstate)) x ->  ev₀ v = Some (Def (VMpz x)) /\ ~ List.In v (exp_vars e))
    ) ->

    exp_sem  ev₀' e z
.

Fact weakening_of_expression_semantics_3 {S T : Set} : forall exp_sem, 
    _weakening_of_expression_semantics exp_sem
    -> _weakening_of_expression_semantics_3 (@generic_exp_sem T exp_sem)
.
Proof with auto.
    intros exp Hweak ev e v ev1 Hderiv ev2 Hrel [Henv Hmem]. induction Hderiv.
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
    forall f ev₀  s ev₁,
    stmt_sem f ev₀ s ev₁ -> 
    (
        forall ev₀', (ev₀' ⊑ ev₀)%envmem ->
        (
            (forall v, (dom ev₀ - dom ev₀') v /\ ~ List.In v (stmt_vars s))
            /\
            (forall x v, (dom ev₀.(mstate) - dom ev₀'.(mstate)) x -> ev₀ v = Some (Def (VMpz x)) /\ ~ List.In v (stmt_vars s))
        ) ->

        exists ev₁', stmt_sem f ev₀' s ev₁'
    ).

Lemma weakening_of_statement_semantics_3 {S T : Set} : 
    forall exp_sem stmt_sem, 
    _weakening_of_expression_semantics exp_sem
    -> _weakening_of_statement_semantics_3 stmt_sem 
    -> _weakening_of_statement_semantics_3 (@generic_stmt_sem S T exp_sem stmt_sem)
.

Proof with auto with rac_hint.
    intros exp_sem stmt_sem ext_exp_weak ext_stmt_weak f ev₀ s ev₁ Hderiv ev₀' Hrel [Henv Hmem].
    induction Hderiv.
    (* skip *)
    - exists ev₀'. constructor.
    (* assign *)
    - destruct Henv with x. simpl in H4. destruct H4...  
    (* if true *)
    - destruct IHHderiv as [ev'' Hx]...
        + intro v. destruct Henv with v. split... intros Hin. apply H2.
            apply List.in_app_iff. right. apply List.in_app_iff...
        + intros l v Hdom. destruct Hmem with l v... split... intros Hin. apply H2.  
            apply List.in_app_iff. right. apply List.in_app_iff...
        + exists ev''. apply S_IfTrue with z... destruct H as [He Hzero]. split...
            eapply weakening_of_expression_semantics_3 in He... specialize He with ev₀'. apply He.
            * apply Hrel.
            * split ; simpl in Henv,Hmem.
                ** intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                    intros Hine. apply He2. apply List.in_app_iff...
                ** intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                    intro Hin. apply Hm2. apply List.in_app_iff...

    (* if false *)
    - destruct IHHderiv as [ev'' Hx]...
        + intro v. destruct Henv with v. split... intros Hin. apply H2.
            apply List.in_app_iff. right. apply List.in_app_iff...
        + intros l v Hdom. destruct Hmem with l v... split... intros Hin. apply H2.  
            apply List.in_app_iff. right. apply List.in_app_iff...
        + exists ev''. apply S_IfFalse... 
            eapply weakening_of_expression_semantics_3 in H... specialize H with ev₀'. apply H.
            * apply Hrel.
            * split ; simpl in Henv,Hmem.
                ** intros v. specialize Henv with v as [He1 He2]. simpl in He2. split...
                    intros Hine. apply He2. apply List.in_app_iff...
                ** intros x v Hdom. specialize Hmem with x v. apply Hmem in Hdom as [Hm1 Hm2]. simpl in Hm2. split...
                    intro Hin. apply Hm2. apply List.in_app_iff...
    (* while *)
    - destruct IHHderiv as [ev'' Hx]...
        + intro v. destruct Henv with v. split... intros Hin. simpl in H1,Hin. apply H1. rewrite List.app_nil_r in Hin.
            apply List.in_app_iff in Hin. destruct Hin.
            * apply List.in_app_iff...
            * apply List.in_app_iff in H2. destruct H2... apply List.in_app_iff...
        + intros l v Hdom. destruct Hmem with l v... split... intros Hin. apply H1. simpl in Hin. rewrite List.app_nil_r in Hin.
            apply List.in_app_iff in Hin. destruct Hin.
            * apply List.in_app_iff...
            * apply List.in_app_iff in H2. destruct H2... apply List.in_app_iff...
        +  exists ev''. constructor... 

    (* seq *)
    - destruct IHHderiv as [ev0 Hx]...
        + intro v. destruct Henv with v. split... intros Hin. simpl in H2,Hin. apply H2. 
            apply List.in_app_iff...
        + intros l v Hdom. destruct Hmem with l v... split... intros Hin. apply H2. simpl in Hin.
            apply List.in_app_iff...
        + eexists.  apply S_Seq with ev0... admit. 

    (* fcall *)
    - eexists. apply S_FCall with b xargs zargs...
        * admit.
        * admit.
        * apply H4.

    (* pcall *)
    - repeat eexists. apply S_PCall with b xargs zargs...
        * admit.
        *  admit.

    (* return *)
    - exists (ev₀' <| env ; vars ::= {{res_f\Def z}} |>). apply S_Return.
        eapply weakening_of_expression_semantics_3 in H... specialize H with ev₀'. apply H... apply Hrel.
        
    (* assert *)
    - exists ev₀'. apply S_PAssert with z... 
        eapply weakening_of_expression_semantics_3 in H... specialize H with ev₀'. apply H... apply Hrel.
        

    (* other cases *)
    - unfold _weakening_of_statement_semantics_3 in ext_stmt_weak.
        specialize (ext_stmt_weak f  ev (S_Ext s) _ H ev₀' Hrel).
        destruct ext_stmt_weak as [ev'' Hd]... exists ev''...
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

Open Scope macro_sem_scope.

Corollary same_eval_macro :  forall (ev : Env) v l e z z', 
    _no_env_mpz_aliasing ev ->
    ~ List.In v (exp_vars e) ->
    ev v = Some (Def (VMpz (Some l))) ->
    ev |= e ⇝ z ->
    ev <| mstate ::= {{l \ Defined z'}} |> |= e ⇝ z.

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
    forall f e z (ev : Env) v (y:location),
    ev |= e ⇝ z ->
    ev v = Some (Def (VMpz y)) ->
    gmp_stmt_sem f ev (mpz_ASSGN v e) (ev <| mstate ::= {{y\Defined z}} |>)
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
    forall f e z (ir: Int.inRange z) (ev:Env) v,
    is_comp_var v = false ->
    ev |= e ⇝ z ->
    type_of_value (ev v) = Some C_Int ->
    gmp_stmt_sem f ev (int_ASSGN v e) (ev <| env ; vars ::= {{v\VInt (z ⁱⁿᵗ ir) : 𝕍}} |>)
.
Proof with eauto with rac_hint.
    intros f e z ir ev v Hnotcomp H H0. 
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
    forall f z (ir: Int.inRange z) (ev:Env) v,
    is_comp_var v = false ->
    type_of_value (ev v) = Some C_Int ->
    gmp_stmt_sem f ev (Z_ASSGN C_Int v z) (ev <| env ; vars ::= {{v\VInt (z ⁱⁿᵗ ir) : 𝕍}} |>)
.
Proof.
    intros.  constructor ; auto with rac_hint.
Qed.

Lemma semantics_of_the_Z_assgn_macro_tmpz :
    forall f y (z:ℤ) (ev:Env) v,
    ev v = Some (Def (VMpz (Some y))) ->
    gmp_stmt_sem f ev (Z_ASSGN Mpz v z) (ev <| mstate ::= {{y\Defined z}} |>)
.
Proof with auto using BinaryString.Z_of_of_Z.
    intros. simpl. constructor. apply S_set_s...
Qed.


Lemma semantics_of_the_cmp_macro :
    forall f (ev:Env) c e1 e2 v1 v2 z1 z2 a,
    _no_env_mpz_aliasing ev ->
    is_comp_var c = false ->
    type_of_value (ev c) = Some C_Int ->
    ev |= e1 ⇝ z1 ->
    ev |= e2 ⇝ z2 ->

    (
        (Def a = VInt sub_one <-> Z.lt z1 z2 ) /\
        (Def a = VInt zero <-> z1 = z2) /\
        (Def a = VInt one <-> Z.gt z1 z2)
    ) -> 

    (* v1 and v2 must be bound to a mpz location (implied by mpz_assign ) *)
    forall (l1 l2 : location),
    ev v1 = Some (Def (VMpz l1)) /\  ev v2 = Some (Def (VMpz l2))->
    
    ~ List.In v1 ((exp_vars e2)) /\  l1 <> l2   -> (* not in paper proof *)

    exists M, (
        forall v (n:location), 
        ev v = Some (Def (VMpz n)) ->
        ev v <> ev v1 /\ ev v <> ev v2  -> 
        ev.(mstate) n = M n
    ) -> 
    
    gmp_stmt_sem f ev (CMP c e1 e2 v1 v2) (ev <| env ; vars ::= {{c\Def a}} |> <| mstate := M |>) 
.

Proof with try easy ; auto with rac_hint ; unshelve eauto using Z.ltb_irrefl,Z.gtb_ltb,Z.ltb_lt with rac_hint; auto with rac_hint.
    intros f ev c e1 e2 v1 v2 z1 z2 a Hnoalias Hnocom H H0 H1 (inf & eq & sup) l1 l2 (Hv1 & Hv2) (Hv1NotIne2 & Hdiffl1l2).
    
    assert (NotInt : 
        exists M, (
            forall v (n:location), 
            ev v = Some (Def (VMpz n)) ->
            ev v <> ev v1 /\ ev v <> ev v2  -> 
            ev.(mstate) n = M n
        ) -> 
        let cmp := S_Ext <(c = cmp (v1, v2) )> in
        gmp_stmt_sem f ev <{(mpz_ASSGN v1 e1); (mpz_ASSGN v2 e2); cmp}> 
        (ev <| env ; vars ::= {{c \Def a}} |> <| mstate := M |>)
    ). {
        exists ev.(mstate){l2 \Defined z2, l1 \Defined  z1}. intros Hvdiff. 
        apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |>).
        - apply semantics_of_the_mpz_assgn_macro...
        - eapply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |> <| mstate ::= {{l2\Defined z2}} |> ).
            + apply semantics_of_the_mpz_assgn_macro... inversion H1 ; subst. 
                * constructor. eapply untouched_var_same_eval_exp_gmp...
                * inversion H2. subst.   assert (Hdiffxv1: x <> v1). 
                    { simpl in Hv1NotIne2. now apply Decidable.not_or_iff in Hv1NotIne2 as [Hv1NotIne2 _]. }
                    econstructor. eapply untouched_var_same_eval_exp_gmp... 
                    assert (Hdiffll1: l <> l1)... apply p_map_not_same_eq... 

            + constructor. replace 
                (_ <| env; vars ::= _ |><| mstate := _ |>)
                with (ev <| mstate := ev.(mstate) {l2 \Defined z2, l1 \Defined z1} |><| env; vars ::= {{c \Def a}} |> ) by reflexivity.
                apply S_cmp with (vx:=l1) (vy:=l2) (lx:=z1) (ly:=z2) ; simpl...
                * constructor... constructor 1 with z1...  apply p_map_not_same_eq...
                * constructor... constructor 1 with z2...  apply p_map_same...
                * apply p_map_not_same_eq...
    }
    unfold CMP. destruct (ty e1) eqn:T1, (ty e2) eqn:T2 ; try apply NotInt ; clear NotInt.
    
    (* both ty(e1) = int and ty(e2) = int *)
    inversion H0 ; inversion H1 ; try 
    match goal with 
    | Contra :  (_ |= _ => Def (VMpz _))%gmpesem |- _ => 
        inversion Contra ; match goal with 
        | Contra : _gmp_exp_sem _ _ _ |- _ => inversion Contra ; now subst
        end
    end.

    exists ev.(mstate). intros Hvdiff. clear Hvdiff (* not needed *). destruct (Z.lt_trichotomy z1 z2) as [inf' | [ eq' | sup']].
        
    (* z1 < z2 *)
    * assert (cmp := inf'). apply <- inf in inf'. clear eq inf sup. subst.
        destruct x,x0. subst. apply S_IfTrue with (VInt one).
        + split... apply C_E_BinOpTrue with x x0 i i0... apply Z.ltb_lt. apply cmp.
        + inversion inf'. constructor...  apply (C_E_BinOpInt ev 0 1 0 1) with zeroinRange oneinRange...

    (* z1 = z2 *)
    * assert (cmp := eq'). rewrite <- eq in eq'. clear eq inf sup. subst.
        destruct x,x0. apply Int.mi_eq in cmp. injection cmp as cmp. inversion eq'. subst. repeat constructor... 

    (* z1 > z2 *)
    * assert (cmp := sup').  apply Z.lt_gt in sup'. apply <- sup in sup'.  clear inf eq sup. subst.
        destruct x, x0. subst. constructor ; simpl in *.
        + eapply C_E_BinOpFalse... apply Z.ltb_ge. unfold Z.le. now rewrite cmp.  
        + inversion sup'. subst. apply S_IfTrue with (VInt one).
            ++  subst. split... apply C_E_BinOpTrue with x x0 i i0... now apply Z.gtb_lt.
            ++  constructor...
Qed.




Lemma semantics_of_the_binop_macro_int :
    forall f (ev:Env) (op:fsl_binop_int) c r e1 e2 v1 v2 z1 z2 (ir: Int.inRange (⋄ op z1 z2) ) l1 l2 lr,
    _no_env_mpz_aliasing ev ->
    is_comp_var c = false ->
    type_of_value (ev c) = Some C_Int ->
    ev |= e1 ⇝ z1 ->
    ev |= e2 ⇝ z2 ->
    let zr := ⋄ op z1 z2 in

    ev v1 = Some (Def (VMpz (Some l1))) /\  
    ev v2 = Some (Def (VMpz (Some l2))) /\
    ev r = Some (Def (VMpz (Some lr))) ->
    exists M, (forall v n, ev v = Some (Def (VMpz (Some n))) ->
    ev v1 <> ev v /\ ev v2 <> ev v  -> ev.(mstate) n = M n) -> 

    ~ List.In v1 ((exp_vars e2)) /\  l1 <> l2   -> (* not in paper proof *)

    gmp_stmt_sem f ev (binop_ASSGN op (c,C_Int) e1 e2 r v1 v2) (ev <| env ; vars ::= fun e => e{c\VInt (zr ⁱⁿᵗ ir) : 𝕍} |> <| mstate := M |>)
    .

Proof with eauto with rac_hint.
    intros f ev op c r e1 e2 v1 v2 z1 z2 ir l1 l2 lr Hnoalias Hnocomp H H0 H1 zr H2. destruct H2 as (v1l & v2l & rl).  
    assert (NotInt : 
        exists M,
        (forall (v : 𝓥) (n : location),
        ev v = Some (Def (VMpz n)) ->
        ev v1 <> ev v /\ ev v2 <> ev v ->
        ev.(mstate) n = M n) ->
        ~ List.In v1 ((exp_vars e2)) /\  l1 <> l2   -> (* not in paper proof *)
        gmp_stmt_sem f ev <{
            (mpz_ASSGN v1 e1);
            (mpz_ASSGN v2 e2);
            (S_Ext (Definitions.op op r v1 v2));
            (int_ASSGN c (C_Id r Mpz))
        }> (ev <| env ; vars ::= fun e => e{c \VInt (zr ⁱⁿᵗ ir) : 𝕍} |> <| mstate := M |> )
    ). {
    exists ev.(mstate){lr\Defined zr,l2\Defined z2,l1\Defined z1}. intros H2 [H3 H4].  apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |>). 
    - apply semantics_of_the_mpz_assgn_macro...
    - apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |> <| mstate ::= {{l2\Defined z2}} |> ). 
        + apply semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
        + apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |> <| mstate ::= {{l2\Defined z2}}  |> <| mstate ::= {{lr\Defined zr}} |>).
            * constructor. apply S_op with l1 l2...
                ** constructor... easy. apply GMP_E_Var with z1... destruct (eq_dec l1 l2).
                    *** subst. edestruct Hnoalias...
                    *** apply p_map_not_same_eq... autounfold with rac_hint. simpl...
                ** destruct (eq_dec l1 l2).
                    *** subst. edestruct Hnoalias...
                    *** apply p_map_not_same_eq...  autounfold with rac_hint. simpl...
                ** constructor... easy. constructor 1 with z2. simpl... autounfold with rac_hint. simpl...
                ** simpl...
            * replace (ev <| env; vars ::= _ |> <| mstate :=  _ |>)
            with (ev <| mstate := ev.(mstate) {lr \Defined zr, l2 \Defined z2, l1 \ Defined z1} |> 
                    <| env; vars ::= {{c \Def (VInt ((zr ⁱⁿᵗ) ir))}} |>
            ) by reflexivity.
            apply semantics_of_the_int_assgn_macro...  apply M_Mpz with lr ; simpl...
                constructor... easy. constructor 1 with zr ; simpl...
    }
    
    unfold binop_ASSGN. destruct (ty e1) eqn:T1, (ty e2) eqn:T2 ; try apply NotInt. clear NotInt.
    exists ev.(mstate). intros. inversion H0 ; inversion H1; try 
    match goal with 
    | Contra :  ( _ |= _ => Def (VMpz _))%gmpesem |- _ => 
        inversion Contra ; match goal with 
        | Contra : _gmp_exp_sem _ _ _ |- _ => inversion Contra ; now subst
        end
    end.
    - subst. constructor... destruct x,x0. econstructor...
Qed.



Lemma semantics_of_the_binop_macro_mpz :
    forall f (ev:Env) (op:fsl_binop_int) c y r e1 e2 v1 v2 z1 z2 l1 l2,
    _no_env_mpz_aliasing ev ->
    type_of_value (ev c) = Some C_Int ->
    ev |= e1 ⇝ z1 ->
    ev |= e2 ⇝ z2 ->

    let zr := ⋄ op z1 z2 in
    ev v1 = Some (Def (VMpz (Some l1))) /\  ev v2 = Some (Def (VMpz (Some l2))) /\  ev c = Some (Def (VMpz (Some y))) ->
    ~ List.In v1 (exp_vars e2) -> (* not in paper proof *)
    exists M, (forall v n, ev v = Some (Def (VMpz (Some n))) ->
    ev v1 <> ev v /\ ev v2 <> ev v -> ev.(mstate) n = M n) -> 
    l1 <> l2 -> (* not in paper proof *)
    gmp_stmt_sem f ev (binop_ASSGN op (c,T_Ext Mpz) e1 e2 r v1 v2) (ev <| mstate := M{y\Defined zr} |>)
    .
Proof with eauto using p_map_same with rac_hint.
    intros f ev op c y r e1 e2 v1 v2 z1 z2 l1 l2 Hnoalias H H0 H1 zr H2 H3. 
    exists ev.(mstate){l2\Defined z2,l1\Defined z1}. intros. destruct H2 as (v1l & v2l & rl). unfold binop_ASSGN.
    apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |>).
    - apply semantics_of_the_mpz_assgn_macro...
    - apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |> <| mstate ::= {{l2\Defined z2}} |>). 
        * apply semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
        * constructor.  
            replace  (ev <| mstate := ev.(mstate) {y \Defined zr, l2 \Defined z2, l1 \Defined z1} |>)
            with (ev <| mstate ::= {{l1 \Defined z1}} |> 
                    <| mstate ::= {{l2 \Defined z2}} |>
                    <| mstate ::= {{y \Defined zr}} |> 
            ) by reflexivity.
        apply S_op with l1 l2 ; simpl...
            + constructor... easy. apply GMP_E_Var with z1... simpl. apply p_map_not_same_eq...
            + simpl. apply p_map_not_same_eq...
            + constructor... easy. constructor 1 with z2... simpl...
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
