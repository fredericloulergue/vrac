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

Fact eq_mem_partial_order :  
    forall mem mem' z l, mems_partial_order mem mem' l -> z <> None ->  
    mem l = z ->  mem' l = z.
Proof.
    intros. destruct H as [some_z Hl | Hmem]. 
    - subst.  now rewrite H,Hl.
    - rewrite H1 in Hmem. now destruct H0.
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


Open Scope c_sem_scope.
Lemma weakening_of_expression_semantics : 
forall env (e : _c_exp) (x:𝕍),
    env |= e => x <-> (forall env', env ⊑ env' ->  env'  |= e => x)
.
Proof with (eauto using refl_env_partial_order with rac_hint; try easy). intros env e x.
    split... intro H. intros env' H0.  generalize dependent x.  induction e ; intros x H; 
    match goal with 
        Sem :c_exp_sem  _ _ _ _ |- _ =>  inversion Sem 
    end...
    (* machine integer *)
    - econstructor.
    (* variable of type machine integer *)
    - econstructor. eapply eq_env_partial_order in H4...


    (* binop *)
    - econstructor... subst.  apply IHe1... apply IHe2...
    - econstructor... apply IHe1... apply IHe2...
    - econstructor... apply IHe1... apply IHe2...
Qed.
Close Scope c_sem_scope.


Open Scope generic_sem_scope.
Lemma weakening_of_c_expression_semantics : 
forall e env mem (x:𝕍),
    @generic_exp_sem Empty_set Empty_exp_sem env mem e x <-> 
    (forall env' mem',  (env,mem) ⊑ (env',mem') -> @generic_exp_sem Empty_set Empty_exp_sem env' mem' e x)
.
Proof with (eauto using refl_env_partial_order, refl_mem_partial_order with rac_hint; try easy).
    split... 
    - generalize dependent x. induction e ; intros ;  
        match goal with 
            Sem : _ ⋅ _ |= _ => _ |- _ =>  inversion Sem 
        end ; subst ...
        (* variable of type machine integer *)
        + constructor. eapply eq_env_partial_order in H4...
Qed.
Close Scope generic_sem_scope.

Open Scope gmp_sem_scope.
Lemma weakening_of_gmp_expression_semantics : 
forall env mem (e : _c_exp) (x:𝕍),
    env ⋅ mem |= e => x <-> (forall env' mem', (env,mem) ⊑ (env',mem') ->  env' ⋅ mem' |= e => x)
.
Proof with (eauto using refl_env_partial_order, refl_mem_partial_order with rac_hint; try easy).
    split... 
    - generalize dependent x. induction e ; intros ;  
        match goal with 
            Sem : _ ⋅ _ |= _ => _ |- _ =>  inversion Sem 
        end ; subst ...
        (* machine integer *)
        + econstructor.
        (* variable of type machine integer *)
        + constructor. eapply eq_env_partial_order in H4...

        (* variable of type mpz *)
        + destruct ty... destruct t... constructor. inversion H1; subst.  apply GMP_E_Var with z; destruct H0 as [relEnv memEnv].
            ++  eapply eq_env_partial_order in relEnv...
            ++ eapply eq_mem_partial_order in memEnv...
            
        (* binop *)
        + econstructor. apply IHe1... apply IHe2...
        + econstructor... apply IHe1... apply IHe2...
        + econstructor... apply IHe1... apply IHe2...
Qed.
Close Scope gmp_sem_scope.


Open Scope c_sem_scope.

Lemma weakening_of_statement_semantics_1 :
    forall Ω₀ M₀ s Ω₁ M₁,
    Ω₀ ⋅ M₀ |= s => Ω₁ ⋅ M₁ <->
    ( forall Ω₀' M₀', (Ω₀ , M₀) ⊑ (Ω₀', M₀') ->
    exists Ω₁' M₁', (Ω₁ , M₁) ⊑ (Ω₁', M₁') ->
    Ω₀' ⋅ M₀' |= s => Ω₁'⋅ M₁').
Proof with auto using weakening_of_c_expression_semantics with rac_hint.
    intros Ω₀ M₀ s Ω₁ M₁. split. 
    - intros Hderiv. induction Hderiv ; intros Ω₀' M₀' Hrel.
        (* skip *)
        * exists Ω₀',M₀'. constructor. 
        
        (* assign *) 
        * exists ((fst Ω₀') {x \ z}, (snd Ω₀')) , M₀'. intros _. apply S_Assign.
            *** now apply env_same_ty with env. 
            *** rewrite weakening_of_c_expression_semantics in H0. specialize (H0 Ω₀' M₀'). apply H0...


        (* if true *)
        * destruct H. destruct (IHHderiv Ω₀' M₀') as [env_s [mem_s Hs]]... exists env_s, mem_s. intros . apply S_IfTrue with z. split...
            rewrite weakening_of_c_expression_semantics in H... apply Hs...
        (* if false *)
        * destruct (IHHderiv Ω₀' M₀') as [env_s [mem_s Hs]]... exists env_s, mem_s. intro rel. apply S_IfFalse.
            rewrite weakening_of_c_expression_semantics in H... apply Hs... 


         (* while *)
        * destruct (IHHderiv Ω₀' M₀') as [env_s [mem_s Hs]]... exists env_s, mem_s.
            intros. apply S_While. apply Hs...


        (* c seq *)
        *   destruct IHHderiv1 with Ω₀' M₀' as [I1env [I1mem I1H]]...
            destruct IHHderiv2 with I1env I1mem as [I2env [I2mem I2H]]. admit. 
            exists I2env,I2mem. intro H.  
            apply S_Seq with I1env I1mem.
            ** apply I1H. admit.
            ** apply I2H...

        (* f call *)
        * admit.


        (* p call *)
        * admit.

        (* return *)
        * exists ((fst Ω₀') {resf \ z}, snd Ω₀'), M₀'. intro rel.  apply S_Return...
            apply (weakening_of_c_expression_semantics e env mem z)...

        (* assert *)
        * exists Ω₀', M₀'. intro rel.  apply S_PAssert with z...
            apply (weakening_of_c_expression_semantics e env mem z)...

        (* no other case as there is no additional semantic *)
        * contradiction.
    
    - admit.
Admitted.




(* 2 *)

Lemma weakening_of_statement_semantics_2 :
    forall Ω₀ Ω₀' M₀ M₀' s Ω₁ M₁,
    Ω₀ ⋅ M₀|= s => Ω₁ ⋅ M₁ /\ (Ω₀, M₀) ⊑ (Ω₀', M₀')  ->
    (
        forall Ω₁' M₁',
        Ω₀' ⋅ M₀' |= s => Ω₁' ⋅ M₁' ->
        (forall (v:𝓥),v ∉ fst Ω₀ -> fst Ω₀' v = fst Ω₁' v) 
        /\
        (forall (x:location) (v:𝓥), (fst Ω₀ v) <> Some (VMpz x) -> M₀' x = M₁' x)
    ).
Proof with auto with rac_hint ; try contradiction.
    intros Ω₀ Ω₀' M₀ M₀' s Ω₁ M₁ [Hderiv1 Hrel] Ω₁' M₁' Hderiv2. induction s; split ; intros ; inversion Hderiv2 ; subst...
    (* assign env *)
    - admit.
    (* fcall env *)
    - admit.
    (* fcall mem *)
    - admit.
    (* pcall mem *)
    - admit.
    (* seq env *)
    -admit.
    (* seq mem *)
    - admit.
    (* if true env *)
    - admit.
    (* if false env *)
    - admit.
    (* if true mem *)
    - admit.
    (* if false mem *)
    - admit.
    (* while env *)
    - admit.
    (* while mem *)
    - admit.
    (* return env *)
    - admit. 
Admitted.


Lemma weakening_of_statement_semantics_3 :
    forall Ω₀ M₀  s Ω₁ M₁,
    Ω₀ ⋅ M₀|= s => Ω₁ ⋅ M₁ -> 
    (
        forall Ω₀' M₀', (Ω₀', M₀') ⊑ (Ω₀, M₀) ->
        (
            (forall v, (dom (fst Ω₀) - dom (fst Ω₀')) v /\ ~ List.In v (stmt_vars s))
            /\
            (forall x v, (dom M₀ - dom M₀') x -> (fst Ω₀) v = Some (VMpz x) /\ ~ List.In v (stmt_vars s))
        ) ->

        exists Ω₁' M₁', Ω₀' ⋅ M₀' |= s => Ω₁' ⋅ M₁'
    ).
Proof with auto with rac_hint.
    intros Ω₀ M₀ s Ω₁ M₁ Hderiv Ω₀' M₀' Hrel [Henv Hmem].  induction Hderiv.
    (* skip *)
    - exists Ω₀', M₀'. constructor.
    (* assign *)
    - destruct Henv with x. destruct H1. admit.
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
    (* no other case as there is no additional semantic *)
    - contradiction.
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
    - inversion H0... constructor.
    - destruct ty ; inversion H0...
        * constructor. simpl. subst. unfold p_map. simpl. apply Decidable.not_or_iff in H. destruct H as [H _]. 
            destruct (string_dec x var)... now destruct H. 
        * destruct t... inversion H1. subst. constructor. apply GMP_E_Var with z0... simpl.
            unfold p_map. simpl in *. apply Decidable.not_or_iff in H. destruct H as [H3 _].
            destruct string_dec... subst. easy.

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
            unfold p_map. simpl in *. apply Decidable.not_or_iff in H. destruct H as [H _].
            destruct Nat.eq_dec... subst. admit.

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
        + subst. rewrite <- H3. apply p_map_not_same.
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
        * now apply S_set_i.
        * inversion H1. inversion H4. now subst. 
    - unfold ty in TY. destruct e; try easy. subst. inversion H; now inversion H1.
    - destruct t.
        * destruct H; destruct H ; try easy ; now destruct H.
        * destruct e; try easy. inversion H.
            ** inversion H1 ; inversion H3. now subst.
            ** inversion H1. inversion H4. constructor. now apply S_set_z with l.
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
        * constructor... subst. rewrite (x_of_z_to_z_is_x x ir). now constructor.
        * inversion H1. inversion H4. now subst.
    - inversion H ; inversion H1;  inversion H3 ; inversion H4; now subst.
    - destruct t.
        * destruct H; destruct H ; try easy ; now destruct H.
        * destruct e; try easy. inversion H.
            ** inversion H1.  inversion H3. now subst. easy.
            ** inversion H1 ; inversion H4. subst. constructor. now apply S_get_int with l.
Qed.

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
    intros. simpl. constructor. apply S_set_s...
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
                * subst. econstructor. apply same_eval_mem with v1... rewrite <- H5. apply p_map_not_same. admit.
            + constructor. apply S_cmp with (vx:=l1) (vy:=l2) (lx:=z1) (ly:=z2)...
                * constructor. apply GMP_E_Var with z1. assumption. unfold p_map. simpl. 
                    destruct (Nat.eq_dec l2 l1) as [Neq | Nneq]. 
                        ** now destruct Hl1Notl2.
                        ** now destruct (Nat.eq_dec l1 l1).
                * constructor. apply GMP_E_Var with z2. assumption. unfold p_map. simpl.
                    now destruct (Nat.eq_dec l2 l2) as [Neq | Nneq].
                *  unfold p_map. simpl. destruct (Nat.eq_dec l2 l1) as [Neq | Nneq].
                    ** now destruct Hl1Notl2.
                    ** now destruct (Nat.eq_dec l1 l1).
                * unfold p_map. simpl. destruct (Nat.eq_dec l2 l1) as [Neq | Nneq] ;  now destruct (Nat.eq_dec l2 l2).
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
            + split... eapply C_E_BinOpTrue... apply Z.ltb_lt. apply cmp.
            + constructor... constructor... unshelve eapply (C_E_BinOpInt Ω M 0 1 0 1)...

        (* z1 = z2 *)
        * assert (cmp := eq'). rewrite <- eq in eq'. clear eq inf sup. rewrite <- H5, <-H7 in cmp.
            destruct x,x0. apply Int.mi_eq in cmp. injection cmp as cmp. inversion cmp.  constructor ; subst... constructor... 

        (* z1 > z2 *)
        * assert (cmp := sup').  apply Z.lt_gt in sup'. apply <- sup in sup'.  clear inf eq sup. rewrite <- H5, <- H7 in cmp.
          destruct x, x0. subst. constructor ; simpl in *.
            + constructor. eapply C_E_BinOpFalse... apply Z.ltb_ge. unfold Z.le. now rewrite cmp.  
            + apply S_IfTrue with one.
                ++  subst. split... constructor. eapply C_E_BinOpTrue... simpl.  now apply Z.gtb_lt.
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
        * constructor. pose proof (p_map_not_same M{l1 \ z1}) l1 l2 z2 H4. apply S_op with l1 l2...
            ** constructor. apply GMP_E_Var with z1...  rewrite H5.  unfold p_map. simpl. now destruct Nat.eq_dec.
            ** unfold p_map. simpl. destruct Nat.eq_dec.
                *** now destruct H4. 
                *** now destruct Nat.eq_dec.
            ** constructor. apply GMP_E_Var with z2... unfold p_map. simpl. now destruct Nat.eq_dec...
            ** unfold p_map. simpl. now destruct Nat.eq_dec.
        * apply semantics_of_the_int_assgn_macro...  apply M_Mpz with lr ; try (constructor ; apply GMP_E_Var with zr ; try easy) ;
        unfold p_map ; simpl ; now destruct Nat.eq_dec.
    }
    
    unfold binop_ASSGN. destruct (ty e1) eqn:T1, (ty e2) eqn:T2 ; try apply NotInt. clear NotInt.
    exists M. intros. inversion H0 ; inversion H1; try 
    match goal with 
    | Contra :  _ ⋅ _ |= _ => VMpz _ |- _ => 
        inversion Contra ; match goal with 
        | Contra : _gmp_exp_sem _ _ _ _ |- _ => inversion Contra ; now subst
        end
    end.
    - destruct x,x0. constructor... constructor. subst. eapply C_E_BinOpInt...
Qed.



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
Proof with eauto with rac_hint.
    intros. exists M{l2\z2,l1\z1}. intros. destruct H2 as (v1l & v2l & rl). unfold binop_ASSGN.
    apply S_Seq with Ω M{l1\z1}.
    - apply semantics_of_the_mpz_assgn_macro...
    - apply S_Seq with Ω M{l2\z2,l1\z1}. 
        * apply semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
        * constructor. pose proof (p_map_not_same M{l1 \ z1}) l1 l2 z2 H5.  apply S_op with l1 l2...
            + constructor. apply GMP_E_Var with z1...  rewrite H2. 
             unfold p_map. simpl. now destruct Nat.eq_dec.
            + rewrite H2.  unfold p_map. simpl. now destruct Nat.eq_dec.
            + constructor. apply GMP_E_Var with z2... unfold p_map. simpl. now destruct Nat.eq_dec.
            + unfold p_map. simpl. now destruct Nat.eq_dec...
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
