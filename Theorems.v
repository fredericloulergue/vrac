Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import RAC.Semantics.
Require Import RAC.Translation.
Require Import  Strings.String.
From Coq Require Import ZArith.ZArith.


(* Properties of the semantics *)

Fact eq_env_partial_order :  forall e e' v z, e ⊑ e' ->  z <> UInt /\ z <> UMpz -> (fst e) v = Some z -> (fst e') v = Some z.
Proof.
    intros. destruct H with v ; try assumption ; try rewrite H2 in H1 ; try injection H1 as Eq ; subst ; now try assumption.
Qed.


Fact env_same_ty : forall  (Ω Ω' : Ω) v t, Ω ⊑ Ω' -> t <> None -> type_of_value (fst Ω v) = t -> type_of_value (fst Ω' v) = t.
Proof.
    intros. destruct H with v ; subst ;  try now rewrite H2,H3.
    - destruct H3. 
        * now rewrite H1,H2.
        * destruct H1. now rewrite H1,H2.
    -destruct H3. 
        * now rewrite H1,H2.
        * destruct H1. now rewrite H1,H2.
    - destruct H0. now rewrite H2.
Qed.

Lemma weakening_of_expression_semantics : 
forall T env (e : @c_exp T) (x:𝕍),
    env |= e => x <-> (forall env', env ⊑ env' ->  env' |= e => x)
.
Proof with (eauto using refl_env_partial_order with rac_hint ; try easy).
    split... generalize dependent x. induction e.
    * intros v H. inversion H...
    * intros v H env' Inc. inversion H.
        eapply eq_env_partial_order in Inc...
    * intros v H. inversion H...
    * intros. inversion H...
Qed.

Open Scope mini_gmp_stmt_scope.
Open Scope mini_gmp_exp_scope.


Lemma weakening_of_statement_semantics_1 :
    forall Ω₀ M₀ s Ω₁ M₁,
    Ω₀ ⋅ M₀ |= s => Ω₁ ⋅ M₁ <->
   ( forall Ω₀' M₀', (Ω₀ , M₀) ⊑ (Ω₀', M₀') ->
     exists Ω₁' M₁', (Ω₁ , M₁) ⊑ (Ω₁', M₁') ->
     Ω₀' ⋅ M₀' |= s => Ω₁'⋅ M₁').
Proof with auto with rac_hint.
     split. 
    - induction s ; intros ; inversion H0 ; inversion H ; inversion H3.
        (* skip *)
        * exists Ω₀',M₀'... 

        (* assign *)
        * pose ((fst Ω₀'){x\z}, snd Ω₀'). exists p ,M₀'.
         intros. pose (weakening_of_expression_semantics _gmp_t Ω₀ e z). specialize i. rewrite i in H12. specialize H12 with Ω₀'. clear i.
         subst. constructor. apply S_Assign... now apply env_same_ty with Ω₀.

         (* pcall *)
        * subst. exists ((fst Ω₀') {var \ z}, snd Ω₀'), M₁.  
            intros. constructor. eapply S_FCall ; try eassumption.
            + intros. admit.
            + admit.

        (* fcall *)         
        *  eexists. eexists. intro. constructor. eapply S_PCall ; try eassumption.
            + admit.
            + admit.

        (* c seq *)
        * exists Ω₁, M₁. intro. constructor. apply S_Seq with  env' mem'...  admit. admit.

        (* gmp seq *)
        * exists Ω₁, M₁. intro. apply GMP_Seq with  env' mem'...  admit. admit.

        (* if true *)
        * exists Ω₁, M₁. intro. constructor. apply S_IfTrue with z.
            + admit.
            + admit. 

        (* if false *)
        * exists Ω₁, M₁. intro. constructor. apply S_IfFalse.
            +  pose (weakening_of_expression_semantics _gmp_t Ω₀ cond zero). specialize i. rewrite i in H12. specialize H12 with Ω₀'. clear i.
                rewrite <- H7 in *. clear H3 H4. apply (H12 H1).
            + admit.
        
        (* while *)
        * exists Ω₁, M₁. intro. constructor. apply S_While. admit.

        (* assert *)
        * exists Ω₀', M₀'. intro. constructor. apply S_PAssert with z... apply weakening_of_expression_semantics  with Ω₁... inversion H12...

        (* return *)
        * exists ((fst Ω₀') {resf \ z}, snd Ω₀'), M₀'. intro. subst. constructor. apply S_Return. admit.

        (* set_i *)
        * admit.

        (* set_z *)
        * admit.
        
        (* get_int *)
        * admit.

        (* set_s *)
        * admit.

        (* cmp *)
        * admit.

        (* op *)
        * admit. 
    
    - intros. induction s.
     * destruct H with Ω₀ M₀. 
        +  constructor.
            ++ apply refl_env_partial_order.
            ++ apply refl_mem_partial_order.
        + destruct H0. admit.

    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
Admitted.


(* 2 *)

Lemma weakening_of_statement_semantics_2 :
    forall Ω₀ Ω₀' M₀ M₀' s Ω₁ M₁,
    Ω₀ ⋅ M₀|= s => Ω₁ ⋅ M₁ /\ Ω₀ ⋅ M₀ |= s => Ω₀' ⋅ M₀'  ->
    forall Ω₁' M₁',
    Ω₀' ⋅ M₀' |= s => Ω₁' ⋅ M₁' -> 
    (forall (v:𝓥), ~(dom (fst Ω₀) v) -> fst Ω₀' v = fst Ω₁' v) /\ True.
    (* (forall x, ~ exists (v:𝓥), (fst Ω₀ v) = Some x -> M₀' x = M₁' x). *)
Admitted.


(* Lemma weakening_of_statement_semantics_3 :
    forall Ω₀ Ω₀' M₀ M₀' s Ω₁ M₁,
    Ω₀ ⋅ M₀|= s => Ω₁ ⋅ M₁ ->
    Ω₀' ⋅ M₀'|= s => Ω₀ ⋅ M₀ ->
    forall v, (dom (fst Ω₀) - dom (fst Ω₀')) v -> 
    ~ var_in_stmt s v -> 
    forall x, (dom M₀ - dom M₀') x -> (fst Ω₀) v = Some (VMpz x) ->
    exists Ω₁' M₁', Ω₀' ⋅ M₀' |= s => Ω₁' ⋅ M₁'.

Admitted.
 *)



(* Proofs of structural properties of the translation *)

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


Lemma semantics_of_the_mpz_assgn_macro :
    forall e z Ω M v (y:location),
    Ω ⋅ M |= e ⇝ z ->
    (fst Ω) v = Some (VMpz y) ->
    Ω ⋅ M |= (mpz_ASSGN v e) => Ω ⋅ M{y\z}
.
Proof.
    intros. 
    unfold mpz_ASSGN. destruct (ty e) eqn:TY.
    - inversion H.
        * now apply S_set_i.
        * inversion H1 ; now subst.
    - unfold ty in TY. destruct e; try easy. subst. inversion H; now inversion H1.
    - destruct t.
        * destruct H; destruct H ; try easy ; now destruct H.
        * destruct e; try easy. inversion H.
            ** inversion H1. inversion H3. now subst.
            ** inversion H1 ; try easy. subst. now apply S_set_z with l.
Qed.

Lemma semantics_of_the_int_assgn_macro :
    forall e z (ir: Int.inRange z) Ω M v,
    Ω ⋅ M |= e ⇝ z ->
    type_of_value ((fst Ω) v) = Some C_Int ->
    Ω ⋅ M |= (int_ASSGN v e) => ((fst Ω){v\z ⁱⁿᵗ ir}, snd Ω) ⋅ M
.
Proof with eauto with rac_hint.
    intros. 
    unfold int_ASSGN. destruct (ty e) eqn:TY.
    - inversion H.
        * constructor. constructor... subst. inversion H1. subst. 
            replace ((x) ̇ ⁱⁿᵗ ir) with (VInt x). assumption. admit. (* proof of x ̇ in = x *)
        * inversion H1 ; now subst.
    - inversion H ; inversion H1;  inversion H3 ; now subst.
    - destruct t.
        * destruct H; destruct H ; try easy ; now destruct H.
        * destruct e; try easy. inversion H.
            ** inversion H1.  inversion H3. now subst.
            ** inversion H1 ; try easy. subst. now apply S_get_int with l.
Admitted.

Lemma semantics_of_the_Z_assgn_macro_tint :
    forall z (ir: Int.inRange z) Ω M v,
    type_of_value ((fst Ω) v) = Some C_Int ->
    Ω ⋅ M |= (Z_ASSGN C_Int v z) => ((fst Ω){v\z ⁱⁿᵗ ir}, snd Ω) ⋅ M
.
Proof.
    intros. simpl. auto with rac_hint.
Qed.

Lemma semantics_of_the_Z_assgn_macro_tmpz :
    forall y (z:ℤ) Ω M v,
    (fst Ω) v = Some (VMpz y) ->
    Ω ⋅ M |= (Z_ASSGN Mpz v z) => Ω ⋅ M{y\z}
.
Proof with auto using BinaryString.Z_of_of_Z.
    intros. simpl. apply S_set_s...
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
    exists M', forall v n, (fst Ω) v = Some (VMpz n) ->
    ~ ((fst Ω) v1 = (fst Ω) v) /\ ~ ((fst Ω) v2 = (fst Ω) v)  -> M n = M' n -> 
    Ω ⋅ M |= (CMP c e1 e2 v1 v2) => ((fst Ω){c\a}, snd Ω) ⋅ M'
    .

Proof with try easy ; auto with rac_hint ; unshelve eauto using Z.ltb_irrefl,Z.gtb_ltb,Z.ltb_lt with rac_hint; auto with rac_hint.
    intros. destruct H2 as (inf & eq & sup), H3.

    assert (NotInt : 
        exists M', forall v n, (fst Ω) v = Some (VMpz n) ->
        ~ ((fst Ω) v1 = (fst Ω) v) /\ ~ ((fst Ω) v2 = (fst Ω) v)  -> M n = M' n -> 
        Ω ⋅ M |= <{ 
        (mpz_ASSGN v1 e1); 
        (mpz_ASSGN v2 e2); 
        <c = cmp (v1, v2)>
        }> => ((fst Ω){c\a}, snd Ω) ⋅ M'
    ). {
        exists M{l2 \ z2, l1 \ z1}. intros v n VN [Hvneqv1 Hvneqv2] HM.
        apply GMP_Seq with Ω M{l1\z1}.
        + apply semantics_of_the_mpz_assgn_macro...
        + apply GMP_Seq with Ω M{l2\z2,l1\z1}.  
            ++ apply semantics_of_the_mpz_assgn_macro... admit. 
            ++ apply S_cmp with (vx:=l1) (vy:=l2) (lx:=z1) (ly:=z2)...
                * apply GMP_E_Var with z1. assumption. unfold p_map. simpl. 
                    destruct (Nat.eq_dec l2 l1) as [Neq | Nneq].
                        ** subst. admit.
                        ** now destruct (Nat.eq_dec l1 l1).
                * apply GMP_E_Var with z2. assumption. unfold p_map. simpl.
                    now destruct (Nat.eq_dec l2 l2) as [Neq | Nneq].
                *  unfold p_map. simpl. destruct (Nat.eq_dec l2 l1) as [Neq | Nneq].
                    ** subst. admit.
                    ** now destruct (Nat.eq_dec l1 l1).
                * unfold p_map. simpl. destruct (Nat.eq_dec l2 l1) as [Neq | Nneq] ;  now destruct (Nat.eq_dec l2 l2).
    }

     unfold CMP. destruct (ty e1) eqn:T1, (ty e2) eqn:T2 ;

    (* get rid of impossible void type *)
    try (unfold ty in T2 ; destruct e2 eqn:X; try easy ; subst ; inversion H1 ; inversion H5; easy) ;
    try (unfold ty in T1;  destruct e1 eqn:X; try easy; subst; inversion H0; inversion H5; easy);
    (* when ty e1 & ty e2 != int *)
    try (exists M{l2\z2,l1\z1} ; intros ; now apply NotInt). clear NotInt.

     
     (* both ty(e1) = int and ty(e2) = int *)
     inversion H0; inversion H1; inversion H5; inversion H7 ; try (subst ; easy). clear H8 H9.
        exists M. intros v l Hv _ _. destruct (Z.lt_trichotomy z1 z2) as [inf' | [ eq' | sup']].
        
        (* z1 < z2 *)
        * assert (cmp := inf'). apply <- inf in inf'. clear eq inf sup. rewrite <- H5, <-H7 in cmp.
            destruct x,x0. constructor. apply S_IfTrue with one. inversion H4. inversion H6.
            +  split... subst.  eapply C_E_BinOpTrue... now apply Z.ltb_lt.
            + constructor... replace a with (⋄ C_Sub 0 1 ⁱⁿᵗ suboneinRange)...

        (* z1 = z2 *)
        * assert (cmp := eq'). rewrite <- eq in eq'.  clear eq inf sup. rewrite <- H5, <-H7 in cmp.
            destruct x,x0. inversion H4. inversion H6.  simpl in cmp. subst. constructor. constructor... 

        (* z1 > z2 *)
        * apply Z.lt_gt in sup'. assert (cmp := sup'). apply <- sup in sup'.  clear inf eq sup.
          destruct x, x0. inversion H4. inversion H6. constructor. apply S_IfFalse.
            + econstructor... subst. simpl in *. unfold Z.ltb. now rewrite cmp.
            + apply S_IfTrue with one ; subst... split... subst.  eapply C_E_BinOpTrue... 
                    rewrite Z.gtb_ltb. rewrite Z.ltb_lt. now rewrite <- Z.gt_lt_iff.
Admitted.




Lemma semantics_of_the_binop_macro_int :
    forall (Ω:Ω) (M:𝓜) (op:fsl_binop_int) c r e1 e2 v1 v2 z1 z2 (ir: Int.inRange (⋄ (□ op) z1 z2) ) l1 l2 lr,
    type_of_value ((fst Ω) c) = Some C_Int ->
    Ω ⋅ M |= e1 ⇝ z1 ->
    Ω ⋅ M |= e2 ⇝ z2 ->
    let zr := ⋄ (□ op) z1 z2 in

    (fst Ω) v1 = Some (VMpz l1) /\  (fst Ω) v2 = Some (VMpz l2) /\ ( (fst Ω) r = Some (VMpz lr) ) ->
    exists M', forall v n, (fst Ω) v = Some (VMpz n) ->
    ~ ((fst Ω) v1 = (fst Ω) v) /\ ~ ((fst Ω) v2 = (fst Ω) v)  -> M n = M' n -> 
    Ω ⋅ M |= (binop_ASSGN op (C_Int,c) e1 e2 r v1 v2) => ((fst Ω){c\zr ⁱⁿᵗ ir}, snd Ω) ⋅ M'
    .

Proof with eauto with rac_hint.
    intros. destruct H2 as (v1l & v2l & rl).  
    assert (NotInt : 
    exists M', forall v n, (fst Ω) v = Some (VMpz n) ->
    ~ ((fst Ω) v1 = (fst Ω) v) /\ ~ ((fst Ω) v2 = (fst Ω) v)  -> M n = M' n -> 
    Ω ⋅ M |= <{

        (mpz_ASSGN v1 e1);
        (mpz_ASSGN v2 e2);
        (Definitions.op op r v1 v2);
        (int_ASSGN c (C_Id r Mpz))
        
        }> => ((fst Ω){c\zr ⁱⁿᵗ ir}, snd Ω) ⋅ M'
    
    ). {
        exists M{lr\zr,l2\z2,l1\z1}. intros. 
    apply GMP_Seq with Ω M{l1\z1}. apply semantics_of_the_mpz_assgn_macro...
    apply GMP_Seq with Ω M{l2\z2,l1\z1}. apply semantics_of_the_mpz_assgn_macro... admit.
    apply GMP_Seq with Ω M{lr\zr,l2\z2,l1\z1}. 
    apply S_op with l1 l2...
    * constructor. admit.
    * unfold p_map. simpl. destruct Nat.eq_dec.
        + admit.
        + now destruct Nat.eq_dec.
    * constructor. admit.
    * unfold p_map. simpl. now destruct Nat.eq_dec.
    * apply semantics_of_the_int_assgn_macro...  apply M_Mpz with lr.
        +  constructor. admit. 
        +  unfold p_map. simpl. now destruct Nat.eq_dec. 
    }
    
    unfold binop_ASSGN. destruct (ty e1) eqn:T1, (ty e2) eqn:T2 ; 
    (* get rid of impossible void type *)
    try (unfold ty in T2 ; destruct e2 eqn:X; try easy ; subst ; inversion H1 ; inversion H5; easy) ;
    try (unfold ty in T1;  destruct e1 eqn:X; try easy; subst; inversion H0; inversion H5; easy);
    (* when ty e1 & ty e2 != int *)
    try (exists M{lr\zr,l2\z2,l1\z1} ; intros ; now apply NotInt). clear NotInt.


    exists M. intros. inversion H0 ; inversion H1;  subst ; constructor ; constructor ; admit.
Admitted.



Lemma semantics_of_the_binop_macro_mpz :
    forall (Ω:Ω) (M:𝓜) (op:fsl_binop_int) c y r e1 e2 v1 v2 z1 z2 l1 l2,
    type_of_value ((fst Ω) c) = Some C_Int ->
    Ω ⋅ M |= e1 ⇝ z1 ->
    Ω ⋅ M |= e2 ⇝ z2 ->
   
    let zr := ⋄ (□ op) z1 z2 in
    (fst Ω) v1 = Some (VMpz l1) /\  (fst Ω) v2 = Some (VMpz l2) /\  (fst Ω) c = Some (VMpz y) ->
    exists M', forall v n, (fst Ω) v = Some (VMpz n) ->
    ~ ((fst Ω) v1 = (fst Ω) v) /\ ~ ((fst Ω) v2 = (fst Ω) v)  -> M n = M' n -> 
    Ω ⋅ M |= (binop_ASSGN op (T_Ext Mpz,c) e1 e2 r v1 v2) => Ω ⋅ M'{y\zr}
    .
Proof with eauto with rac_hint.
    intros. exists M{l2\z2,l1\z1}. intros. destruct H2 as (v1l & v2l & rl). unfold binop_ASSGN.
    apply GMP_Seq with Ω M{l1\z1}.
    - apply semantics_of_the_mpz_assgn_macro...
    - apply GMP_Seq with Ω M{l2\z2,l1\z1}. 
        * apply semantics_of_the_mpz_assgn_macro... admit.
        * apply S_op with l1 l2  ...
            + constructor. admit. 
            + unfold p_map. simpl. destruct Nat.eq_dec.
                ++ admit.
                ++ now destruct Nat.eq_dec.
            + constructor. admit.
            + unfold p_map. simpl. now destruct Nat.eq_dec.
Admitted.


(* Preservation of the semantics *)

Open Scope mini_fsl_scope.

Lemma semantics_of_term_translation : 
    forall (t:fsl_term) Ω Γ Ψ, 
    I1 Ω Γ ->
    I2 Ψ ->
    (exists (z:ℤ), Ω |= t => z)
        <-> True.
Proof.
Admitted.
