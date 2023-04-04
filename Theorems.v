Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import RAC.Semantics.


Fact eq_env_partial_order :  forall e e' v z, e ⊑ e' ->  z <> UInt /\ z <> UMpz -> (fst e) v = Some z -> (fst e') v = Some z.
Proof.
    intros. destruct H with v ; try assumption ; try rewrite H2 in H1 ; try injection H1 as Eq ; subst ; try assumption.
    - destruct H0 as [uint _]. destruct uint. reflexivity.
    - destruct H0 as [_ umpz]. destruct umpz. reflexivity.
    - discriminate.
Qed.

#[global] Hint Constructors c_exp_sem  : core.
#[global] Hint Constructors c_statement  : core.
#[global] Hint Constructors c_exp  : core.
#[global] Hint Constructors c_stmt_sem  : core.
#[global] Hint Constructors env_partial_order : core.

Lemma weakening_of_expression_semantics : 
forall T env (e : @c_exp T) (x:𝕍),
    env |= e => x <-> (forall env', env ⊑ env' ->  env' |= e => x)
.
Proof with auto.
split.
- generalize dependent x. induction e.
    * intros v H env' Inc. inversion H...
    * intros v H env' Inc. inversion H.
        eapply eq_env_partial_order in Inc ; eauto.
        split ; congruence.
    * intros v H env' Inc. inversion H. eauto.
    * intros. inversion H ; eauto.
- auto using refl_env_partial_order.
Qed.


Open Scope mini_c_stmt_scope.
Lemma weakening_of_statement_semantics_1 :
    forall Ω₀ M₀ s Ω₁ M₁,
    Ω₀ ⋅ M₀ |= s => Ω₁ ⋅ M₁ <->
    forall Ω₀' M₀', (Ω₀ , M₀) ⊑ (Ω₀', M₀') ->
     exists Ω₁' M₁', 
     (Ω₁ , M₁) ⊑ (Ω₁', M₁') /\  Ω₀' ⋅ M₀' |= s => Ω₁'⋅ M₁'.
Proof.
    (* split. 
    - induction s ; intro H ; inversion H ; subst ; intros.
        * exists Ω₀'. exists M₀'. split. apply H0. constructor.
        * exists ((fst Ω₀'){var\z}, (snd Ω₀')). exists M₀'. destruct H0 as [H0 _]. split.
         ** split. 
            *** intro x. destruct Ω₀,Ω₀'. apply <- env_partial_order_next. apply (H0 x).
            *** apply fixme.
         ** constructor. apply (weakening_of_expression_semantics Ω₀) ; assumption.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
        * admit.
    - intros. destruct H with Ω₀ M₀ as [Ω₀' [M₀' [[Inc fixme] H1]]]; subst; clear H. 
        * constructor ; constructor.
        * inversion H1 ; subst.
            ** admit.
             ** replace  Ω₁ with ((fst Ω₀) {x \ z}, snd Ω₀). replace M₁ with M₀' . apply S_Assign.
               *** assumption.
               *** admit.
               *** admit.
            ** *)
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


(* Theorem absence_of_dangling_pointers :
    forall n (z:=VMpz n) (mem_state:𝓜) (var_env:Ωᵥ), 
        mem_state n <> ⊥ n <-> 
        exists x, var_env x = Some z /\
        ~(exists x', x <> x' -> var_env x <> Some z)
.
Admitted. *)
