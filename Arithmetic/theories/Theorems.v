From Coq Require Import ZArith.ZArith Strings.String.
From RAC Require Import Utils Environnement Macros.
From RAC.Languages Require Import Syntax Semantics.

Open Scope utils_scope.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.


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
