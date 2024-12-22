From Coq Require Import ZArith String.
From RAC Require Import Utils Environment.
From RAC.Languages Require Import Syntax Semantics.

Open Scope Z.

Import Environment.Facts.
Import FunctionalEnv.

Section GMPFacts.

    Context {fe : rac_prog_fenv}.

    Fact _no_mem_aliasing_gmp : @_no_mem_aliasing _ _ _gmp_stmt_sem fe.
    Proof with auto with rac_hint.
        intros ev s ev' Hnoalias H. induction H
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
            destruct H3 as [sup [inf eq]]. destruct (Z.lt_trichotomy zx zy) as [Hinf | [Heq | Hsup]].
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

    (* helper lemma for gmp cmp semantics *)
    Fact cmp_induced : forall zx zy (b: 𝕍) sub,
        (zx > zy <-> b = one) /\ (zx < zy <-> b = sub_one) /\ (Z.eq zx zy <-> b = zero)
        -> 
        (zx > zy <-> induced sub b = one) /\
    (zx < zy <-> induced sub b = sub_one) /\ (Z.eq zx zy <-> induced sub b = zero).
    Proof.
        intros zx zy b sub (Hone & Hsubone &Hzero). split.
        - split.
            * intros Hzxzy. apply Hone in Hzxzy. now subst.
            * intros Hzxzy. apply induced_int_iff in Hzxzy. inversion Hzxzy. now apply Hone.
        - split.
        * split.
                + intros Hzxzy. apply Hsubone in Hzxzy. now subst.
                + intros Hzxzy. apply induced_int_iff in Hzxzy. inversion Hzxzy. now apply Hsubone.
            * split.
                + intros Hzxzy. apply Hzero in Hzxzy. now subst.
                + intros Hzxzy. apply induced_int_iff in Hzxzy. inversion Hzxzy. now apply Hzero.
    Qed.


    Fact _determinist_gmp_stmt_eval : _determinist_stmt_eval generic_exp_sem _gmp_stmt_sem (fe:=fe).
    Admitted.



End GMPFacts.