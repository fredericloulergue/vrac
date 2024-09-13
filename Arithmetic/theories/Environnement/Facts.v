From Coq Require Import String FinFun Setoid.
From RecordUpdate Require Import RecordUpdate.
From RAC Require Import Utils.
From RAC Require Export Environnement.

Import FunctionalEnv Domain.
Import RecordSetNotations.

#[local] Open Scope utils_scope.

(* σ-equivalence facts *)

Fact bijective_eq_iff_f_eq  {A B:Type} : forall (f: A -> B) x y , Bijective f -> x = y <-> f x = f y. 
Proof.
    intros. destruct H as [f_inv [H1 H2]]. split ; congruence.
Qed.

Fact list_map_id_eq {A B} (f : A -> B): forall x x', 
    Injective f ->
    List.map f x = List.map f x' <-> x  = x'.
Proof.
    split; intros; subst; auto. generalize dependent x'. induction x.
    -  simpl. intros x'. destruct x'; [trivial|].  intros. simpl in H0. inversion H0.
    - intros. destruct x'; simpl in *; [inversion H0|]. inversion H0. f_equal; auto. 
Qed. 


Fact bijective_injective {A B : Type} (f : A -> B) :
    Bijective f -> Injective f.
Proof.
    intros [g [H H']] x y e.
    rewrite <- (H x), <- (H y).
    now rewrite e.
Qed.

Fact bijective_surjective {A B : Type} (f : A -> B) :
    Bijective f -> Surjective f.
Proof.
    intros [g [H H']] y. now exists (g y).
Qed.

Fact induced_not_mpz_transparent (f: location -> location) : forall v, 
    (forall l, v <> Def (VMpz (Some l))) -> induced f v = v.
Proof.
        intros. destruct v; auto. destruct v; auto. destruct l; auto. congruence.
Qed.

Fact induced_int_iff (f: location -> location) : forall v n, 
    induced f v = (VInt n) <-> v = VInt n.
Proof.
        intros. split; intros H.
        - unfold induced in H. simpl in H. destruct v; try congruence.
            destruct v; try congruence. now destruct l.
        - subst. now apply induced_not_mpz_transparent.
Qed.


Fact id_bijective {T:Type} : @Bijective T T (fun T => T). 
Proof.
    now exists (fun x => x).
Qed.

Fact bijective_comp_bijective {A B C: Type} (fa: {f: A -> B | Bijective f}) (fb: {f: B -> C | Bijective f}) : 
    Bijective (fun x => (proj1_sig fb) (proj1_sig fa x)).
Proof. 
    destruct fa as [a [a_inv [a1 a2]]] ,fb as [b [b_inv [b1 b2]]].
    exists (fun x => a_inv (b_inv x)). simpl in *. split ; congruence. 
Qed.




(* strong environnement relation facts *)

Fact strong_env_mem_stronger : forall e e' f, 
    strong_env_mem_partial_order e e' f -> 
    env_mem_partial_order e e' f.
Proof with eauto with rac_hint.
    intros e e' f [Hstrenv Hstrmem]. split ; [|trivial].
    intros v. destruct (e v) as [val |] eqn:res...
    specialize (Hstrenv v v val res). destruct val...
        + destruct v0; simpl in *... destruct l...
        + destruct uv...
Qed.



Fact strong_reverse_dom_same : forall (ev' ev : Env) x (v: 𝕍) (s rev : location -> location) 
    (H1 :forall x, rev (s x) = x ) (H2: forall y, s (rev y) = y),

    strong_env_mem_partial_order ev' ev 
        (exist (fun f => Bijective f) s
                (ex_intro
                    (fun g =>
                        (forall x, g (s x) = x) /\ (forall y, s (g y) = y)
                    )
                    rev (conj H1 H2)
                )
        )%type ->
    ev x = Some v ->
    (dom ev')%utils x ->
    ev' x = Some (induced rev v)
.
Proof.
    intros ev' ev x v s rev H1 H2 [Hrenv _] Hevx [v' Hdom].  
    specialize (Hrenv x).  apply Hrenv in Hdom as H4. destruct v, v'; simpl in * ; try congruence. 
    - destruct v , v0; simpl in H4; try congruence.
        + destruct l; simpl in H4; try congruence.
        + destruct l, l0; simpl in H4; try congruence.
    - destruct v; simpl in H4; try congruence.
        destruct l; simpl in H4; try congruence.
Qed.




(* environnement relation facts *)

Fact _refl_env_partial_order : reflexive Ω (fun e e' => env_partial_order e e' (exist _ _ id_bijective)).

Proof.
    intros [v l] var. destruct (v var) as [val |] eqn:res. destruct val.
    - destruct v0.
        * now apply EsameInt with n.
        * destruct l0 as [l0|].
            ** now apply EsameMpz with l0. 
            ** now apply ENullPtr.
    - destruct uv.
        * apply EundefInt with u; eauto.
        * apply EundefMpz with u; eauto.
    - apply Enone ; auto.
Qed.

Corollary refl_env_partial_order :  reflexive Ω (fun e e' => e ⊑ e')%env.
Proof. 
    eexists. apply _refl_env_partial_order.
Qed.

Fact _trans_env_partial_order : forall (x y z:Ω) f1 f2, 
    env_partial_order x y f1 ->
    env_partial_order y z f2 -> 
    env_partial_order x z (exist _ _ (bijective_comp_bijective f1 f2)).
Proof.
    intros  e e' e''  sub1 sub2 Hrel1 Hrel2 var. destruct Hrel1 with var ; specialize (Hrel2 var).
    * apply EsameInt with n. easy. inversion Hrel2 ; congruence.
    * apply EsameMpz with l ; inversion Hrel2; simpl in * ; try congruence.
        ** rewrite H0 in H1. inversion H1. now subst.
        ** now rewrite H1 in H0. 
    * apply ENullPtr;[easy|]. inversion Hrel2; simpl in *; try congruence. now  rewrite H0 in H1.
    * apply EundefInt with u.
        + assumption.
        + inversion Hrel2 ; destruct H0 ; eauto ; try congruence ; try (destruct H0 ; congruence).
    * apply EundefMpz with u;[easy|].  inversion Hrel2; destruct H0; try congruence || (destruct H0 ; congruence) ;simpl in *.
        + right. now exists (proj1_sig sub2 l).
        + destruct H0. right. now  exists None.
    * now apply Enone.
Qed.


Fact trans_env_partial_order : transitive Ω (fun e e' => e ⊑ e')%env.
Proof.
    intros e e' e'' [f1 H1] [f2 H2]. exists (exist _ _ (bijective_comp_bijective f1 f2)).
    now apply _trans_env_partial_order with e'. 
Qed.


(* 
Fact antisym_env_partial_order : forall env env',
    env_partial_order env' env /\ env_partial_order env env' -> forall v, env v = env' v.

Proof.
    intros env env' [[[f1 Hf1] H1] [[f2 Hf2] H2]] v. specialize (H1 v). inversion H1.
    - congruence. 
    - destruct H2 with v; try congruence. clear H1. clear H2. simpl in *.
       admit.
    - congruence.
    - destruct H0 ; destruct H0;  destruct H2 with v; congruence.
    - destruct H0 ; destruct H0;  destruct H2 with v; congruence.
    - destruct H2 with v; destruct H0 ; try congruence  || (destruct H3; destruct H0 ; congruence).
Qed. *)



#[global] Add Relation Ω (fun e e' => e ⊑ e')%env
    reflexivity proved by refl_env_partial_order
    transitivity proved by trans_env_partial_order as Renv.



Fact _refl_mem_partial_order : reflexive 𝓜  (fun e e' => mem_partial_order e e' (exist _ _ id_bijective)).
Proof.
    easy.
Qed.    

Corollary refl_mem_partial_order : reflexive 𝓜  (fun e e' => e ⊑ e')%mem.
Proof.
    eexists. apply _refl_mem_partial_order.
Qed.    


Fact _trans_mem_partial_order : forall (x y z: 𝓜) f1 f2, 
    mem_partial_order x y f1 ->
    mem_partial_order y z f2 -> 
    mem_partial_order x z (exist _ _ (bijective_comp_bijective f1 f2)).
Proof.
    intros mem mem' mem'' sub1 sub2 Hrel1 Hrel2 l i H. simpl in *.
    specialize (Hrel1 l i). apply Hrel1 in H as HH.
    specialize (Hrel2 (proj1_sig sub1 l) i). now apply Hrel2 in HH.
Qed.


Corollary trans_mem_partial_order : transitive 𝓜 (fun e e' => e ⊑ e')%mem.
Proof.
    intros e e' e'' [f1 H1] [f2 H2]. exists (exist _ _ (bijective_comp_bijective f1 f2)). now apply _trans_mem_partial_order with e'.
Qed.

(* Fact antisym_mem_partial_order : forall mem mem', 
    mems_partial_order mem mem' /\ mems_partial_order mem' mem -> forall l, mem l = mem' l.
Proof.
    intros mem mem' [H1 H2] l. destruct (mem l) eqn:Heqn.
    - now apply H1 in Heqn.
    - destruct (mem' l) eqn:Heqn'. apply H2 in Heqn'.
        + congruence.
        + easy.
Qed. *)


#[global] Add Relation 𝓜 (fun e e' => e ⊑ e')%mem
    reflexivity proved by refl_mem_partial_order 
    transitivity proved by trans_mem_partial_order as mem.

    
Fact _refl_env_mem_partial_order : reflexive Env (fun e e' => env_mem_partial_order e e' (exist _ _ id_bijective))%envmem.
Proof.
    intros e.  split.
    -  apply _refl_env_partial_order.
    - apply _refl_mem_partial_order.
Qed.


Corollary refl_env_mem_partial_order : reflexive Env (fun e e' => e ⊑ e')%envmem.
    eexists. apply _refl_env_mem_partial_order.
Qed.


Fact _trans_env_mem_partial_order : forall (x y z: Env) f1 f2, 
    env_mem_partial_order x y f1 ->
    env_mem_partial_order y z f2 -> 
    env_mem_partial_order x z (exist _ _ (bijective_comp_bijective f1 f2)).
Proof.
    intros e e' e'' f1 f2 [Henv1 Hmem1] [Henv2 Hmem2]. split.
    - now apply _trans_env_partial_order with e'.
    - now eapply _trans_mem_partial_order.
Qed.

Fact trans_env_mem_partial_order : transitive Env (fun e e' => e ⊑ e')%envmem.
Proof.
        intros e e' e'' [f1 H1] [f2 H2].   exists (exist _ _ (bijective_comp_bijective f1 f2)).
        now apply _trans_env_mem_partial_order with e'.
Qed.


#[global] Add Relation Env (fun e e' => e ⊑ e')%envmem  
    reflexivity proved by refl_env_mem_partial_order 
    transitivity proved by trans_env_mem_partial_order as env_mem.


(* Fact eq_env_partial_order :  forall e e' v z, (e ⊑ e')%env ->  
    e v = Some (Def z) -> e' v = Some (Def z).
Proof.
    intros e e' v z Hrel He. destruct Hrel. specialize (H v). inversion H; try congruence. rewrite He in H0. injection H0 as H0. subst.
    intros e e' v z Hrel He. destruct Hrel. specialize (H v). inversion H. try congruence.
Qed. *)



Fact empty_env_refl_any_sub: forall s, env_partial_order empty_env empty_env s.
Proof.
    intros s v. now constructor.  
Qed.

Fact empty_mem_refl_any_sub:  forall s, mem_partial_order empty_env empty_env s.
Proof.
    intros s v z H. inversion H. 
Qed.

Fact empty_env_mem_refl_any_sub:  forall s, env_mem_partial_order empty_env empty_env s.
Proof.
        intros s. split.
        - apply empty_env_refl_any_sub.
        - apply empty_mem_refl_any_sub.
Qed.

Fact eq_int_env_mem_partial_order :  forall e e' v n, (e ⊑ e')%envmem -> 
    e v = Some (Def (VInt n)) -> e' v = Some (Def (VInt n)).
Proof.
    intros e e' v z [f [He Hm]] Hsome. destruct (He v); congruence.  
Qed.



Fact eq_mpz_env_mem_partial_order :  forall e e' sub, 
    env_mem_partial_order e e' sub -> 
    forall v mpz, e v = Some (Def (VMpz mpz)) -> e' v = Some (induced (proj1_sig sub) (VMpz mpz)).
Proof.
    intros e e' sub [He Hm] v l Hsome. destruct (He v); try congruence.
    - rewrite Hsome in H. now inversion H.
    - destruct l;  simpl ; rewrite Hsome in H; now inversion H.
Qed.

Fact eq_defined_mpz_mem_partial_order : forall e e' sub, 
    env_mem_partial_order e e' sub -> 
    forall (l:location) z, e.(mstate) l = Some (Defined z) -> e'.(mstate) (proj1_sig sub l) = Some (Defined z).
Proof.
    intros e e' sub [_ Hmem] l z H. specialize (Hmem l).  now destruct Hmem with z.
Qed.


(* Fact sym_env_cond : forall (env env' : Ω), 
(forall v, (dom env - dom env') v ) -> (env ⊑ env')%env -> (env' ⊑ env)%env.

Proof.
    intros env env' H rel v ; destruct H with v as [Hin Hnotin] ; destruct Hnotin ; destruct rel with v.
    - now exists n. 
    - now exists (VMpz l).
    - destruct H1.
        + now exists UInt. 
        + destruct H1. now exists x. 
    - destruct H1.
        + now exists UMpz.
        + destruct H1 as [x]. now exists (VMpz x).
    - destruct Hin. destruct env. simpl in *. congruence.
Qed.

Corollary sym_env_cond_mem : forall (ev ev' : Env), 
(forall v, (dom ev - dom ev') v ) -> (ev ⊑ ev')%envmem ->  (mkEnv ev' ev ⊑ mkEnv ev ev')%envmem.
Proof.
    intros [env mem]. split. now apply sym_env_cond. now destruct H0.
Qed. *)


(* Corollary eq_env_partial_order_add :  forall (e e' :Ω) v v' z z',  (e ⊑ e')%env ->  
    v <> v' ->
    e v = Some (Def z) -> (e'{v'\z'}) v = Some (Def z).
Proof.
    intros [v l] [v' l'] var var' z z' Hrel Hneq H. 
    pose proof (eq_env_partial_order {|vars:=v;binds:=l|} {|vars:=v';binds:=l'|} var z Hrel H).
    pose proof (p_map_not_same {| vars := v'; binds := l' |} var var' z' Hneq). congruence.
Qed. *)


(* Fact eq_mem_partial_order :  
    forall mem mem' z l, (mem ⊑ mem')%mem -> z <> None ->  
    mem l = z ->  mem' l = z.
Proof.
    intros. destruct z.
    - edestruct H; eauto.
    - contradiction.
Qed. *)


Fact mem_def_partial_order_add : forall e e' sub, env_mem_partial_order e e' sub -> 

    (forall (l:location) (z : mpz_val),

            env_mem_partial_order 
                (e <| mstate ::={{l \ z}} |>) 
                (e' <| mstate ::={{proj1_sig sub l \ z}} |>) sub

    ).
Proof.
        intros e e' sub [Henv Hmem] l z. split; [trivial|].
        intros l'.  intros mpz H. simpl in *. destruct (eq_dec l l').
        - subst. unfold p_map_back in H. rewrite p_map_same in H. inversion H. subst.
            unfold p_map_back. apply p_map_same.
        - unfold p_map_back in H. rewrite p_map_not_same in H; [|auto]. apply p_map_not_same_eq.
            * destruct sub. simpl in *. now rewrite <- bijective_eq_iff_f_eq. 
            * specialize (Hmem l'). now apply Hmem in H. 
Qed.


Fact env_partial_order_add : forall Ω₀ Ω₀' sub, 
    env_mem_partial_order Ω₀ Ω₀' sub -> 
    (forall var' z, 
    env_mem_partial_order (Ω₀ <| env; vars ::= {{var' \ z}} |>) (Ω₀' <| env ; vars ::= {{var' \ induced (proj1_sig sub) z}} |>) sub
    )%envmem.
Proof with eauto with rac_hint.
    intros [v l][v' l'] sub H x z.  split.
    - intros var. destruct (string_dec x var) as [Heq|Hneq].
        -- subst. simpl. destruct z. 
            + destruct v0.
                * apply EsameInt with n ;  apply p_map_same.
                * destruct l0 eqn:L0.
                    ++ apply EsameMpz with l1; apply p_map_same.
                    ++ apply ENullPtr; simpl; now apply p_map_same.
            + destruct uv.
                ++ apply EundefInt with u; autounfold with rac_hint; simpl...
                ++ apply EundefMpz with u; autounfold with rac_hint; simpl...

        -- apply not_eq_sym in Hneq. epose proof (p_map_not_same v var x ?[z] Hneq) as H0. simpl. remember (v var) as res. destruct res as [z'|] eqn:RES.
            * destruct z' eqn:Z.
                + { 
                    destruct v0.
                    - apply EsameInt with n ; simpl.
                        + apply H0.
                        + autounfold with rac_hint. apply p_map_not_same_eq...  apply (eq_int_env_mem_partial_order (mkEnv v l) (mkEnv v' l') var n)... now exists sub.
                    - destruct l0.
                        + apply EsameMpz with l0; simpl...
                            autounfold with rac_hint. apply p_map_not_same_eq...
                            now apply (eq_mpz_env_mem_partial_order  (mkEnv v l) (mkEnv v' l') sub H var (Some l0)).
                        + apply ENullPtr... simpl.  apply p_map_not_same_eq...
                         now apply (eq_mpz_env_mem_partial_order  (mkEnv v l) (mkEnv v' l') sub H var None).
                }

                + {
                    destruct uv.
                    - apply EundefInt with u;subst ;simpl. 
                        + apply H0.
                        + destruct H. specialize (H var). simpl in *. destruct H; try congruence. destruct H2 as [[n H2]|[n H2]].
                            ++ left. exists n. now apply p_map_not_same_eq.
                            ++ right. exists n. now apply p_map_not_same_eq.
                    - apply EundefMpz with u; subst ; simpl.
                        + apply H0.
                        + destruct H. specialize (H var). simpl in *. destruct H; try congruence. destruct H2 as [[n H2]|[n H2]].
                            ++ left. exists n. now apply p_map_not_same_eq.
                            ++ right. exists n. now apply p_map_not_same_eq.
                }
            * now apply Enone.

    - intros loc. intros mpz Hloc. simpl in *. destruct  H as [_ H]. specialize (H loc mpz). now destruct H. 
Qed.





Fact env_mem_partial_order_add_mem : forall e1 e1' e2 e2' sub, 
    env_mem_partial_order e1 e2 sub  -> 
    env_mem_partial_order e1' e2' sub -> 
    env_mem_partial_order (e1 <| mstate := e1' |>) (e2 <| mstate := e2' |>) sub.
    
Proof with auto with rac_hint.
    intros e1 e1' e2 e2' sub [H1e H1m] [H2e H2m]. now split.
Qed.



Fact same_int_any_sub :  forall e e' xargs zargs sub, 
    List.length xargs = List.length zargs -> 
    let vargs := List.map (fun x => Def (VInt x)) zargs in 
    env_mem_partial_order e e' sub -> 
    env_mem_partial_order 
        (e <| env; vars ::= p_map_addall_back xargs vargs |>)
        (e' <| env; vars ::= p_map_addall_back xargs vargs |>) sub.
Proof.
    intros e e' xargs. simpl. induction xargs; intros  zargs sub H Henv.
    - simpl in H. symmetry in H. apply List.length_zero_iff_nil in H. subst. simpl.
        unfold p_map_addall_back. unfold p_map_addall_front. simpl.   admit. (* should be able to use Henv *)
    - simpl in *.  destruct zargs as [| zargs_hd zargs_tl] eqn:zargsEqn; [discriminate|].  
        destruct (IHxargs zargs_tl sub) as [Hindenv _]; auto. clear IHxargs. simpl in *.
        unfold p_map_addall_back. unfold p_map_addall_front. simpl. admit.
Admitted.


Fact type_of_value_env : forall (env:Ω) (var:𝓥), type_of_value (env var) <> None -> env var <> None.
Proof.
    intros env var Hty. now destruct (env var) as [v|].
Qed.


Fact induced_ty_same v (sub:σ) : type_of_value (Some (induced (proj1_sig sub) v)) = type_of_value (Some v).
Proof.
    destruct v; simpl; [|trivial]. destruct v; simpl; [trivial|]. now destruct l. 
Qed.

Fact env_same_ty : forall  (Ω Ω' : Env) v t, ((Ω ⊑ Ω')%envmem \/ (Ω' ⊑ Ω)%envmem) -> t <> None -> type_of_value (Ω v) = t <-> type_of_value (Ω' v) = t.
Proof.
    (* intros. 
    match goal with | IncRel : (_ ⊑ _)%env |- _ =>  destruct IncRel with v ; subst end ;
    match goal with 
    | L : apply_env ?Ω v = _,  R : apply_env ?Ω' v = _  |- _ => now rewrite L,R 
    | L : apply_env ?Ω v = _,  R : apply_env ?Ω' v = _ \/ _ |- _ => destruct R as [SomeUInt | [ x Some_n ]]; [now rewrite L,SomeUInt | now rewrite L,Some_n] 
    | L : _ = None,  Contra : _ <> None |- _ =>  now rewrite L in Contra
    end. *)
Admitted.

