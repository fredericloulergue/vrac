From Coq Require Import Strings.String Logic.FinFun Setoids.Setoid ZArith.ZArith.

From RAC Require Import Utils.
From RAC Require Export Environment.

Import FunctionalEnv Domain.
Import RecordSetNotations.

#[local] Open Scope utils_scope.
#[local] Open Scope domain_scope.

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


(* strong Environment relation facts *)

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



Fact strong_reverse_dom_same_env : forall (ev' ev : Env)  (x :𝓥) (v: 𝕍) (s rev : location -> location) 
    (Hbij: Bijective_wit s rev),

    strong_env_mem_partial_order ev' ev {|f:=s; f_rev:=rev; Hbij:=Hbij|} ->
    ev x = Some v ->
    (dom ev')%utils x ->
    ev' x = Some (induced rev v)
.
Proof.
    intros ev' ev x v s rev Hbij  [Hrenv _] Hevx [v' Hdom].  inversion Hbij.
    specialize (Hrenv x).  apply Hrenv in Hdom as H4. destruct v, v'; simpl in * ; try congruence. 
    - destruct v , v0; simpl in H4; try congruence.
        + destruct l; simpl in H4;  congruence.
        + destruct l, l0; simpl in H4; congruence.  
    - destruct v; simpl in H4;  try congruence.
        destruct l; simpl in H4;  congruence.
Qed.


Fact strong_reverse_dom_same_mem : forall (ev' ev : Env) (x:location) (v: mpz_val) (s rev : location -> location) 
    (Hbij: Bijective_wit s rev), 

    strong_env_mem_partial_order ev' ev {|f:=s; f_rev:=rev; Hbij:=Hbij|}  ->

    ev.(mstate) x = Some v ->
    (dom ev'.(mstate))%utils (rev x) ->
    ev'.(mstate) (rev x) = Some v
.
Proof.
    intros ev' ev x v s rev Hbij [_ Hrmem] Hevx [v' Hdom]. inversion Hbij. red in Hrmem.  
    specialize (Hrmem (rev x)). apply Hrmem in Hdom as H4.  simpl in *. congruence.
Qed.



(* Environment relation facts *)

Program Definition f_id: σ := {|f :=fun x => x ; f_rev := fun x => x|}.
Final Obligation. red. easy. Qed.

Fact _refl_env_partial_order : 
    reflexive Ω (fun e e' => env_partial_order e e' f_id).
Proof.
    intros [v l]. 
    intros var. destruct (v var) as [val |] eqn:res.
    - destruct val.
        + destruct v0.
            * now apply EsameInt with n.
            * destruct l0 as [l0|].
                -- now  apply EsameMpz with l0. 
                -- now apply ENullPtr.
        + destruct uv.
            * apply EundefInt with u; eauto.
            * apply EundefMpz with u; eauto.
    - apply Enone ; auto.
Qed.

Corollary refl_env_partial_order :  reflexive Ω (fun e e' => e ⊑ e')%env.
Proof.
    pose proof _refl_env_partial_order. red in H.
    intros e. specialize (H e). now eexists.
Qed.

Fact _refl_env_partial_order_strong : 
    reflexive Ω (fun e e' => strong_env_partial_order e e' f_id).
Proof.
    intros [v l] x y val' Hval'.
    destruct val'.
    + destruct v0.
        * assumption.
        * destruct l0 as [l0|]; assumption.
    + destruct uv; assumption.
Qed.


Corollary refl_env_partial_order_strong :  reflexive Ω exist_strong_env_partial_order.
Proof.
    pose proof _refl_env_partial_order_strong. red in H.
    intros e. specialize (H e). now eexists.
Qed.

Program Definition f_trans (f1: σ) (f2 : σ) : σ := {|f:=fun x => f2 (f1 x) ; f_rev:=fun x => f1.(f_rev) (f2.(f_rev) x)|}.
Final Obligation.
    destruct f1, f2. destruct Hbij, Hbij0. simpl. split; congruence.
Qed. 

(* Program Definition f_trans' (e1 e2 e3: Ω) (f1: σ' e1 e2) (f2 : σ' e2 e3) : σ' e1 e3 := {|s:=f_trans f1 f2 |}. 
Final Obligation.
    destruct f1,f2. simpl in *. apply Hbij_f_fresh in H.  apply Hbij_f_fresh0 in H. now specialize (H v).
Qed. *)

Fact _trans_env_partial_order : forall (x y z:Ω) f1 f2, 
    env_partial_order x y f1 ->
    env_partial_order y z f2 -> 
    env_partial_order x z (f_trans f1 f2).
Proof.
    intros  e1 e2 e3 sub1 sub2 Hrel1 Hrel2 var. destruct Hrel1 with var ; specialize (Hrel2 var).
    - apply EsameInt with n;[easy|]. inversion Hrel2 ; congruence.
    - apply EsameMpz with l ; inversion Hrel2; simpl in * ; try congruence.
        + rewrite H0 in H1. inversion H1. now subst.
        + now rewrite H1 in H0. 
    - apply ENullPtr;[easy|]. inversion Hrel2; simpl in *; try congruence. now  rewrite H0 in H1.
    - apply EundefInt with u.
        + assumption.
        + inversion Hrel2 ; destruct H0 ; eauto ; try congruence ; try (destruct H0 ; congruence).
    - apply EundefMpz with u;[easy|].  inversion Hrel2; destruct H0; try congruence || (destruct H0 ; congruence) ;simpl in *.
        + right. now exists (sub2 l).
        + destruct H0. right. now exists None.
    - now apply Enone.
Qed.


Fact trans_env_partial_order : transitive Ω (fun e e' => e ⊑ e')%env.
Proof.
    intros e1 e2 e3 [f1 H1] [f2 H2]. exists (f_trans f1 f2).
    now eapply _trans_env_partial_order. 
Qed.


(* 
Fact antisym_env_partial_order : forall env env',
    env_partial_order env' env /\ env_partial_order env env' -> forall v, env v = env' v.

Proof.
    intros env env' [[[f1 Hf1] H1] [[f2 Hf2] H2]] v. specialize (H1 v). inversion H1.
    - congruence. 
    - destruct H2 with v; try congruence. clear H1. clear H2. simpl in *. admit.
    - congruence.
    - destruct H0 ; destruct H0;  destruct H2 with v; congruence.
    - destruct H0 ; destruct H0;  destruct H2 with v; congruence.
    - destruct H2 with v; destruct H0 ; try congruence  || (destruct H3; destruct H0 ; congruence).
Qed. *)



#[global] Add Relation Ω (fun e e' => e ⊑ e')%env
    reflexivity proved by refl_env_partial_order
    transitivity proved by trans_env_partial_order as Renv.


#[global] Add Relation Ω exist_strong_env_partial_order
    reflexivity proved by refl_env_partial_order_strong
    (* transitivity proved by trans_env_partial_order *)  as Renvstrong.

Fact _refl_mem_partial_order: reflexive 𝓜  (fun m m' => mem_partial_order m m' f_id).
Proof.
    easy.
Qed.    

Corollary refl_mem_partial_order: reflexive 𝓜  exist_mem_partial_order.
Proof.
    eexists. apply _refl_mem_partial_order.
Qed.    


Fact _trans_mem_partial_order: forall (m1 m2 m3: 𝓜) f1 f2, 
    mem_partial_order m1 m2 f1 ->
    mem_partial_order m2 m3 f2 -> 
    mem_partial_order m1 m3 (f_trans f1 f2).
Proof.
    intros mem mem' mem'' sub1 sub2 Hrel1 Hrel2 l i H. simpl in *.
    specialize (Hrel1 l i). apply Hrel1 in H as HH.
    specialize (Hrel2 (sub1 l) i). now apply Hrel2 in HH.
Qed.


Corollary trans_mem_partial_order: transitive 𝓜 exist_mem_partial_order.
Proof.
    intros m m' m'' [f1 H1] [f2 H2]. exists (f_trans f1 f2). now apply _trans_mem_partial_order with m'.
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

    
Fact _refl_env_mem_partial_order : 
    reflexive Env (fun e e' => env_mem_partial_order e e' f_id).
Proof.
    intros e. now pose proof (_refl_env_partial_order e).
Qed.


Corollary refl_env_mem_partial_order : reflexive Env (fun e e' => e ⊑ e')%envmem.
    pose proof _refl_env_mem_partial_order. red in H.
    intros e. specialize (H e) as [Hbij Hp]. now exists f_id.
Qed.


Fact _trans_env_mem_partial_order : forall (x y z: Env) f1 f2, 
    env_mem_partial_order x y f1 ->
    env_mem_partial_order y z f2 -> 
    env_mem_partial_order x z (f_trans f1 f2).
Proof.
    intros e e' e'' f1 f2 [Henv1 Hmem1] [Henv2 Hmem2]. split. 
    - now eapply _trans_env_partial_order.
    - now eapply _trans_mem_partial_order.
Qed.

Fact trans_env_mem_partial_order : transitive Env (fun e e' => e ⊑ e')%envmem.
Proof.
        intros e1 e2 e3 [f1 H1] [f2 H2]. exists (f_trans f1 f2).
        now apply _trans_env_mem_partial_order with e2.
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

Fact eq_int_env_partial_order :  forall e e' v n, (e ⊑ e')%env -> 
    e v = Some (Def (VInt n)) -> e' v = Some (Def (VInt n)).
Proof.
    intros e e' v z [f He] Hsome. destruct (He v); congruence.  
Qed.



Fact eq_mpz_env_partial_order :  forall e e' sub, 
    env_partial_order e e' sub -> 
    forall v mpz, e v = Some (Def (VMpz mpz)) -> e' v = Some (induced sub (VMpz mpz)).
Proof.
    intros e e' sub He v l Hsome. destruct (He v); try congruence.
    - rewrite Hsome in H. now inversion H.
    - destruct l;  simpl ; rewrite Hsome in H; now inversion H.
Qed.

Fact eq_defined_mpz_mem_partial_order : forall e e' sub, 
    env_mem_partial_order e e' sub -> 
    forall (l:location) z, e.(mstate) l = Some (Defined z) -> e'.(mstate) (sub l) = Some (Defined z).
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


Fact mem_partial_order_add : forall m m' (l:location) (z : mpz_val)
    (sub : σ),
    mem_partial_order m m' sub -> 
    mem_partial_order (m {l \ z}) (m' {sub l \ z}) sub.
Proof.
    intros e e' l z sub Hmem.
    intros l'.  intros mpz H. simpl in *. destruct (eq_dec l l').
    - subst. rewrite p_map_same in H. inversion H. subst. apply p_map_same.
    - rewrite p_map_not_same in H; [|easy]. apply p_map_not_same_eq.
        + destruct sub. simpl in *. rewrite <- bijective_eq_iff_f_eq; [easy|].
            now exists f_rev.
        + specialize (Hmem l'). now apply Hmem in H. 
Qed.


Fact env_partial_order_add : forall Ω₀ Ω₀' sub, 
    env_partial_order Ω₀ Ω₀' sub -> 
    (forall var' z, 
    env_partial_order (Ω₀ <| vars ::= {{var' \ z}} |>) (Ω₀' <| vars ::= {{var' \ induced sub z}} |>) sub
    )%envmem.
Proof with eauto with rac_hint.
    intros [v l][v' l'] sub Henv x z ; simpl in *.
    intros var. destruct (string_dec x var) as [Heq|Hneq].
    - subst. simpl. destruct z. 
        + destruct v0.
            * apply EsameInt with n ;  apply p_map_same.
            * destruct l0 eqn:L0.
                ++ apply EsameMpz with l1; apply p_map_same.
                ++ apply ENullPtr; simpl; now apply p_map_same.
        + destruct uv.
            ++ apply EundefInt with u; autounfold with rac_hint; simpl...
            ++ apply EundefMpz with u; autounfold with rac_hint; simpl...

    - apply not_eq_sym in Hneq. epose proof (p_map_not_same v var x ?[z] Hneq) as H0. simpl. remember (v var) as res. destruct res as [z'|] eqn:RES.
        + destruct z' eqn:Z; subst.
            * {
                set (mkEnv (mkΩ v l) empty_env) as env;
                set (mkEnv (mkΩ v' l') empty_env) as env'.  
                destruct v0.
                - apply EsameInt with n ; simpl.
                    + apply H0.
                    + apply p_map_not_same_eq... 
                        apply (eq_int_env_partial_order env env' var n)... now exists sub.
                - destruct l0.
                    + apply EsameMpz with l0; simpl...
                        autounfold with rac_hint. apply p_map_not_same_eq...
                        now apply (eq_mpz_env_partial_order env env' sub Henv var (Some l0)).
                    + apply ENullPtr... simpl.  apply p_map_not_same_eq...
                        now apply (eq_mpz_env_partial_order env env' sub Henv var None).
            }

            * { 
                specialize (Henv var). destruct uv.
                - apply EundefInt with u;subst ;simpl in *. 
                    + apply H0.
                    + inversion Henv; simpl in *; try congruence. destruct H1 as [[n H1]|[n H1]].
                        ++ left. exists n. now apply p_map_not_same_eq.
                        ++ right. exists n. now apply p_map_not_same_eq.
                - apply EundefMpz with u; subst ; simpl in *.
                    + apply H0.
                    + destruct Henv; simpl in *; try congruence. destruct H1 as [[n H1]|[n H1]].
                        ++ left. exists n. now apply p_map_not_same_eq.
                        ++ right. exists n. now apply p_map_not_same_eq.
            }
            + now apply Enone.
Qed.


Fact env_partial_order_add_strong : forall Ω₀ Ω₀' sub, 
    strong_env_partial_order Ω₀ Ω₀' sub -> 
    (forall x z, 
    strong_env_partial_order (Ω₀ <| vars ::= {{x \ z}} |>) (Ω₀' <| vars ::= {{x \ induced sub z}} |>) sub
    )%envmem.
Proof.
    intros * Henv *. 
    intros x1 x2 v H. destruct (eq_dec x x2).
    - subst. simpl in H. rewrite <- p_map_single_back_front_eq, p_map_same  in H; inversion H. 
        apply p_map_same.
    - simpl in H. apply p_map_not_same_eq in H; [| easy]. apply p_map_not_same_eq; [easy|]. 
    now apply Henv.
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
        unfold p_map_addall_back. unfold p_map_addall_front. simpl. admit. (* should be able to use Henv *)
    - simpl in *.  destruct zargs as [| zargs_hd zargs_tl] eqn:zargsEqn; [discriminate|].  
        destruct (IHxargs zargs_tl sub) as [Hindenv _]; auto. clear IHxargs. simpl in *.
        unfold p_map_addall_back. unfold p_map_addall_front. simpl. admit.
Admitted.


Fact type_of_value_env : forall (env:Ω) (var:𝓥), type_of_value (env var) <> None -> env var <> None.
Proof.
    intros env var Hty. now destruct (env var) as [v|].
Qed.


Fact induced_ty_same v (sub:σ) : type_of_value (Some (induced sub v)) = type_of_value (Some v).
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

