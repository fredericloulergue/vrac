From Coq Require Import ZArith.ZArith Strings.String Logic.FinFun Sets.Ensembles Sets.Finite_sets.
From RecordUpdate Require Import RecordUpdate.
From RAC Require Import Utils.
From RAC.Languages Require Import Syntax.


Import FunctionalEnv.

Record fenv {S T : Set} := mk_fenv {
    funs : @𝓕 S T ;
    procs : @𝓟 S T ;
    lfuns : 𝔉 ;
    preds : 𝔓 ;
}.

Module Int16Bounds.
    Open Scope Z_scope.
    Definition m_int := -32768.
    Definition M_int := 32767.
End Int16Bounds.

Module Int := MachineInteger Int16Bounds.



Notation "z ̇" := (Int.of_mi z) (at level 0).
Notation "z 'ⁱⁿᵗ'" := (Int.to_mi z) (at level 99).


Fact zeroinRange : Int.inRange 0.  now split. Qed.
Fact oneinRange : Int.inRange 1. now split. Qed.
Fact suboneinRange : Int.inRange (-1). now split. Qed.
Definition zero :=  0ⁱⁿᵗ zeroinRange.
Definition one := 1ⁱⁿᵗ oneinRange.
Definition sub_one := (-1)ⁱⁿᵗ suboneinRange.



(* adresses and undefined values must be an enumerable set. We use nat for convenience *)
Definition location := nat. 
Definition undefval := nat.

#[global] Instance location_eq_dec : FunctionalEnv.EqDecC location := {eq_dec := Nat.eq_dec}.



#[global] Hint Resolve zeroinRange: rac_hint.
#[global] Hint Resolve oneinRange: rac_hint.
#[global] Hint Resolve suboneinRange: rac_hint.



Inductive value := 
    | VInt (n:Int.MI) :> value (* set of type int, a machine integer (may overflow) *)
    | VMpz (l:option location) (* memory location for values of type mpz, none is a null pointer *) 
.


Inductive undef := 
    | UInt : undefval -> undef (* set of undefined values of type int *) 
    | UMpz : undefval -> undef (* set of undefined values of type mpz *) 
.


Inductive 𝕍 :=  Def (v : value) :> 𝕍 | Undef (uv : undef) :> 𝕍.
Coercion v_int (mi:Int.MI) : 𝕍 := Def (VInt mi). 
Coercion def_v_mpz (l:nat) : 𝕍 := Def (VMpz (Some l)). 
Coercion mpz_loc (l:location) : 𝕍 := VMpz (Some l).

Inductive 𝔹 := BTrue | BFalse.

Inductive mpz_val := Defined (z:Z) :> mpz_val | Undefined (z:Z).


Definition 𝓜 := location ⇀ mpz_val. 


Definition Ωᵥ : Type := 𝓥 ⇀ 𝕍.
Definition Ωₗ : Type := 𝔏 ⇀ ℤ.


(* Coercion ir_z (x:Z) ir : 𝕍 := VInt (x ⁱⁿᵗ ir). *)
Coercion int_option_loc (l:nat) :=  Some l.


(* Coercion VMpz : nat >-> Value. *)
(* 
Definition same_values (v1 v2: option 𝕍) : bool := match v1,v2 with
    | Some (VInt n1), Some (VInt n2) => Int.mi_eqb n1 n2
    | Some (VMpz n1), Some (VMpz n2) => (n1 =? n2)%nat
    | _,_ => false
end
. *)



Import RecordSetNotations.

Record Ω := mkΩ {vars :> Ωᵥ ;  binds :> Ωₗ}.
Definition empty_Ω  : Ω := {|vars:=⊥;binds:=⊥|}.
#[export] Instance etaΩ : Settable _ := settable! mkΩ <vars ; binds>.
Definition apply_env (a : Ω) (v : 𝓥) : option 𝕍 := a.(vars) v.
Coercion apply_env : Ω >-> Funclass.

Record Env := mkEnv {env :> Ω ;  mstate :> 𝓜}.
Definition empty_env : Env := {|env:=empty_Ω;mstate:=⊥|}.
#[export] Instance etaEnv : Settable _ := settable! mkEnv <env ; mstate>.
Definition apply_mem (a : Ω) (l : 𝔏) : option Z := a.(binds) l.
(* Coercion apply_mem : Ω >-> Funclass. *) (* can't use same coercion path *)


Definition σ : Type := {f : location -> location | Bijective f}.

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





Definition induced (f: σ) : 𝕍 -> 𝕍 := fun value => match value with
| Def (VMpz (Some l)) => Def (VMpz (Some (proj1_sig f l)))
| v => v
end.

Fact induced_not_mpz_transparent (f: σ) : forall v, 
    (forall l, v <> Def (VMpz (Some l))) -> induced f v = v.
Proof.
        intros. destruct v; auto. destruct v; auto. destruct l; auto. congruence.
Qed.

Fact induced_int_iff (f: σ) : forall v n, 
    induced f v = (VInt n) <-> v = VInt n.
Proof.
        intros. split; intros H.
        - unfold induced in H. simpl in H. destruct v; try congruence.
            destruct v; try congruence. now destruct l.
        - subst. now apply induced_not_mpz_transparent.
Qed.


Inductive param_env_partial_order (env env':Ω) (var: 𝓥) (f:σ) : Prop :=
| EsameInt n : 
    env var = Some (Def (VInt n))
    ->  env' var = Some (Def (VInt n))
    -> param_env_partial_order env env' var f
| EsameMpz (l:location) : 
    (* if the mpz is not a null pointer, we must have a corresponding adress *)
    env var = Some (Def (VMpz l)) ->
    env' var = Some (Def (VMpz (proj1_sig f l)))
    -> param_env_partial_order env env' var f
| ENullPtr : 
    (* if the mpz is a null pointer, it must stay null *)
    env var = Some (Def (VMpz None)) ->
    env' var = Some (Def (VMpz None))
    -> param_env_partial_order env env' var f
| EundefInt u : env var = Some (Undef (UInt u))
    -> (exists u', env' var = Some (Undef (UInt u'))) \/  (exists n, env' var = Some (Def (VInt n)))
    -> param_env_partial_order env env' var f
| EundefMpz u: env var = Some (Undef (UMpz u))
    -> (exists u, env' var = Some (Undef (UMpz u))) \/  (exists l, env' var = Some (Def (VMpz l)))
    -> param_env_partial_order env env' var f
| Enone : env var = None -> param_env_partial_order env env' var f
.

#[global] Hint Constructors param_env_partial_order : rac_hint.

Declare Scope env_scope.
Delimit Scope env_scope with env.
Declare Scope mem_scope.
Delimit Scope mem_scope with mem.
Declare Scope env_mem_scope.
Delimit Scope env_mem_scope with envmem.

Definition existify {A} (p: A -> Prop) : Prop := exists a, p a. 

Definition env_partial_order env env' := fun f => forall v, param_env_partial_order env env' v f.
Infix "⊑" := (fun e e' =>  existify (env_partial_order e e') ) : env_scope.


Definition param_mem_partial_order (mem mem':𝓜)  (l: location) (f:σ) := forall i, mem l = Some i ->  (mem' (proj1_sig f l)) = Some i.
Definition mem_partial_order env env' := fun f => forall l, param_mem_partial_order env env' l f.
Infix "⊑" := (fun e e' =>  existify (mem_partial_order e e') ) : mem_scope.


Definition env_mem_partial_order e e' f := 
    env_partial_order e.(env) e'.(env) f /\ mem_partial_order e.(mstate) e'.(mstate) f.
Infix "⊑" := (fun e e' =>  existify (env_mem_partial_order e e') ) : env_mem_scope.


Open Scope utils_scope.


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


(* Environnement Properties *)
From Coq Require Import Setoid.

Fact _refl_env_partial_order : reflexive Ω (fun e e' => env_partial_order e e' (exist _ _ id_bijective)).

Proof.
    intros [v l] var. destruct (v var) as [val |] eqn:res. induction val.
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
    forall v mpz, e v = Some (Def (VMpz mpz)) -> e' v = Some (induced sub (VMpz mpz)).
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


Import FunctionalEnv.

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
    env_mem_partial_order (Ω₀ <| env; vars ::= {{var' \ z}} |>) (Ω₀' <| env ; vars ::= {{var' \ induced sub z}} |>) sub
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



Definition _no_env_mpz_aliasing (ev : Ω) : Prop := 
    forall v v' l l', 
    v <> v' ->
    ev v = Some (Def (VMpz (Some l)))  ->
    ev v' = Some (Def (VMpz (Some l'))) -> 
    l <> l'.



Definition _type_of_value {T:Set} (ext_valty : 𝕍 -> @_c_type T) : option 𝕍 -> option (@_c_type T) := fun v => match v with
| Some (VInt _) | Some (UInt _) => Some C_Int
| Some t => Some (ext_valty t)
| None => None
end.

Definition _type_of_gmp :  𝕍 -> gmp_t := fun _ =>  T_Ext Mpz.


Definition type_of_value := _type_of_value _type_of_gmp.

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




(* environnement enrichers *)

Inductive add_z_var (e : Env) (τ:gmp_t) (v:id) (z:Z) : Env -> Prop :=
| typeInt irz : 
    (* fixme: section F is able to tell if z is in Uint and in any case transform it into a machine integer (how?) *)
    τ = C_Int ->
    add_z_var e τ v z (e <| env ; vars ::= {{v\z ⁱⁿᵗ irz : 𝕍}} |>)

| typeMpz l:
    τ  = Mpz ->
    (forall v', e v' <> Some (Def (VMpz (Some l))) )->
    add_z_var e τ v z 
    ( e 
    <| env ; vars ::= {{ v\l : 𝕍}} |>
    <| mstate ::= {{l\Defined z}} |> 
    )
.

Notation "env '+++' ( t , v , z )" := (add_z_var env t v z) (at level 99).

Definition 𝐴 : Type := Ensemble (gmp_t ⨉ id ⨉ Z).

Inductive add_z_vars (e : Env) : 𝐴 -> Env -> Prop := 
| add_z_vars_nil : add_z_vars e (Empty_set _) e

| add_z_vars_cons (vars:𝐴) t v z e': 
    e +++ (t,v,z) e' -> 
    add_z_vars e (Add _ vars (t,v,z)) e'
.

Fixpoint list_to_ensemble {X} (l:list X) : Ensemble X := match l with
| nil => Empty_set _
| List.cons hd tl => Add _ (list_to_ensemble tl) hd
end
.




(* 
(* the first mpz location is 0 and is then incremented by one *)
Inductive fresh_location (mem : 𝓜)  : location -> Prop :=  
    | First : 
        (forall l, mem l = None) -> 
        fresh_location mem O

    | New (max:location) : 
        max ∈ mem ->
        (forall l, mem l <> None -> max >= l)%nat ->
        fresh_location mem (max+1)%nat
. 


Fact fresh_location_deterministic : forall mem l l', 
    fresh_location mem l /\ fresh_location mem l' ->
    l = l'.
Proof.
    intros mem l l' [Hfl Hfl']. inversion Hfl ; inversion Hfl'. 
    - easy.
    - subst. destruct H1.  specialize H with max. congruence. 
    - subst. destruct H.  specialize H0 with max. congruence. 
    - clear Hfl Hfl'. subst. f_equal. inversion H. inversion H2. 
        specialize H3 with max. specialize H0 with max0.
        assert (mem max0 <> None) by congruence. assert (mem max <> None) by congruence.
        apply H0 in H5. apply H3 in H6. now apply Nat.le_antisymm. 
Qed.

Fact fresh_location_no_alias : forall mem l , 
    fresh_location mem l -> mem l = None.
Proof.
intros. destruct mem eqn:X.
    - inversion H.
        + specialize H0 with O. congruence.
        + exfalso. destruct H0. specialize H1 with (max + 1)%nat.
            assert (Hsome: mem (max + 1)%nat <> None) by congruence. apply H1 in Hsome. auto with zarith. 
    - easy.
Qed. *)