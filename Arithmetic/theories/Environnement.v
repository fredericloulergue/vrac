From RAC Require Import Utils.
From RAC.Languages Require Import Syntax.
From Coq Require Import ZArith.ZArith Strings.String.
From RecordUpdate Require Import RecordUpdate.


Record fenv {S T : Set} := {
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

Definition location := nat. 
#[global] Instance location_eq_dec : EqDec location := {eq_dec := Nat.eq_dec}.



#[global] Hint Resolve zeroinRange: rac_hint.
#[global] Hint Resolve oneinRange: rac_hint.
#[global] Hint Resolve suboneinRange: rac_hint.



Inductive value := 
    | VInt (n:Int.MI) :> value (* set of type int, a machine integer (may overflow) *)
    | VMpz (l:option location) (* memory location for values of type mpz, none is a null pointer *) 
.

Inductive undef := 
    | UInt (n:Int.MI) (* set of undefined values of type int *) 
    | UMpz (l:option location) (* set of undefined values of type mpz *) 
.

Inductive 𝕍 :=  Def (v : value) :> 𝕍 | Undef (uv : undef) :> 𝕍.

Inductive 𝔹 := BTrue | BFalse.

Inductive mpz_val := Defined (z:Z) :> mpz_val | Undefined (z:Z).

Definition 𝓜 := location ⇀ mpz_val. 
Definition Ωᵥ : Type := 𝓥 ⇀ 𝕍.
Definition Ωₗ : Type := 𝔏 ⇀ ℤ.


(* Coercion ir_z (x:Z) ir : 𝕍 := VInt (x ⁱⁿᵗ ir). *)
Coercion int_option_loc (l:nat) :=  Some l.
Coercion v_int (mi:Int.MI) : 𝕍 := Def (VInt mi). 
Coercion def_v_mpz (l:nat) : 𝕍 := Def (VMpz (Some l)). 
Coercion mpz_loc (l:location) : 𝕍 := VMpz (Some l).

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


Inductive param_env_partial_order (var: 𝓥) (env env':Ω) : Prop :=
| EsameInt n : 
    env var = Some (Def (VInt n))
    ->  env' var = Some (Def (VInt n))
    -> param_env_partial_order var env env'
| EsameMpz l : 
    env var = Some (Def (VMpz l))
    -> env' var = Some (Def (VMpz l))
    -> param_env_partial_order var env env'
| EundefInt n: env var = Some (Undef (UInt n))
    -> env' var = Some (Undef (UInt n)) \/  (exists n, env' var = Some (Def (VInt n)))
    -> param_env_partial_order var env env'
| EundefMpz n : env var = Some (Undef (UMpz n))
    -> env' var = Some (Undef (UMpz n)) \/  (exists n, env' var = Some (Def (VMpz n)))
    -> param_env_partial_order var env env'
| Enone : env var = None -> param_env_partial_order var env env'
.

#[global] Hint Constructors param_env_partial_order : rac_hint.

Declare Scope env_scope.
Delimit Scope env_scope with env.
Declare Scope mem_scope.
Delimit Scope mem_scope with mem.
Declare Scope env_mem_scope.
Delimit Scope env_mem_scope with envmem.

Definition env_partial_order env env' := forall v, param_env_partial_order v env env'.
Infix "⊑" := env_partial_order : env_scope.

Definition mems_partial_order (mem mem':𝓜) : Prop := forall l i, mem l = Some i ->  mem' l = Some i.
Infix "⊑" := mems_partial_order : mem_scope.


Infix "⊑" :=  ( fun e e' => (e.(env) ⊑ e'.(env))%env /\ (e.(mstate) ⊑ e'.(mstate))%mem) : env_mem_scope.


(* Environnement Properties *)
From Coq Require Import Setoid.
Fact refl_env_partial_order : reflexive Ω env_partial_order.
Proof.
    intros [v l] var. destruct (v var) as [val |] eqn:res. induction val.
    - destruct v0.
        * now apply EsameInt with n.
        * now apply EsameMpz with l0. 
    - destruct uv.
        * apply EundefInt with n; auto.
        * apply EundefMpz with l0; auto.
    - apply Enone ; auto.
Qed.


Fact trans_env_partial_order : transitive Ω env_partial_order.
Proof.
    intros  [v l] [v' l'] [v'' l'']  H1 H2 var. destruct H1 with var ; specialize (H2 var).
    * apply EsameInt with n. easy. inversion H2 ; congruence.
    * apply EsameMpz with l0 ; inversion H2; congruence.
    * apply EundefInt with n.
        + assumption.
        + inversion H2 ; destruct H0 ; eauto ; try congruence ; try (destruct H0 ; congruence).
    * apply EundefMpz with n. easy. inversion H2; destruct H0; try congruence || (destruct H0 ; congruence). right. now exists l0.
    * now apply Enone.
Qed.

Fact antisym_env_partial_order : forall env env',
    env_partial_order env' env /\ env_partial_order env env' -> forall v, env v = env' v.

Proof.
    intros env env' [H1 H2] v. specialize (H1 v). inversion H1 ; try congruence.
    - destruct H0 ; destruct H0;  destruct H2 with v; congruence.
    - destruct H0 ; destruct H0;  destruct H2 with v; congruence.
    - destruct H2 with v; destruct H0 ; try congruence  || (destruct H3; destruct H0 ; congruence).
Qed.



#[global] Add Relation Ω env_partial_order
    reflexivity proved by refl_env_partial_order
    transitivity proved by trans_env_partial_order as Renv.


Fact refl_mem_partial_order : reflexive 𝓜 mems_partial_order.
Proof.
    intros mem l. trivial. 
Qed.    

Fact trans_mem_partial_order : transitive 𝓜 mems_partial_order.
Proof.
    intros mem mem' mem'' H1 H2 l. destruct (mem l) eqn:L.
    - erewrite H2 ; eauto. 
    - discriminate.
Qed.


Fact antisym_mem_partial_order : forall mem mem', 
    mems_partial_order mem mem' /\ mems_partial_order mem' mem -> forall l, mem l = mem' l.
Proof.
    intros mem mem' [H1 H2] l. destruct (mem l) eqn:Heqn.
    - now apply H1 in Heqn.
    - destruct (mem' l) eqn:Heqn'. apply H2 in Heqn'.
        + congruence.
        + easy.
Qed.


#[global] Add Relation 𝓜 mems_partial_order
    reflexivity proved by refl_mem_partial_order 
    transitivity proved by trans_mem_partial_order as mem.

    
Fact refl_env_mem_partial_order : forall ev, (ev ⊑ ev)%envmem.
Proof.
    intros. split.
    - pose refl_env_partial_order as r. now unfold reflexive in r.
    - pose refl_mem_partial_order as r. now unfold reflexive in r.
Qed.

Fact eq_env_partial_order :  forall e e' v z, (e ⊑ e')%env ->  
    e v = Some (Def z) -> e' v = Some (Def z).
Proof.
    intros e e' v z Hrel He. destruct Hrel with v; congruence.
Qed.



Fact eq_int_env_mem_partial_order :  forall e e' v n, (e ⊑ e')%envmem -> 
    e v = Some (Def (VInt n)) -> e' v = Some (Def (VInt n)).
Proof.
    intros e e' v z [He Hm] Hsome. destruct (He v); congruence.  
Qed.

Open Scope utils_scope.

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



Definition _no_env_mpz_aliasing (ev : Ω) : Prop := 
    forall v v' l l', 
    v <> v' ->
    ev v = Some (Def (VMpz (Some l)))  ->
    ev v' = Some (Def (VMpz (Some l'))) -> 
    l <> l'.



Definition type_of_value : option 𝕍 -> option 𝔗 := fun v => match v with
| Some (VInt _) | Some (UInt _)  => Some C_Int
| Some (VMpz _) | Some (UMpz _) => Some (T_Ext Mpz)
| None => None
end.


Fact type_of_value_env : forall (env:Ω) (var:𝓥), type_of_value (env var) <> None -> env var <> None.
Proof.
    intros env var Hty. now destruct (env var) as [v|].
Qed.


Fact env_same_ty : forall  (Ω Ω' : Ω) v t, (Ω ⊑ Ω')%env -> t <> None -> type_of_value (Ω v) = t -> type_of_value (Ω' v) = t.
Proof.
    intros. 
    match goal with | IncRel : (_ ⊑ _)%env |- _ =>  destruct IncRel with v ; subst end ;
    match goal with 
    | L : apply_env ?Ω v = _,  R : apply_env ?Ω' v = _  |- _ => now rewrite L,R 
    | L : apply_env ?Ω v = _,  R : apply_env ?Ω' v = _ \/ _ |- _ => destruct R as [SomeUInt | [ x Some_n ]]; [now rewrite L,SomeUInt | now rewrite L,Some_n] 
    | L : _ = None,  Contra : _ <> None |- _ =>  now rewrite L in Contra
    end.
Qed.




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


(**** oracle & co ****)

Record 𝐼 := mkInterval {min : Z; max : Z}. (* interval *)

Definition 𝓘 := ℨ -> (𝔏 ⇀ 𝐼) -> 𝐼. (* oracle *)

Definition ϴ :=  𝐼 -> 𝔗.

Definition Γᵢ := 𝔏 ⇀ 𝐼. (* typing env mapping logic binders to intervals *)
Definition Γᵥ := 𝔏 ⇀ 𝓥 ⨉ 𝐼. (* environment for bindings :  variable and interval infered from it *)
Definition Γ := Γᵥ ⨉ Γᵢ.

(* See 5.1. (𝔏 ⇀ 𝐼) is the interval infered for each function arguments but how to make it decidable ? *)
Axiom eq_dec_bindings : forall (e1 e2 : (𝔏 ⨉ (𝔏 ⇀ 𝐼))), {e1 = e2} + {e1 <> e2}. 

#[global] Instance eqdec_bindings : EqDec (𝔏 ⨉ (𝔏 ⇀ 𝐼)) := {
    eq_dec := eq_dec_bindings
}.


Definition ψ := (𝔏 ⨉ (𝔏 ⇀ 𝐼)) ⇀ 𝓥 . (* global definitions env *)
Notation "'Γ' '(' x ')' " := (Γᵥ x, Γᵢ x).
Definition 𝚪 (oracle: 𝓘) (o:ϴ) := fun (t:ℨ) (τᵢ: Γᵢ) =>  o (oracle t τᵢ) : 𝔗. (* Θ ◦ oracle. *)
Record type_inf := { oracle : 𝓘 ; t_env : Γᵢ ; i_op : ϴ }.
