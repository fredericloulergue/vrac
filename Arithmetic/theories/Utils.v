From Coq Require Import Strings.String ZArith.ZArith Setoids.Setoid Eqdep_dec Logic.FinFun MSets MSetList. 
From Equations Require Import Equations.
From MMaps Require Import MMaps.
From RAC Require Export Prelude.



Declare Scope utils_scope.
Delimit Scope utils_scope with utils.

Create HintDb rac_hint.
#[local] Open Scope utils_scope.



Fixpoint fold_left2 {Acc A B : Type} (f : Acc -> A -> B -> Acc) (acc:Acc) (l1 : A*) (l2 : B*) : Acc := 
    match l1,l2 with
    | nil,nil => acc
    | cons b1 t1,cons b2 t2 => fold_left2 f (f acc b1 b2) t1 t2
    | _,_ => acc (* both lists must have the same length,
    otherwise computation will be interrupted when one of the list is empty but not the other *)
    end
.

Fixpoint fold_left_in {Acc A : Type} (l : list A) (f : Acc -> {x:A| List.In x l}  -> Acc)   (acc_base:Acc) {struct l} : Acc.
Proof.
    refine (match l with nil => fun _ => acc_base | cons h t => fun f => _ end f).
    refine (fold_left_in _ _ t _ (f acc_base (exist _ h _))).
    - refine (fun acc_new x => f acc_new (exist _ (proj1_sig x) _)). destruct x. simpl. now right.
    - now constructor.
Defined.


Fixpoint fold_left2_in {Acc A B: Type} (l1: list A) (l2 : list B) (f : Acc -> {x:A| List.In x l1}  -> {x:B| List.In x l2} -> Acc)  (acc_base:Acc) {struct l1} : Acc.
Proof.
    refine (match l1,l2 with cons h1 t1,cons h2 t2 => fun f => _  | _,_ => fun _ => acc_base end f).
    refine (fold_left2_in _ _ _ t1 t2 _ (f acc_base (exist _ h1 _) (exist _ h2 _))).
    - refine (fun acc_new x1 x2 => f acc_new (exist _ (proj1_sig x1) _) (exist _ (proj1_sig x2) _)).
        + destruct x1; now right.
        + destruct x2; now right.
    - now constructor.
    - now constructor.
Defined.



Module FunctionalEnv. (* used across the formalization to bind variables to values *)

Definition partial_function (X Y : Type) : Type := X -> option Y.
Infix "⇀" := partial_function : type_scope.
Definition empty_p {X Y:Type} := fun (_:X) => (None: option Y).
Notation "⊥" := empty_p : type_scope.


Class EqDecC X := {eq_dec : EqDec X }.


#[global] Instance z_eq_dec : EqDecC Z := {eq_dec := Z.eq_dec}.
#[global] Instance eqdec_v : EqDecC 𝓥 := {eq_dec := string_dec}.
#[global] Instance eqdec_l : EqDecC 𝔏 := {eq_dec := string_dec}.

Definition p_map_front {X Y : Type} `{EqDecC X}  (f: X -> option Y) (xy:X ⨉ Y)   : X -> option Y :=
    fun i => if eq_dec (fst xy) i then Some (snd xy) else f i.

Definition p_map_back {X Y : Type} `{EqDecC X}  (xy:X ⨉ Y) (f: X -> option Y)  : X -> option Y :=
    p_map_front f xy.

#[global] Hint Unfold p_map_back : rac_hint.

Notation "x '\' y" := (x,y) (in custom pmap at level 0, x constr, y constr) : utils_scope.
Notation "f { xy , .. , xy' }" :=  (p_map_front .. (p_map_front f xy') .. xy ) : utils_scope.
Notation "'{{' xy , .. , xy' '}}'" := (fun f => p_map_back xy' .. (p_map_back xy f) .. ) : utils_scope. (* fixme: make same as the other*)



Definition p_map_addall_back {X Y: Type} `{EqDecC X} (lx:list X) (ly : list Y) env :=
    fold_left2 (fun f x y => f {x \ y}) env lx ly
.

Definition p_map_addall_front {X Y: Type} `{EqDecC X} env (lx:list X) (ly : list Y) :=
    p_map_addall_back lx ly env
.


   (* some facts *)

Fact p_map_single_back_front_eq {X Y : Type} `{EqDecC X} : 
    forall f x (y:Y) z , f{x\y} z = {{x\y}}f z.
Proof. auto. Qed.
#[global] Hint Unfold p_map_addall_back : rac_hint.


Fact p_map_not_same {X T : Type } `{EqDecC X}: forall f (x x' : X) (v : T), x <> x' -> f{x'\v} x = f x.
Proof.
    intros. unfold p_map_front. simpl. destruct eq_dec.
    - now destruct H0. 
    - easy.
Qed.
#[global] Hint Resolve p_map_not_same : rac_hint.


Corollary p_map_not_same_eq {X T : Type } `{EqDecC X}: forall f (x x' : X) (v : T) (res : option T), x <> x' -> f{x'\v} x = res <-> f x = res.
Proof.
    split. 
    - intro H1. now rewrite p_map_not_same in H1.
    - intro H1.  erewrite <- p_map_not_same in H1.
        + apply H1.
        + assumption.
Qed.

#[global] Hint Resolve p_map_not_same_eq : rac_hint.

Fact p_map_same {X T : Type } `{EqDecC X}: forall f (x : X) (v : T), f{x\v} x = Some v.
Proof.
    intros. unfold p_map_front. simpl. now destruct eq_dec.
Qed.

#[global] Hint Resolve p_map_same : rac_hint.

Fact p_map_apply {X T T' : Type } `{EqDecC X} : forall env (x :X)  (v : T) (f : option T -> T'),  f (env{x\v} x)  = f (Some v).
Proof.
    intros env x v f. f_equal. apply p_map_same.
Qed.

Fact p_map_domain {X Y : Type } `{EqDecC X} (env : X -> option Y) (z : X) :
    forall x x' y z, env{x\y} x' = Some z -> x' = x \/ env x' = Some z.
Proof.
    intros. destruct (eq_dec x' x).
    + now left.
    +  rewrite p_map_not_same in H0 ; auto.
Qed.


Module Domain.
    Declare Scope domain_scope.
    Delimit Scope domain_scope with dom_.

    #[local] Open Scope domain_scope.

    Definition in_domain { X Y : Type} (f: X ⇀ Y) (x:X) := exists y, f x = Some y.
    #[global] Hint Unfold in_domain : rac_hint.

    Definition not_in_domain { X Y : Type} (f: X ⇀ Y) (x:X) := f x = None.

    Definition in_codomain { X Y : Type} (f: X ⇀ Y) (y:Y) := exists x, f x = Some y.
    Definition not_in_codomain { X Y : Type} (f: X ⇀ Y) (y:Y) := forall x, f x <> Some y.

    Definition domain_incl_prop { X : Type} (dom1: X -> Prop) (dom2: X -> Prop) := forall (x:X), (dom1 x -> dom2 x).
    #[global] Hint Unfold domain_incl_prop : rac_hint.

    Definition eq_domain_prop { X : Type} (dom1: X -> Prop) (dom2: X -> Prop) := (domain_incl_prop dom1 dom2) /\ (domain_incl_prop dom2 dom1).
    #[global] Hint Unfold eq_domain_prop : rac_hint.


    Definition sub_domain_prop { X : Type} (dom1: X -> Prop) (dom2: X -> Prop) (x:X) := dom1 x /\ ~ dom2 x.
    #[global] Hint Unfold sub_domain_prop : rac_hint.

    Definition add_domain { X : Type} (dom1: X -> Prop) (dom2: X -> Prop) (x:X) := dom1 x \/ dom2 x.
    #[global] Hint Unfold add_domain : rac_hint.


    Infix "+" := add_domain : domain_scope.
    Infix "-" := sub_domain_prop : domain_scope.
    Infix "=" := eq_domain_prop : domain_scope.
    Infix "⊂" := domain_incl_prop (at level 99) : domain_scope.
    Notation "x ∉ E" := (not_in_domain E x) (at level 99) : domain_scope.
    Notation "'dom' f" := (in_domain f) : domain_scope.
    Notation "x ∈ E" := (in_domain E x) (at level 99) : domain_scope.


    Fact not_in_equiv { X Y : Type} (f: X ⇀ Y) (x:X) : (x ∉ f) <-> ~(x ∈ f).
    Proof. 
        split; intros H.
        -intros contra. inversion H.  inversion contra. now rewrite H0 in H1.
        -destruct (f x) eqn:Fx.
            +  exfalso.  apply H. now exists y.
            + assumption.
    Qed. 

    Fact in_domain_dec { X Y : Type} (f: X ⇀ Y) (x:X) : Decidable.decidable (x ∈ f). 
    Proof. 
        destruct (f x) eqn:Fx.
        -  left. now exists y.
        - right.  intros contra. destruct contra. now rewrite H in Fx.
    Qed. 

    Fact not_in_sub_domain_prop { X : Type} (x: X) (dom1: X -> Prop) (dom2: X -> Prop): 
        Decidable.decidable (dom1 x) -> 
        Decidable.decidable (dom2 x) -> 
        ~ ((dom1 - dom2) x) -> dom2 x \/ ~ dom1 x.
    Proof.
        intros Hdec1 Hdec2 H. autounfold with rac_hint in H. apply Decidable.not_and in H;[|trivial]. destruct H.
        - now right.
        - apply Decidable.not_not in H;[|trivial]. now left.
    Qed.


    Fact not_in_diff {X Y : Type} : forall (x y:X) (f : (X ⇀ Y)), f y <> None -> x ∉ f -> y <> x.
    Proof.
        intros x y f H H0 Hnot. subst. destruct (f x) eqn:F.
        * destruct H0. auto.
        * contradiction.
    Qed.

    Fact d_sub_d_empty {X Y : Type} : forall (f : (X ⇀ Y)),
        ~ exists n, (dom f - dom f) n.
    Proof.
        intros f contra. inversion contra. inversion H. destruct H1. assumption.
    Qed.


End Domain.


End FunctionalEnv.

Module MMapsEnv(K: OrderedType).
    Import MMaps.   
    
    Module M  := OrdList.Make(K).
    Include M.

   (* extra operations *)
    Definition add_all {V:Type} (lk:list K.t) (lv: list V) : t V -> t V :=  
            List.fold_left (fun env kv => add (fst kv) (snd kv) env) (List.combine lk lv)
    .

    Include Facts.OrdProperties(K)(M).

    Module Decidable(V:OrderedType) := Facts.OrderedMaps(K)(V)(M).

    Notation "⊥" := M.empty : type_scope.
End MMapsEnv.

Module StringMap := MMapsEnv(String_as_OT).

Module MSetEnv(T: OrderedType).    
    Module S := MSetList.Make(T).
    Include S.
    Module D := MSetDecide.Decide(S).


   (* extra operations *)
    Definition union_list (lv: list t) : t -> t :=  
        List.fold_left (fun s x => union x s) lv
    .
    

    Notation "⊥" := S.empty : type_scope.
End MSetEnv.

Module StringSet := MSetEnv(String_as_OT).


(* modified from http://poleiro.info/posts/2013-03-31-reading-and-writing-numbers-in-coq.html *)
Definition string_of_nat (n : nat) : string :=
    let fix aux (time n : nat) (acc : string) : string :=
    let acc' := String (Ascii.ascii_of_nat ((n mod 10) + 48)) acc in
    match time with
    | 0 => acc'
    | S time' =>
        match n / 10 with
        | 0 => acc'
        | n' => aux time' n' acc'
        end
    end in
    aux n n EmptyString.




Module Type Bounds.
    Parameter m_int : Z.
    Parameter M_int : Z.
End Bounds.


(* simplified from compcert.lib.Integers *)
Module MachineInteger(B:Bounds).
    #[local] Open Scope bool_scope.
    #[local] Open Scope Z_scope.

    Include B.
    
    Definition inRange n : Prop := (B.m_int <? n) && (n <? B.M_int) = true.

    Definition MI := sig inRange.

    Lemma mi_eq : forall (x y : MI), x = y <-> proj1_sig x = proj1_sig y.
    Proof.
        intros x y. split ; intros EQ.
        - destruct x,y. simpl. now inversion EQ.
        - destruct x,y. simpl in EQ. subst. f_equal. unfold inRange in *. now pose proof (Eqdep_dec.UIP_dec Bool.bool_dec).
    Qed.

    Definition to_mi x (H: inRange x) : MI := exist inRange x H.

    Definition of_mi (mi: MI) : Z := proj1_sig mi.


    Fact x_of_mi_to_mi_x : forall x irx, (to_mi (of_mi x) irx) = x.
    Proof.
        intros. unfold to_mi, of_mi. destruct x. simpl. f_equal. unfold inRange in *. 
        simpl in *.  apply (Eqdep_dec.UIP_dec Bool.bool_dec).
    Qed.
End MachineInteger.


Module Type Monad.

    Parameter t : Type -> Type.

    Parameter ret : forall a, a -> t a.

    Parameter bind : forall a b (m: t a) (f: a -> t b), t b.

End Monad.


Module MonadNotations(M : Monad).
    Import M.
    Notation "x <- f ;; c" := (bind _ _ f (fun x => c)) (f at next level, at level 61, right associativity) .
    Notation "x <- f ;;; c" := (bind _ _ f (fun x => ret _ c)) (f at next level, at level 61, right associativity) .
    Notation "f ;; c" := (bind _ _ f (fun _ => c)) ( at level 61, right associativity).
    Notation "f ;;; c" := (bind _ _ f (fun _ => ret _ c)) ( at level 61, right associativity).
End MonadNotations.


Module MonadOps(M : Monad).
    Equations map {A B: Type} (f: A -> M.t B) (l: list A) : M.t (list B) := 
    | _,nil => M.ret _ nil
    | _,hd::tl => M.bind _ _ (f hd) (fun x => 
        M.bind _ _ (map f tl) (fun l =>
            M.ret _ (x::l)
        )
    )
    .


    Equations fold {A B : Type} (f: B -> A -> M.t B) (l: list A) (e: B) : M.t B :=
    | _,nil,_ => M.ret _ e
    | _,hd::tl,_ => M.bind _ _ (fold f tl e) (fun res => f res hd)
    .
End MonadOps.


Module TranslationMonad <: Monad . (* option + state *)
    Definition t {T : Type} : Type :=  nat -> @option T  ⨉ nat.


    Definition ret {A : Type} (a : A) : t (T:=A) := fun c => (Some a, c).

    Definition bind {A B : Type} (m : t (T:=A)) (f : A -> t (T:=B)) : t (T:=B) :=
        fun c => 
            let (a, c') := m c in match a with
            | Some a => f a c'
            | None => (None,c')
    end
    .

    Definition tick : t := fun c => (Some tt, S c).
    Definition getTick : t := fun c => (Some c, c).
    Definition fresh : t := bind getTick (fun n : nat => bind tick (fun _ : unit => ret n)).
    Definition exec {A:Type} (m: t (T:=A)) : option A := fst (m 0).
    Definition error {A : Type} : t (T:=A) := fun c => (None, c).

End TranslationMonad.


Module TranslationMonadNoError <: Monad . (*  state *)
    Definition t {T : Type} : Type :=  nat -> T  ⨉ nat.


    Definition ret {A : Type} (a : A) : t (T:=A) := fun c =>  (a, c).

    Definition bind {A B : Type} (m : t (T:=A)) (f : A -> t (T:=B)) : t (T:=B) :=
        fun c =>  let (a, c') := m c in f a c'
    .

    Definition tick : t := fun c => (tt, S c).
    Definition getTick : t := fun c => (c, c).
    Definition fresh : t := bind getTick (fun n : nat => bind tick (fun _ : unit => ret n)).
    Definition exec {A:Type} (m: t (T:=A)) : A := fst (m 0).
End TranslationMonadNoError.


Close Scope utils_scope.