From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax Semantics Lemmas.
From Coq Require Import  ZArith.ZArith BinaryString.
From RecordUpdate Require Import RecordUpdate.


Open Scope mini_c_scope.
Open Scope Z_scope.
Open Scope mini_gmp_scope.



Definition mpz_ASSGN v (e: gmp_exp ) : gmp_statement := match ty e with
    | T_Ext Mpz => match e with
                    | C_Id x _ => <( set_z(v,x) )>
                    | _ => Skip (* cannot happen *)
                    end
    | C_Int => <( set_i(v,(gmp_exp_to_c_exp e)) )> : gmp_statement
    | _ => Skip (* cannot happen  *)
end.

Definition int_ASSGN v (e: gmp_exp) : gmp_statement := match ty e with
    | T_Ext Mpz => match e with
                    | C_Id x _ => <( v = get_int(x) )>
                    | _ => Skip (* cannot happen *)
                    end
    
    | C_Int =>  <{ v = e }>
    | _ => Skip
end.

Definition τ_ASSGN (t:gmp_t) := match t with
    | T_Ext Mpz => mpz_ASSGN
    | C_Int => int_ASSGN
    | _ => int_ASSGN (* cannot happen  *)
    end.

Definition Z_ASSGN (τz:gmp_t) v (z:Z) : gmp_statement := match τz with
    | C_Int => <{ v = z }>
    | T_Ext Mpz => <( set_s(v, (BinaryString.of_Z z) ) )>
    | _ => Skip (* cannot happen  *)
end.




Definition CMP c (e₁ e₂ : gmp_exp) v₁ v₂ : gmp_statement := match ty e₁, ty e₂ with
    |  C_Int,C_Int => 
        <{ 
            if (e₁ < e₂) c = 0-1
            else if (e₁ > e₂) c = 1
            else c = 0
        }>
    | _,_ => 
        let a1 := mpz_ASSGN v₁ e₁ in 
        let a2 := mpz_ASSGN v₂ e₂ in
        let cmp : gmp_statement := <( c = cmp(v₁,v₂) )> in
        <{ a1 ; a2 ; cmp }>
end
.


Definition binop_ASSGN (fsl_op:fsl_binop_int) (v:𝓥 ⨉ gmp_t) e₁ e₂ (r:id) v₁ v₂ : gmp_statement := 
    let (c,τ) := v in
    match τ,(ty e₁),(ty e₂) with
    | C_Int,C_Int,C_Int =>  let res := BinOpInt e₁ (□ fsl_op) e₂ in <{ c = res }>
    | _,_,_ => 
        let s1 :=  mpz_ASSGN v₁ e₁ in
        let s2 :=  mpz_ASSGN v₂ e₂ in
        let s3 : gmp_statement := match τ with
            | C_Int => 
                let op : gmp_statement  := <( (fsl_to_gmp_op fsl_op r v₁ v₂) )> in
                let r : gmp_exp := (C_Id r (T_Ext Mpz)) in 
                <{op  ; <( (int_ASSGN c r) )> }>                    
            | T_Ext Mpz => fsl_to_gmp_op fsl_op c v₁ v₂
            | _ => Skip
            end
        in <{s1;s2;s3}>

    end
    .


Inductive get_int_exp (ev:Env) (e:gmp_exp): Z -> Prop :=
| M_Int x : 
    ty e = C_Int -> 
    (ev |= gmp_exp_to_c_exp e => (VInt x))%csem ->
    ev |= e ⇝ x ̇
| M_Mpz l z : 
    ty e = Mpz ->
    ev (gmp_ty_mpz_to_var e) = Some (Def (VMpz (Some l))) ->
    ev.(mstate) l = Some (Defined z) ->
    ev |= e ⇝ z
where "ev '|=' e ⇝ z" := (get_int_exp ev e z).

#[global] Hint Constructors get_int_exp : rac_hint.


(* helper lemmas *)

Lemma same_eval_macro :  forall (ev : Env) v l e z z', 
    _no_env_mpz_aliasing ev ->
    ~ List.In v (exp_vars e) ->
    ev v = Some (Def (VMpz (Some l))) ->
    ev |= e ⇝ z ->
    ev <| mstate ::= {{l \ Defined z'}} |> |= e ⇝ z.

Proof.
    intros. inversion H2.
   *  subst. constructor 1;auto. apply untouched_var_same_eval_exp with v ; auto.
        - easy.
        - now rewrite gmp_exp_c_exp_same_exp_vars. 

    * subst. pose proof (mpz_exp_is_var e). apply H6 in H3 as [var].  subst. simpl in *.
    apply M_Mpz with l0; subst.
    + now simpl.
    + apply Decidable.not_or_iff in H0 as [Hdiff _].
        destruct (eq_dec l l0).
        ++ subst. destruct H with v var l0 l0 ; congruence.
        ++ now simpl.
    + apply Decidable.not_or_iff in H0 as [Hdiff _].
        destruct (eq_dec l l0).
        ++ subst. destruct H with v var l0 l0 ; congruence.
        ++  simpl. apply p_map_not_same_eq;auto.
Qed.


Lemma semantics_of_the_mpz_assgn_macro :
    forall f e z (ev : Env) v (y:location),
    ev |= e ⇝ z ->
    ev v = Some (Def (VMpz y)) ->
    gmp_stmt_sem f ev (mpz_ASSGN v e) (ev <| mstate ::= {{y\Defined z}} |>)
.
(* implies either set_i or set_z, everything else is not possible *)
Proof.
    intros. 
    unfold mpz_ASSGN. destruct (ty e) eqn:TY.  
    - inversion H ; constructor. 
        * now apply S_set_i.
        * now rewrite H1 in TY. 
    - inversion H.
        * now rewrite H1 in TY.
        * now rewrite H1 in TY. 
    -  inversion H.
        * now rewrite H1 in TY.
        * rewrite TY in H1. subst. inversion H1. destruct e; simpl in TY ; subst; try discriminate.
            + constructor.  apply S_set_z with l;auto. 
            +  destruct (ty e1); try congruence. destruct (ty e2); congruence.
            +  destruct (ty e1); try congruence. destruct (ty e2); congruence.
Qed.

Lemma semantics_of_the_int_assgn_macro :
    forall f e z (ir: Int.inRange z) (ev:Env) v,
    is_comp_var v = false ->
    ev |= e ⇝ z ->
    type_of_value (ev v) = Some C_Int ->
    gmp_stmt_sem f ev (int_ASSGN v e) (ev <| env ; vars ::= {{v\VInt (z ⁱⁿᵗ ir) : 𝕍}} |>)
.
(* implies either set_i or S_Assign, everything else is not possible *)
Proof with eauto with rac_hint.
    intros f e z ir ev v Hnotcomp H H0. 
    unfold int_ASSGN.
    destruct (ty e)  eqn:EqTY.
    -  constructor... inversion H ; subst.
        + apply ty_int_gmp_c_exp_equiv ;[assumption|]. now rewrite Int.x_of_mi_to_mi_x.
        +  now rewrite H1 in EqTY.
    - inversion H.
        * now rewrite H1 in EqTY.
        * now rewrite H1 in EqTY. 
    - inversion H. subst.
        + now rewrite H1 in EqTY.
        + subst. destruct t. 
            * now rewrite EqTY in H1.
            * destruct e; simpl in EqTY ;try discriminate.
                2,3:  destruct (ty e1); try congruence; destruct (ty e2); congruence.
                constructor. subst. simpl in H2. apply S_get_int with l; auto.
Qed.

Lemma semantics_of_the_Z_assgn_macro_tint :
    forall f z (ir: Int.inRange z) (ev:Env) v,
    is_comp_var v = false ->
    type_of_value (ev v) = Some C_Int ->
    gmp_stmt_sem f ev (Z_ASSGN C_Int v z) (ev <| env ; vars ::= {{v\VInt (z ⁱⁿᵗ ir) : 𝕍}} |>)
.
Proof.
    intros.  constructor ; auto with rac_hint.
Qed.

Lemma semantics_of_the_Z_assgn_macro_tmpz :
    forall f y (z:ℤ) (ev:Env) v,
    ev v = Some (Def (VMpz (Some y))) ->
    gmp_stmt_sem f ev (Z_ASSGN Mpz v z) (ev <| mstate ::= {{y\Defined z}} |>)
.
Proof with auto using BinaryString.Z_of_of_Z.
    intros. simpl. constructor. apply S_set_s...
Qed.


Lemma semantics_of_the_cmp_macro :
    forall f (ev:Env) c e1 e2 v1 v2 z1 z2 a,
    _no_env_mpz_aliasing ev ->
    is_comp_var c = false ->
    type_of_value (ev c) = Some C_Int ->
    ev |= e1 ⇝ z1 ->
    ev |= e2 ⇝ z2 ->

    (
        (Def a = VInt sub_one <-> Z.lt z1 z2 ) /\
        (Def a = VInt zero <-> z1 = z2) /\
        (Def a = VInt one <-> Z.gt z1 z2)
    ) -> 

    (* v1 and v2 must be bound to a mpz location (implied by mpz_assign ) *)
    forall (l1 l2 : location),
    ev v1 = Some (Def (VMpz l1)) /\  ev v2 = Some (Def (VMpz l2))->
    
    ~ List.In v1 ((exp_vars e2)) /\  l1 <> l2   -> (* not in paper proof *)

    exists M, (
        forall v (n:location), 
        ev v = Some (Def (VMpz n)) ->
        ev v <> ev v1 /\ ev v <> ev v2  -> 
        ev.(mstate) n = M n
    ) -> 
    
    gmp_stmt_sem f ev (CMP c e1 e2 v1 v2) (ev <| env ; vars ::= {{c\Def a}} |> <| mstate := M |>) 
.

Proof with try easy ; auto with rac_hint ; unshelve eauto using Z.ltb_irrefl,Z.gtb_ltb,Z.ltb_lt with rac_hint; auto with rac_hint.
    intros f ev c e1 e2 v1 v2 z1 z2 a Hnoalias Hnocom H H0 H1 (inf & eq & sup) l1 l2 (Hv1 & Hv2) (Hv1NotIne2 & Hdiffl1l2).
    
    assert (NotInt : 
        exists M, (
            forall v (n:location), 
            ev v = Some (Def (VMpz n)) ->
            ev v <> ev v1 /\ ev v <> ev v2  -> 
            ev.(mstate) n = M n
        ) -> 
        let cmp := S_Ext <(c = cmp (v1, v2) )> in
        gmp_stmt_sem f ev <{(mpz_ASSGN v1 e1); (mpz_ASSGN v2 e2); cmp}> 
        (ev <| env ; vars ::= {{c \Def a}} |> <| mstate := M |>)
    ). {
        exists ev.(mstate){l2 \Defined z2, l1 \Defined  z1}. intros Hvdiff. 
        apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |>).
        - apply semantics_of_the_mpz_assgn_macro...
        - eapply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |> <| mstate ::= {{l2\Defined z2}} |> ).
            + apply semantics_of_the_mpz_assgn_macro... inversion H1 ; subst. 
                * constructor... eapply untouched_var_same_eval_exp...
                    now rewrite gmp_exp_c_exp_same_exp_vars.
                *  econstructor... 
                    assert (Hdiffll1: l <> l1) by admit. apply p_map_not_same_eq... 

            + constructor. replace 
                (_ <| env; vars ::= _ |><| mstate := _ |>)
                with (ev <| mstate := ev.(mstate) {l2 \Defined z2, l1 \Defined z1} |><| env; vars ::= {{c \Def a}} |> ) by reflexivity.
                apply S_cmp with (lx:=l1) (ly:=l2) (zx:=z1) (zy:=z2) ; simpl... apply p_map_not_same_eq...
    }
    unfold CMP. destruct (ty e1) eqn:T1, (ty e2) eqn:T2 ; try apply NotInt ; clear NotInt.
    
    (* both ty(e1) = int and ty(e2) = int *)
    inversion H0 ; inversion H1 ; idtac; try  match goal with 
        | mpz : ty ?e = (gmp_t_ext Mpz), int : ty ?e = C_Int  |- _ => now rewrite mpz in int end.


    exists ev.(mstate). intros Hvdiff. clear Hvdiff (* not needed *). destruct (Z.lt_trichotomy z1 z2) as [inf' | [ eq' | sup']].
        
    (* z1 < z2 *)
    * assert (cmp := inf'). apply <- inf in inf'. clear eq inf sup. subst. 
        destruct x,x0. simpl in *.  apply S_IfTrue with one.
        + split ; [| easy]. apply C_E_BinOpTrue with x x0 i i0. 
            ++ now apply ty_int_gmp_c_exp_equiv.
            ++ now apply ty_int_gmp_c_exp_equiv.
            ++ apply Z.ltb_lt. apply cmp.
        + inversion inf'. constructor...  apply (C_E_BinOpInt ev 0 1 0 1) with zeroinRange oneinRange...

    (* z1 = z2 *)
    * assert (cmp := eq'). rewrite <- eq in eq'. clear eq inf sup. subst.
        destruct x,x0. apply Int.mi_eq in cmp. injection cmp as cmp. inversion eq'. subst. simpl in *. constructor.
        + econstructor... apply ty_int_gmp_c_exp_equiv... apply ty_int_gmp_c_exp_equiv...
        + constructor. econstructor...  apply ty_int_gmp_c_exp_equiv... apply ty_int_gmp_c_exp_equiv... constructor...


    (* z1 > z2 *)
    * assert (cmp := sup').  apply Z.lt_gt in sup'. apply <- sup in sup'.  clear inf eq sup. subst.
        destruct x, x0. subst. constructor ; simpl in *.
        + apply C_E_BinOpFalse with x x0 i i0.
            ++ apply ty_int_gmp_c_exp_equiv...
            ++ apply ty_int_gmp_c_exp_equiv...
            ++ apply Z.ltb_ge. auto with zarith. 
        + inversion sup'. subst. apply S_IfTrue with one.
            ++  subst. split; [|easy]. apply C_E_BinOpTrue with x x0 i i0.
                +++ apply ty_int_gmp_c_exp_equiv...
                +++ apply ty_int_gmp_c_exp_equiv...
                +++ now apply Z.gtb_lt.
            ++  constructor...
Admitted.




Lemma semantics_of_the_binop_macro_int :
    forall f (ev:Env) (op:fsl_binop_int) c r e1 e2 v1 v2 z1 z2 (ir: Int.inRange (⋄ op z1 z2) ) l1 l2 lr,
    _no_env_mpz_aliasing ev ->
    is_comp_var c = false ->
    type_of_value (ev c) = Some C_Int ->
    ev |= e1 ⇝ z1 ->
    ev |= e2 ⇝ z2 ->
    let zr := ⋄ op z1 z2 in

    ev v1 = Some (Def (VMpz (Some l1))) /\  
    ev v2 = Some (Def (VMpz (Some l2))) /\
    ev r = Some (Def (VMpz (Some lr))) ->
    exists M, (forall v n, ev v = Some (Def (VMpz (Some n))) ->
    ev v1 <> ev v /\ ev v2 <> ev v  -> ev.(mstate) n = M n) -> 

    ~ List.In v1 ((exp_vars e2)) /\  l1 <> l2   -> (* not in paper proof *)

    gmp_stmt_sem f ev (binop_ASSGN op (c,C_Int) e1 e2 r v1 v2) (ev <| env ; vars ::= fun e => e{c\VInt (zr ⁱⁿᵗ ir) : 𝕍} |> <| mstate := M |>)
    .

Proof with eauto with rac_hint.
    intros f ev op c r e1 e2 v1 v2 z1 z2 ir l1 l2 lr Hnoalias Hnocomp H H0 H1 zr H2. destruct H2 as (v1l & v2l & rl).  
    assert (NotInt : 
        exists M,
        (forall (v : 𝓥) (n : location),
        ev v = Some (Def (VMpz n)) ->
        ev v1 <> ev v /\ ev v2 <> ev v ->
        ev.(mstate) n = M n) ->
        ~ List.In v1 ((exp_vars e2)) /\  l1 <> l2   -> (* not in paper proof *)
        gmp_stmt_sem f ev <{
            (mpz_ASSGN v1 e1);
            (mpz_ASSGN v2 e2);
            (S_Ext (fsl_to_gmp_op op r v1 v2));
            (int_ASSGN c (C_Id r Mpz))
        }> (ev <| env ; vars ::= fun e => e{c \VInt (zr ⁱⁿᵗ ir) : 𝕍} |> <| mstate := M |> )
    ). {
    exists ev.(mstate){lr\Defined zr,l2\Defined z2,l1\Defined z1}. intros H2 [H3 H4].  apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |>). 
    - apply semantics_of_the_mpz_assgn_macro...
    - apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |> <| mstate ::= {{l2\Defined z2}} |> ). 
        + apply semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
        + apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |> <| mstate ::= {{l2\Defined z2}}  |> <| mstate ::= {{lr\Defined zr}} |>).
            * constructor. apply S_op with l1 l2...  
                ** simpl.  apply p_map_not_same_eq...
                ** simpl. apply p_map_same. 
            * replace (ev <| env; vars ::= _ |> <| mstate :=  _ |>)
            with (ev <| mstate := ev.(mstate) {lr \Defined zr, l2 \Defined z2, l1 \ Defined z1} |> 
                    <| env; vars ::= {{c \Def (VInt ((zr ⁱⁿᵗ) ir))}} |>
            ) by reflexivity.
            apply semantics_of_the_int_assgn_macro...  apply M_Mpz with lr ; simpl...
    }
    
    unfold binop_ASSGN. destruct (ty e1) eqn:T1, (ty e2) eqn:T2 ; try apply NotInt. clear NotInt.
    exists ev.(mstate). intros. inversion H0 ; inversion H1;  inversion H0 ; inversion H1 ; 
    try  match goal with 
    | mpz : ty ?e = (gmp_t_ext Mpz), int : ty ?e = C_Int  |- _ => now rewrite mpz in int end.
    (* both ty(e1) = int and ty(e2) = int *)
   subst. constructor... destruct x,x0. econstructor... simpl in *.
        + eapply ty_int_gmp_c_exp_equiv in H5...
        + eapply ty_int_gmp_c_exp_equiv in H8...
Qed.


Lemma semantics_of_the_binop_macro_mpz :
    forall f (ev:Env) (op:fsl_binop_int) c y r e1 e2 v1 v2 z1 z2 l1 l2,
    _no_env_mpz_aliasing ev ->
    type_of_value (ev c) = Some C_Int ->
    ev |= e1 ⇝ z1 ->
    ev |= e2 ⇝ z2 ->

    let zr := ⋄ op z1 z2 in
    ev v1 = Some (Def (VMpz (Some l1))) /\  ev v2 = Some (Def (VMpz (Some l2))) /\  ev c = Some (Def (VMpz (Some y))) ->
    ~ List.In v1 (exp_vars e2) -> (* not in paper proof *)
    exists M, (forall v n, ev v = Some (Def (VMpz (Some n))) ->
    ev v1 <> ev v /\ ev v2 <> ev v -> ev.(mstate) n = M n) -> 
    l1 <> l2 -> (* not in paper proof *)
    gmp_stmt_sem f ev (binop_ASSGN op (c,T_Ext Mpz) e1 e2 r v1 v2) (ev <| mstate := M{y\Defined zr} |>)
    .
Proof with eauto using p_map_same with rac_hint.
    intros f ev op c y r e1 e2 v1 v2 z1 z2 l1 l2 Hnoalias H H0 H1 zr H2 H3. 
    exists ev.(mstate){l2\Defined z2,l1\Defined z1}. intros. destruct H2 as (v1l & v2l & rl). unfold binop_ASSGN.
    apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |>).
    - apply semantics_of_the_mpz_assgn_macro...
    - apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |> <| mstate ::= {{l2\Defined z2}} |>). 
        * apply semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
        * constructor.  
            replace  (ev <| mstate := ev.(mstate) {y \Defined zr, l2 \Defined z2, l1 \Defined z1} |>)
            with (ev <| mstate ::= {{l1 \Defined z1}} |> 
                    <| mstate ::= {{l2 \Defined z2}} |>
                    <| mstate ::= {{y \Defined zr}} |> 
            ) by reflexivity.
        apply S_op with l1 l2 ; simpl...  apply p_map_not_same_eq...
Qed.