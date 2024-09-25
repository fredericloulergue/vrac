From Coq Require Import  ZArith.ZArith BinaryString.

From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax Semantics Lemmas.


Import FunctionalEnv.

#[local] Open Scope Z_scope.
#[local] Open Scope utils_scope.
#[local] Open Scope mini_c_scope.
#[local] Open Scope mini_gmp_scope.



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
    
    | C_Int =>  <{(Assign v e)}>
    | _ => Skip
end.

Definition τ_ASSGN (t:gmp_t) := match t with
    | T_Ext Mpz => mpz_ASSGN
    | C_Int => int_ASSGN
    | _ => int_ASSGN (* cannot happen  *)
    end.

Definition Z_ASSGN (τz:gmp_t) v (z:Z) : gmp_statement := match τz with
    | C_Int => <{(Assign v z )}>
    | T_Ext Mpz => <( set_s(v, (BinaryString.of_Z z) ) )>
    | _ => Skip (* cannot happen  *)
end.




Definition CMP c (e₁ e₂ : gmp_exp) v₁ v₂ : gmp_statement := match ty e₁, ty e₂ with
    |  C_Int,C_Int => 
        <{ 
            if (e₁ < e₂) (Assign c (-1))
            else if (e₁ > e₂) (Assign c 1)
            else (Assign c 0)
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
    | C_Int,C_Int,C_Int =>  let res := BinOpInt e₁ (□ fsl_op) e₂ in <{ (Assign c res) }>
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
    no_aliasing ev ->
    ~ StringSet.In v (exp_vars e) ->
    ev v = Some (Def (VMpz (Some l))) ->
    ev |= e ⇝ z ->
    ev <| mstate ::= {{l \ Defined z'}} |> |= e ⇝ z.

Proof.
    intros. inversion H2.
    - subst. constructor 1;auto. apply untouched_var_same_eval_exp with v ; auto. 
        now rewrite gmp_exp_c_exp_same_exp_vars. 

    - subst. pose proof (mpz_exp_is_var e). apply H6 in H3 as [var].  subst. simpl in *.
        apply M_Mpz with l0; subst.
        + now simpl.
        + simpl. rewrite StringSet.singleton_spec in H0. 
            destruct (eq_dec l l0).
            * subst. destruct H with v var l0 l0 ; congruence.
            * now simpl.
        + rewrite StringSet.singleton_spec in H0. destruct (eq_dec l l0).
            * subst. destruct H with v var l0 l0 ; congruence.
            * simpl. apply p_map_not_same_eq;auto.
Qed.


#[local] Open Scope gmp_stmt_sem_scope.

(* SECTION E: PROOFS OF THE SEMANTICS OF THE MACROS *)


Lemma LE1_semantics_of_the_mpz_assgn_macro :
    forall f e z (ev : Env) v (y:location),
    ev |= e ⇝ z ->
    ev v = Some (Def (VMpz y)) ->
    (ev |= mpz_ASSGN v e => ev <| mstate ::= {{y\Defined z}} |>) f
.
(* implies either set_i or set_z, everything else is not possible *)
Proof.
    intros. 
    unfold mpz_ASSGN. destruct (ty e) eqn:TY.  
    - inversion H ; constructor. 
        + now apply S_set_i.
        + now rewrite H1 in TY. 
    - inversion H.
        + now rewrite H1 in TY.
        + now rewrite H1 in TY. 
    -  inversion H.
        + now rewrite H1 in TY.
        + rewrite TY in H1. subst. inversion H1. destruct e; simpl in TY ; subst; try discriminate.
            * constructor.  apply S_set_z with l;auto. 
            *  destruct (ty e1); try congruence. destruct (ty e2); congruence.
            *  destruct (ty e1); try congruence. destruct (ty e2); congruence.
Qed.

Lemma LE2_semantics_of_the_int_assgn_macro :
    forall f e z (ir: Int.inRange z) (ev:Env) v,
    is_comp_var v = false ->
    ev |= e ⇝ z ->
    type_of_value (ev v) = Some C_Int ->
    (ev |= int_ASSGN v e => ev <| env ; vars ::= {{v\VInt (z ⁱⁿᵗ ir) : 𝕍}} |>) f
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
        + now rewrite H1 in EqTY.
        + now rewrite H1 in EqTY. 
    - inversion H; subst.
        + now rewrite H1 in EqTY.
        +  destruct t. 
            * now rewrite EqTY in H1.
            * destruct e; simpl in EqTY ;try discriminate.
                2,3:  destruct (ty e1); try congruence; destruct (ty e2); congruence.
                constructor. subst. simpl in H2. apply S_get_int with l; auto.
Qed.

Lemma LE3_semantics_of_the_Z_assgn_macro_tint :
    forall f z (ir: Int.inRange z) (ev:Env) v,
    is_comp_var v = false ->
    type_of_value (ev v) = Some C_Int ->
    (ev |= Z_ASSGN C_Int v z => ev <| env ; vars ::= {{v\VInt (z ⁱⁿᵗ ir) : 𝕍}} |>) f
.
Proof.
    intros.  constructor ; auto with rac_hint.
Qed.

Lemma LE3_semantics_of_the_Z_assgn_macro_tmpz :
    forall f y (z:ℤ) (ev:Env) v,
    ev v = Some (Def (VMpz (Some y))) ->
    (ev |= Z_ASSGN Mpz v z => ev <| mstate ::= {{y\Defined z}} |>) f
.
Proof with auto using BinaryString.Z_of_of_Z.
    intros. simpl. constructor. apply S_set_s...
Qed.


Lemma LE4_semantics_of_the_cmp_macro :
    forall f (ev:Env) c e1 e2 v1 v2 z1 z2 a,


    no_aliasing ev ->  (* not in paper proof *)
    ~ StringSet.In v1 (exp_vars e2) -> (* not in paper proof *)
    v1 <> v2 -> (* not in paper proof *)
    type_of_value (ev c) = Some C_Int (* not in paper proof *) /\ is_comp_var c = false (* added *) -> 


    (* v1 and v2 must be bound to a mpz location (implied by mpz_assign ) *)
    forall (l1 l2 : location),
    ev v1 = Some (Def (VMpz l1)) /\  ev v2 = Some (Def (VMpz l2)) ->
    

    exists M': 𝓜, (
        forall v, 
        v <> v1 /\ v <> v2  -> 
        forall (n:location), ev v = Some (Def (VMpz n)) ->
        ev.(mstate) n = M' n
    ) /\
    (
        (
            (Def a = VInt sub_one <-> Z.lt z1 z2 ) /\
            (Def a = VInt zero <-> z1 = z2) /\
            (Def a = VInt one <-> Z.gt z1 z2)
        ) -> 

        ev |= e1 ⇝ z1 -> 
        ev |= e2 ⇝ z2 ->

        (ev |= CMP c e1 e2 v1 v2 => ev <| env ; vars ::= {{c\Def a}} |> <| mstate := M' |>) f 
    )
.

Proof with try easy ; auto with rac_hint ; unshelve eauto using Z.ltb_irrefl,Z.gtb_ltb,Z.ltb_lt with rac_hint; auto with rac_hint.
    intros f ev c e1 e2 v1 v2 z1 z2 a Hnoalias Hv1NotIne2 Hv1notv2 [Hnocom Hc] l1 l2 [Hv1 Hv2].
    
    assert (NotInt : 
        exists M' : 𝓜,
        (forall v : id, 
            v <> v1 /\ v <> v2 -> 
            forall n : location, ev v = Some (Def (VMpz n)) -> ev.(mstate) n = M' n
        ) 
        /\
        (
            (
                (Def a = VInt sub_one <-> Z.lt z1 z2 ) /\
                (Def a = VInt zero <-> z1 = z2) /\
                (Def a = VInt one <-> Z.gt z1 z2)
            ) ->             ev |= e1 ⇝ z1 ->
            ev |= e2 ⇝ z2 ->
            gmp_stmt_sem f ev <{ (mpz_ASSGN v1 e1); (mpz_ASSGN v2 e2); (<(c = cmp (v1, v2))> : gmp_statement)}>
            (ev <| env; vars ::= {{c \Def a}} |> <| mstate := M' |>)
        )
    ). {
        exists ev.(mstate){l2 \Defined z2, l1 \Defined  z1}. split.
        - intros v [Hvneqv1 Hvneqv2] n Hv. repeat rewrite p_map_not_same...
        - intros Ha He1 He2.  
            apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |>).
            + apply LE1_semantics_of_the_mpz_assgn_macro...
            + apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |> <| mstate ::= {{l2\Defined z2}} |> ). 
                * apply LE1_semantics_of_the_mpz_assgn_macro...  inversion_clear He2 ; subst. 
                    -- constructor... eapply untouched_var_same_eval_exp... now rewrite gmp_exp_c_exp_same_exp_vars.
                    -- econstructor... apply p_map_not_same_eq... destruct e2; try discriminate. 
                        ++ simpl in H. subst. simpl in H0. destruct (eq_dec var v1)...
                            subst. exfalso. apply Hv1NotIne2. simpl. now left.
                        ++ exfalso. simpl in H. destruct (ty e2_1) , (ty e2_2); simpl in H; discriminate.  
                        ++  exfalso. simpl in H. destruct (ty e2_1) , (ty e2_2); simpl in H; discriminate.  

                * constructor.
                    replace  (_ <| env; vars ::= _ |><| mstate := _ |>)
                    with (ev <| mstate := ev.(mstate) {l2 \Defined z2, l1 \Defined z1} |><| env; vars ::= {{c \Def a}} |> ) 
                    by reflexivity.
                    apply S_cmp with (lx:=l1) (ly:=l2) (zx:=z1) (zy:=z2) ; simpl... apply p_map_not_same_eq...
    } 
    unfold CMP. destruct (ty e1) eqn:T1, (ty e2) eqn:T2; try apply NotInt. clear NotInt.
    
    (* both ty(e1) = int and ty(e2) = int *)
    exists ev.(mstate). split ; [auto|]. intros (inf & eq & sup) He1 He2. inversion He1; inversion He2; 
        try match goal with
        | mpz: ty ?e = (gmp_t_ext Mpz), int : ty ?e = C_Int  |- _ => now rewrite mpz in int end. 
    
    destruct (Z.lt_trichotomy z1 z2) as [inf' | [ eq' | sup']].
    
    (* z1 < z2 *)
    - assert (cmp := inf'). apply <- inf in inf'. clear eq inf sup. subst. 
        destruct x,x0. simpl in *.  apply S_IfTrue with one.
        + split ; [| easy]. apply C_E_BinOpTrue with x x0 i i0. 
            * now apply ty_int_gmp_c_exp_equiv.
            * now apply ty_int_gmp_c_exp_equiv.
            * apply Z.ltb_lt. apply cmp.
        + inversion inf'. constructor...

    (* z1 = z2 *)
    - assert (cmp := eq'). rewrite <- eq in eq'. clear eq inf sup. subst.
        destruct x,x0. apply Int.mi_eq in cmp. injection cmp as cmp. inversion eq'. subst. simpl in *. constructor.
        + econstructor... 
            * apply ty_int_gmp_c_exp_equiv...
            * apply ty_int_gmp_c_exp_equiv...
        + constructor.
            * econstructor...
                -- apply ty_int_gmp_c_exp_equiv... 
                -- apply ty_int_gmp_c_exp_equiv...
            * constructor...


    (* z1 > z2 *)
    - assert (cmp := sup').  apply Z.lt_gt in sup'. apply <- sup in sup'.  clear inf eq sup. subst.
        destruct x, x0. subst. constructor ; simpl in *.
        + apply C_E_BinOpFalse with x x0 i i0.
            * apply ty_int_gmp_c_exp_equiv...
            * apply ty_int_gmp_c_exp_equiv...
            * apply Z.ltb_ge. auto with zarith. 
        + inversion sup'. subst. apply S_IfTrue with one.
            *  subst. split; [|easy]. apply C_E_BinOpTrue with x x0 i i0.
                -- apply ty_int_gmp_c_exp_equiv...
                -- apply ty_int_gmp_c_exp_equiv...
                -- now apply Z.gtb_lt.
            *  constructor...
Qed.




Lemma LE5_semantics_of_the_binop_macro_int :  
    forall f (ev:Env) (op:fsl_binop_int) c r (e1 e2 : gmp_exp) v1 v2 z1 z2 (ir: Int.inRange (⋄ op z1 z2) ),

    no_aliasing ev ->  (* not in paper proof *)
    ~ StringSet.In v1 (exp_vars e2) -> (* not in paper proof *)
    v1 <> v2 -> (* not in paper proof *)
    type_of_value (ev c) = Some C_Int /\ is_comp_var c = false (* added *) -> 


    (* v1 and v2 must be bound to a mpz location (implied by mpz_assign ) *)
    forall (l1 l2 lr: location),

    ev v1 = Some (Def (VMpz (Some l1))) /\  
    ev v2 = Some (Def (VMpz (Some l2))) /\
    ev r = Some (Def (VMpz (Some lr))) ->


    exists M': 𝓜, (
        forall v, 
        v <> v1 /\ v <> v2 /\ v <> r -> 
        forall (n:location), ev v = Some (Def (VMpz n)) ->
        ev.(mstate) n = M' n
    ) /\
    (
        ev |= e1 ⇝ z1 -> 
        ev |= e2 ⇝ z2 ->

        (ev |= binop_ASSGN op (c,C_Int) e1 e2 r v1 v2 => ev <| env ; vars ::= fun e => e{c\VInt ((⋄ op z1 z2) ⁱⁿᵗ ir) : 𝕍} |> <| mstate := M' |>) f 
    )
.

Proof with eauto with rac_hint.
    intros f ev op c r e1 e2 v1 v2 z1 z2 ir Hnoalias Hv1NotIne2 Hv1notv2 [Hnocom Hc] l1 l2 lr (Hv1 & Hv2 & Hr).  
    assert (NotInt : 
        exists M' : 𝓜,
        (forall v : id, 
            v <> v1 /\ v <> v2 /\ v <> r -> 
            forall n : location, ev v = Some (Def (VMpz n)) -> ev.(mstate) n = M' n
        ) 
        /\
        (
            ev |= e1 ⇝ z1 ->
            ev |= e2 ⇝ z2 ->

            (ev |= 
                <{
                    (mpz_ASSGN v1 e1); (mpz_ASSGN v2 e2); (gmp_s_ext (fsl_to_gmp_op op r v1 v2)); (int_ASSGN c (C_Id r (T_Ext Mpz)))
                }> 
            => ev <| env; vars ::= (fun e : Ωᵥ => (e) {c \VInt (⋄ op z1 z2 ⁱⁿᵗ ir) : 𝕍}) |> <| mstate := M' |>)%gmpssem f
        )
    ). {
        exists ev.(mstate){lr\Defined (⋄ op z1 z2),l2\Defined z2,l1\Defined z1}. split.
        - intros v (Hvneqv1 & Hvneqv2 & Hvneqr) n Hv. repeat rewrite p_map_not_same...
        - intros He1 He2. apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |>). 
            + apply LE1_semantics_of_the_mpz_assgn_macro...
            + apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |> <| mstate ::= {{l2\Defined z2}} |> ). 
                * apply LE1_semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
                * apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |> <| mstate ::= {{l2\Defined z2}}  |> <| mstate ::= {{lr\Defined (⋄ op z1 z2)}} |>).
                    -- constructor. apply S_op with l1 l2...  
                        ++ simpl.  apply p_map_not_same_eq...
                        ++ simpl. apply p_map_same. 
                    -- replace (ev <| env; vars ::= _ |> <| mstate :=  _ |>)
                        with (ev <| mstate := ev.(mstate) {lr \Defined (⋄ op z1 z2), l2 \Defined z2, l1 \ Defined z1} |> 
                                <| env; vars ::= {{c \Def (VInt (((⋄ op z1 z2) ⁱⁿᵗ) ir))}} |>
                        ) 
                        by reflexivity.
                apply LE2_semantics_of_the_int_assgn_macro...  apply M_Mpz with lr ; simpl...
    } 
    
    unfold binop_ASSGN. destruct (ty e1) eqn:T1, (ty e2) eqn:T2 ; try apply NotInt. clear NotInt.

    exists ev.(mstate). split ; [auto|]. intros  He1 He2. inversion He1; inversion He2; 
        try match goal with
        | mpz: ty ?e = (gmp_t_ext Mpz), int : ty ?e = C_Int  |- _ => now rewrite mpz in int end. 
    (* both ty(e1) = int and ty(e2) = int *)
    subst. constructor... destruct x,x0. econstructor.
    - eapply ty_int_gmp_c_exp_equiv in H0...
    - eapply ty_int_gmp_c_exp_equiv in H3...
Qed.


Lemma LE5_semantics_of_the_binop_macro_mpz :
    forall f (ev:Env) (op:fsl_binop_int) c y r e1 e2 v1 v2 z1 z2,

    no_aliasing ev ->
    ~ StringSet.In v1 (exp_vars e2) -> (* not in paper proof *)
    type_of_value (ev c) = Some C_Int -> (* not in paper proof *)
    v1 <> v2 -> (* not in paper proof *)


    (* v1 and v2 must be bound to a mpz location (implied by mpz_assign ) *)
    forall (l1 l2 lr: location),

    ev v1 = Some (Def (VMpz (Some l1))) /\  
    ev v2 = Some (Def (VMpz (Some l2))) /\ 
    ev c = Some (Def (VMpz (Some y))) ->

    exists M': 𝓜, (
        forall v,
            v1 <> v /\ v2 <> v -> 
            forall (n:location), ev v = Some (Def (VMpz n)) ->
            ev.(mstate) n = M' n
    ) /\
    (
        ev |= e1 ⇝ z1 ->
        ev |= e2 ⇝ z2 ->

    (ev |= binop_ASSGN op (c,T_Ext Mpz) e1 e2 r v1 v2 => ev <| mstate := M'{y\Defined (⋄ op z1 z2)} |>) f 
    ).
Proof with eauto using p_map_same with rac_hint.
    intros f ev op c y r e1 e2 v1 v2 z1 z2  Hnoalias Hv1NotIne2 Hv1notv2 Htyc l1 l2 lr (Hv1 & Hv2 & Hc).  
    exists ev.(mstate){l2\Defined z2,l1\Defined z1}. split.
    - intros v [Hneqv1 Hneqv2] n Hv. repeat rewrite p_map_not_same...
    
    - intros He1 He2.  unfold binop_ASSGN.
        apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |>).
        + apply LE1_semantics_of_the_mpz_assgn_macro...
        + apply S_Seq with (ev <| mstate ::= {{l1\Defined z1}} |> <| mstate ::= {{l2\Defined z2}} |>). 
            * apply LE1_semantics_of_the_mpz_assgn_macro... apply same_eval_macro with v1...
            * constructor.  
                replace  (ev <| mstate := ev.(mstate) {y \Defined (⋄ op z1 z2), l2 \Defined z2, l1 \Defined z1} |>)
                with (ev <| mstate ::= {{l1 \Defined z1}} |> 
                    <| mstate ::= {{l2 \Defined z2}} |>
                    <| mstate ::= {{y \Defined (⋄ op z1 z2)}} |> 
                )
                by reflexivity.
                apply S_op with l1 l2 ; simpl...  apply p_map_not_same_eq... 
Qed.