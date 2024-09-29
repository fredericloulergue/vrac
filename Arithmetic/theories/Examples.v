From Coq Require Import ZArith.ZArith Lists.List String.

From RAC Require Import Utils Environnement Translation.
From RAC.Languages Require Import Syntax Semantics.


Import ListNotations FunctionalEnv Domain.

#[local] Open Scope string_scope.
#[local] Open Scope list_scope.
#[local] Open Scope Z_scope.
#[local] Open Scope utils_scope.
#[local] Open Scope mini_c_scope.
#[local] Open Scope list.



Definition two := VInt (2 ⁱⁿᵗ eq_refl).
Definition three := VInt (3 ⁱⁿᵗ eq_refl).
Definition five := VInt (5 ⁱⁿᵗ eq_refl).
Definition ten := VInt (10 ⁱⁿᵗ eq_refl).
Definition fifteen := VInt (15 ⁱⁿᵗ eq_refl).

#[local] Coercion gmp_id (var:id) : c_exp := C_Id var C_Int (T:=Empty_set).

Definition funs {S} := ⊥{"test"\(["a";"b"] , <{ return ("b") }> : c_statement (S:=S))} .




Goal forall s1 s2 s3 s4, between s1 s2 s4  (Seq (Seq s1 (Seq s2 s3)) s4).
Proof.
    intros. eapply (Between_add_r s3 (Seq s1 (Seq s2 s3))).
    - now constructor.
    - auto.
Qed.

Goal forall s1 s2 s3 s4, between s1 s2 s4  (Seq s1 (Seq s2 (Seq s3 s4))).
Proof.
    intros. eapply (Between_add_r s3 (Seq s1 (Seq s2 s3))).
    - now constructor.
    - simpl. now repeat rewrite <- List.app_assoc.
Qed.

Goal forall s1 s2 s3 s4, between s1 s3 s4  (Seq s1 (Seq s2 (Seq s3 s4))).
Proof.
    intros. eapply (Between_add_l s2 <{s2;s3;s4}>).
    - now constructor. 
    - simpl. now repeat rewrite <- List.app_assoc.
Qed.


Goal forall s1 s2 s3 s4, between s1 s2 s4  (Seq (Seq s1 s2) (Seq s3 s4)).
    intros. eapply (Between_add_r s3 (Seq (Seq s1 s2) s3)).
    - constructor. simpl. now rewrite <- List.app_assoc.
    - simpl. now repeat rewrite <- List.app_assoc.  
Qed.

(* Compute (flatten  (Seq (Seq (Assign "x" 1) (Assign "x" 2)) (Assign "x" 3))).
Compute (flatten  (Seq (Assign "x" 1) (Seq  (Assign "x" 2) (Assign "x" 3)))).
Compute flatten ((Seq (Seq (Assign "x" 1) (Assign "x" 2)) (Seq (Assign "x" 3) (Assign "x" 4)))). *)



(* Open Scope mini_c_decl_scope. *)
(*
Example test_decl : (⊥,⊥) ⋅ ⊥ |= <[ int "x" ]> => (⊥{"x"\UInt},⊥)  ⋅ ⊥.
Proof.
    constructor. 
    - simpl in *. inversion H1. unfold Uτ in H0.  destruct u ; now try discriminate.
    - reflexivity.
Qed.
*)


(* 
latex notation :
BbbA : 𝔸 
mbfA : 𝐀
mitA : 𝐴
mttA : 𝙰
mscrA : 𝒜
mfrakA : 𝔄
mbfscrA : 𝓐
*)


(* Example stmt_test :
    forall v l m,     
    
    ((v{"g"\UInt,"z"\UInt,"x"\UInt,"y"\UInt,"out"\UInt},l)⋅m
    |=
    <{
    "x" = 5 ;
    "y" = 10;
    "z" = "x" + "y";
    "g" = 0;
    "out" <- "test" (1+2,"x"+"g") ;

    if ("z" <= 14)
        "g" = "z"
    else 
        "g" = "out" / 5
    }>
    =>
    (v{"g"\ (VInt one), "out"\  five, "g"\ (VInt zero), "z"\ fifteen, "y"\ ten, "x" \  five,"g"\UInt,"z"\UInt,"x"\UInt,"y"\UInt,"out"\UInt}, l) ⋅m) funs
   .
Proof.
    intros. eapply S_Seq. apply S_Assign. reflexivity.  apply C_E_Int. 
    eapply S_Seq.
     - apply S_Assign. reflexivity. apply C_E_Int.
     - eapply S_Seq.
        + apply S_Assign. reflexivity. apply C_E_BinOpInt with (z:=5) (z':=10) (z_ir:=ir5) (z'_ir:=ir10) ; 
          now apply C_E_Var. 
        + eapply S_Seq.
          ++ apply S_Assign. reflexivity. apply C_E_Int.
          ++ eapply S_Seq.
          { simpl.  
          eapply S_FCall with
              (resf:="out")
              (env':=  (⊥{"out"\five, "b" \five, "a" \three}, ⊥))
              (b := <{ return ("b") }>)
              (funs:=funs)
              (zargs := [three;five])
              (xargs := ["a";"b"])
            . split ; split ; reflexivity.
            - reflexivity.
            - simpl. constructor. 
                apply C_E_BinOpInt with (z_ir:=oneinRange) (z'_ir:=ir2) ; now constructor.
                constructor.
                apply C_E_BinOpInt with (z_ir:=ir5) (z'_ir:=zeroinRange) ; now constructor.
                constructor.
            - simpl. constructor. constructor. now constructor.
            - simpl. constructor.
            }
           apply S_IfFalse.
            * apply C_E_BinOpFalse with 15 14 ir15 ir14 ; try now constructor.
            * constructor. reflexivity. simpl. apply C_E_BinOpInt with  (z:=(5)) (z':=5) (z_ir:=ir5) (z'_ir:=ir5) ; now constructor.
Qed.


Example whileex : (⊥{"m"\VInt zero, "n"\three},⊥) ⋅ ⊥ |= <{ while  "n" > 0  <{"n" = "n" - 1 ; "m" = "m" + 1}> }> => (⊥{"m"\three, "n"\VInt zero,"m"\two, "n"\VInt one,"m"\VInt one, "n"\two,"m"\VInt zero, "n"\three},⊥)⋅⊥.
Proof.
    apply S_While. apply S_IfTrue with one. split. 
    - eapply C_E_BinOpTrue. apply C_E_Var. reflexivity. apply C_E_Int. reflexivity.
    - intro contra. inversion contra. 
    - { eapply S_Seq.  eapply S_Seq.
        - apply S_Assign.  reflexivity. eapply C_E_BinOpInt.  apply C_E_Var. reflexivity. apply C_E_Int.
        - apply S_Assign. reflexivity. eapply C_E_BinOpInt. apply C_E_Var. reflexivity. apply C_E_Int.
        -  apply S_While. eapply S_IfTrue. split.
            eapply C_E_BinOpTrue. apply C_E_Var. reflexivity. apply C_E_Int. reflexivity.
            intro contra. inversion contra.
            {
                eapply S_Seq. eapply S_Seq.
                - apply S_Assign. reflexivity. eapply C_E_BinOpInt. apply C_E_Var. reflexivity. apply C_E_Int.
                - apply S_Assign. reflexivity.  eapply C_E_BinOpInt.  apply C_E_Var. reflexivity. apply C_E_Int.
                - apply S_While. eapply S_IfTrue. split.
                    eapply C_E_BinOpTrue. apply C_E_Var. reflexivity. apply C_E_Int. reflexivity.
                 intro contra. inversion contra.
                 {
                     eapply S_Seq. eapply S_Seq.
                     - apply S_Assign. reflexivity.  eapply C_E_BinOpInt. apply C_E_Var. reflexivity. apply C_E_Int.
                     - apply S_Assign. reflexivity.  eapply C_E_BinOpInt. apply C_E_Var. reflexivity. apply C_E_Int.
                     - apply S_While.  eapply S_IfFalse.
                     eapply C_E_BinOpFalse. apply C_E_Var. reflexivity. apply C_E_Int. reflexivity.
                     constructor. 
                     Unshelve. apply zeroinRange. apply oneinRange. apply oneinRange.  apply oneinRange. 
                                apply zeroinRange.  apply oneinRange. apply zeroinRange.  apply oneinRange.  
                                apply oneinRange.  apply zeroinRange.    
                }
           
           }
     }
Qed. *)


#[local] Open Scope domain_scope.
Example test_dom : 2 ∉ (fun x => if x>?2 then Some (Z.mul x 2) else None).
Proof. easy. Qed.
Close Scope domain_scope.


#[local] Open Scope nat.

(* monad *)

Module TMNotations := MonadNotations(TranslationMonad).

Import TMNotations.
(* Compute (exec (n <- fresh ;;; n)). *)

Fixpoint test (x:  list bool) := match x with
  | i::t => c <- (if i then TranslationMonad.fresh else TranslationMonad.ret 9) ;; let v := (i,c) in x <- test t ;;; v::x
  | nil => TranslationMonad.ret nil 
end.
(* Compute (exec (test (true::true::false::false::true::false::nil))). *)




Example add_var_int : forall (ir3 :MI.inRange 3),  empty_env +++ (C_Int, "y", 3) (empty_env  <| env ; vars := ⊥{"y"\Def (VInt ( 3ⁱⁿᵗ ir3))} |>).
Proof. now constructor. Qed.


Example add_var_mpz  : 
add_z_var empty_env Mpz "y" 3  
    ( empty_env 
        <| env ; vars := ⊥{"y"\Def 1%nat} |>
        <| mstate := ⊥{(1%nat)\(Defined 3)} |>
    )
.
Proof.
    assert (ir3: MI.inRange 3) by easy.
    now apply typeMpz.
Qed.


From Coq Require Import Sets.Ensembles.
Close Scope nat_scope.

Example envaddnil : add_z_vars empty_env (Empty_set _) empty_env.
Proof.
 constructor.
Qed.


Example envaddone : add_z_vars empty_env  (Singleton _ (T_Ext Mpz, "y", 3))
    (empty_env 
        <| env ; vars := ⊥{"y"\Def (VMpz 1%nat)} |>
        <| mstate := ⊥{1%nat\(Defined 3)} |>
    )
.
Proof.
    replace (Singleton _ (T_Ext Mpz, "y", 3)) with (Add _ (Empty_set _) (T_Ext Mpz, "y", 3)).
    - assert (ir3: MI.inRange 3) by easy.
        apply (add_z_vars_cons empty_env (Empty_set _) (T_Ext Mpz) "y" 3) .
        apply (typeMpz empty_env Mpz "y" 3 1%nat).
        * reflexivity.
        * intro v. intro contra. inversion contra.
    - apply Extensionality_Ensembles. split. 
      * autounfold with sets. intros. destruct H.
        + inversion H.
        + auto with sets.
      * autounfold with sets. intros. now constructor.
Qed.




Module DummyOracle : Oracle.Oracle.
    Definition interval := Z ⨉ Z.
    
    Definition Γᵢ : Type :=  StringMap.t interval. 

    Definition get_Γᵢ : fsl_pgrm -> Γᵢ := fun _ => StringMap.empty.

    Definition oracle : ℨ ⨉ Γᵢ -> interval := fun _ => (-10,10).

    Definition ty_from_interval : interval -> 𝔗 := fun _ => Mpz. 

    Definition get_ty : ℨ ⨉ Γᵢ -> 𝔗 := fun x =>  ty_from_interval (oracle x).

    Parameter ty_funcall_is_ty_body: 
    forall (f : fsl_prog_fenv) fname xargs (targs:list ℨ) (iargs:list interval) b, 
    StringMap.find fname f.(lfuns) = Some (xargs,b) ->
    forall te,
    List.Forall2 (fun e i => oracle (e,te) = i) targs iargs ->
        get_ty (T_Call fname targs,te) = get_ty (b,StringMap.add_all xargs iargs StringMap.empty).

    Inductive fits (z:Z) : 𝔗 -> Prop := 
    | InInt : MI.inRange z -> fits z C_Int
    | InMpz : fits z (T_Ext Mpz)
    .

    Parameter ϴ_int_or_mpz : forall i, ty_from_interval i = C_Int \/  ty_from_interval i = T_Ext Mpz.

    Parameter get_ty_prog_var : forall x i, get_ty (T_Id x FSL_Int, i) = C_Int.

    Parameter type_soundness : forall env te f t z, 
    fsl_term_sem f env t z -> fits z (get_ty (t,te)).

    Parameter convergence_of_lfuns_ty : 
    forall fname (targs:list ℨ) (iargs:list interval), 
    forall (typing_envs : Ensembles.Ensemble Γᵢ)  (fe:Γᵢ), Ensembles.In Γᵢ typing_envs fe ->
    (exists ty te, get_ty (T_Call fname targs,te) = ty) -> 
    Finite_sets.Finite _ typing_envs
    .

End DummyOracle.


Module T := Translation.Translation(DummyOracle).

Definition x := FSL_Decl (T_Ext Mpz) "x".
Definition y := FSL_Decl (T_Ext Mpz) "y".

Definition p : predicate := (P_BinOp (T_Id "x" FSL_Int) FSL_Gt (T_Id "y" FSL_Int)). 

(* Definition greaterThan : predicate := P_Call "greaterThan" [T_Id "x" FSL_Int; T_Z 3]. *)

(* Compute ( 
        let z := (C_Id "z" C_Int) in 
        T.translate_program 
        ([] : list _c_decl,
        [<[ /*@ predicate "greaterThan"(x,y) = p  */ ]>;
        <[
            fun int "add" ((C_Decl C_Int "z")) [
                (C_Decl C_Int "nothing") ; 

                 <{
                    "x" = z + 3  ;
                    /*@ assert p  */ ;
                    "x" = 2
                 }> 
            ]
         ]> 
        ]
        ) 
).  *)