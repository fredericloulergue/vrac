From RAC Require Import Utils Environnement Translation.
From RAC.Languages Require Import Syntax Semantics.
From Coq Require Import ZArith.ZArith Lists.List String.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope utils_scope.


Definition two := VInt (2 ⁱⁿᵗ eq_refl).
Definition three := VInt (3 ⁱⁿᵗ eq_refl).
Definition five := VInt (5 ⁱⁿᵗ eq_refl).
Definition ten := VInt (10 ⁱⁿᵗ eq_refl).
Definition fifteen := VInt (15 ⁱⁿᵗ eq_refl).

#[local] Coercion gmp_id (var:id) : _c_exp := C_Id var C_Int (T:=Empty_set).

Definition funs  := ⊥{"test"\(["a";"b"] , <{ return ("b") }> : c_statement)} .

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

Open Scope c_sem_scope.
Open Scope mini_gmp_scope.

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

Example test_dom : 2 ∉ (fun x => if x>?2 then Some (x*2) else None).
Proof. easy. Qed.



Close Scope Z_scope.

(* monad *)
Export CounterMonad.
(* Compute (exec (n <- fresh ;;; n)). *)

Fixpoint test (x:  list bool) : state := match x with
  | i::t => c <- (if i then fresh else ret 9) ;; let v := (i,c) in x <- test t ;;; v::x
  | nil => ret nil 
end.
(* Compute (exec (test (true::true::false::false::true::false::nil))). *)


Open Scope Z_scope.
Open Scope mini_gmp_scope.

Module DummyOracle : Oracle.Oracle.
    Record 𝐼 := mkInterval {min : Z; max : Z}.
    
    Definition 𝓘 : ℨ -> (𝔏 ⇀ 𝐼) -> 𝐼 := fun _ _ => mkInterval (-10) 10.

    Definition ϴ : 𝐼 -> 𝔗 := fun _ => Mpz. 

    Definition Γᵢ : Type :=  𝔏 ⇀ 𝐼. 

    Definition 𝒯 : ℨ -> (𝔏 ⇀ 𝐼) -> 𝔗 := fun t τᵢ =>  ϴ (𝓘 t τᵢ).

    Parameter ty_funcall_is_ty_body: 
    forall S (f : @fenv _fsl_statement S) fname xargs (targs:list ℨ) (iargs:list 𝐼) b, 
    f.(lfuns) fname = Some (xargs,b) ->
    forall te,
    List.Forall2 (fun e i => eq (𝓘 e te) i) targs iargs ->
    𝒯 (T_Call fname targs) te = 𝒯 b (p_map_addall_back xargs iargs ⊥).

    Inductive fits (z:Z) : 𝔗 -> Prop := 
    | InInt : Int.inRange z -> fits z C_Int
    | InMpz : fits z (T_Ext Mpz)
    .

    Parameter type_soundness : forall env te f t z, 
    fsl_term_sem f env t z -> fits z (𝒯 t te).

    Parameter convergence_of_lfuns_ty : 
    forall fname (targs:list ℨ) (iargs:list 𝐼), 
    forall (typing_envs : Ensembles.Ensemble Γᵢ)  (fe:Γᵢ), Ensembles.In Γᵢ typing_envs fe ->
    (exists ty te, eq (𝒯 (T_Call fname targs) te) ty) -> 
    Finite_sets.Finite _ typing_envs
    .

End DummyOracle.


Definition dummy_tenv : DummyOracle.Γᵢ := ⊥.


Module T := Translation.Translation(DummyOracle).

Definition dummy_bindings : T.Γᵥ := ⊥.

Definition dummy_defs : T.ψ := ⊥.

Definition x := FSL_Decl (T_Ext Mpz) "x".
Definition y := FSL_Decl (T_Ext Mpz) "y".

Definition p : predicate := (P_BinOp (T_Id "x" FSL_Int) FSL_Gt (T_Id "y" FSL_Int)). 

(* Definition greaterThan : predicate := P_Call "greaterThan" [T_Id "x" FSL_Int; T_Z 3]. *)

Compute ( 
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
        ) dummy_bindings dummy_tenv  
). 