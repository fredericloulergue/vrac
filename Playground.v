Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import RAC.Semantics.
Require Import ZArith.ZArith.
Require Import String.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Fact ir2 : Int.inRange 2. now split. Qed.
Fact ir3 : Int.inRange 3. now split. Qed.
Fact ir5 : Int.inRange 5. now split. Qed.
Fact ir10 : Int.inRange 10 . now split. Qed.
Fact ir14 : Int.inRange 14. now split. Qed.
Fact ir15 : Int.inRange 15. now split. Qed.
Definition two := VInt (Int.mkMI 2 ir2).
Definition three := VInt (Int.mkMI 3 ir3).
Definition five := VInt (Int.mkMI 5 ir5).
Definition ten := VInt (Int.mkMI 10 ir10).
Definition fifteen := VInt (Int.mkMI 15 ir15).
Definition funs := ⊥{"test"\(["a";"b"] , <{ return ("b") }>)}.


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

Open Scope mini_c_stmt_scope.
Example stmt_test :
    forall v l m,     
    
    (v{"g"\UInt,"z"\UInt,"x"\UInt,"y"\UInt,"out"\UInt},l)⋅m
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
    (v{"g"\ (VInt one), "out"\  five, "g"\ (VInt zero), "z"\ fifteen, "y"\ ten, "x" \  five,"g"\UInt,"z"\UInt,"x"\UInt,"y"\UInt,"out"\UInt}, l) ⋅m
   .
Proof.
    intros. eapply S_Seq. apply S_Assign. reflexivity. apply C_E_Int. 
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
            - simpl. constructor. now constructor.
            - simpl. constructor.
            }
           apply S_IfFalse with zero.
            * apply C_E_BinOpFalse with 15 14 ir15 ir14 ; try now constructor.
            * reflexivity.
            * apply S_Assign. reflexivity. apply C_E_BinOpInt with  (z:=(5)) (z':=5) (z_ir:=ir5) (z'_ir:=ir5) ; now constructor.
Qed.


Example whileex : (⊥{"m"\VInt zero, "n"\three},⊥) ⋅ ⊥ |= <{ while  "n" > 0  <{"n" = "n" - 1 ; "m" = "m" + 1}> }> => (⊥{"m"\three, "n"\VInt zero,"m"\two, "n"\VInt one,"m"\VInt one, "n"\two,"m"\VInt zero, "n"\three},⊥)⋅⊥.
Proof.
    apply S_While. apply S_IfTrue with one.
    - apply C_E_BinOpTrue with 3 0 ir3 zeroinRange. apply C_E_Var. reflexivity. apply C_E_Int. reflexivity.
    - intro contra. inversion contra. 
    - { eapply S_Seq.  eapply S_Seq.
        - apply S_Assign. reflexivity.  apply C_E_BinOpInt with  (z_ir := ir3) (z'_ir := oneinRange).  apply C_E_Var. reflexivity. apply C_E_Int.
        - apply S_Assign. reflexivity. apply C_E_BinOpInt with (z_ir := zeroinRange) (z'_ir := oneinRange). apply C_E_Var. reflexivity. apply C_E_Int.
        -  apply S_While. eapply S_IfTrue.
           apply C_E_BinOpTrue with (z_ir:=ir2) (z'_ir:=zeroinRange). apply C_E_Var. reflexivity. apply C_E_Int. reflexivity.
            intro contra. inversion contra.
            {
                eapply S_Seq. eapply S_Seq.
                - apply S_Assign. reflexivity. apply C_E_BinOpInt with (z_ir := ir2) (z'_ir := oneinRange). apply C_E_Var. reflexivity. apply C_E_Int.
                - apply S_Assign. reflexivity.  apply C_E_BinOpInt with (z_ir := oneinRange) (z'_ir := oneinRange). apply C_E_Var. reflexivity. apply C_E_Int.
                - apply S_While. eapply S_IfTrue.
                apply C_E_BinOpTrue with (z_ir:=oneinRange) (z'_ir:=zeroinRange). apply C_E_Var. reflexivity. apply C_E_Int. reflexivity.
                 intro contra. inversion contra.
                 {
                     eapply S_Seq. eapply S_Seq.
                     - apply S_Assign. reflexivity.  apply C_E_BinOpInt with (z_ir := oneinRange) (z'_ir := oneinRange). simpl. apply C_E_Var. reflexivity. apply C_E_Int.
                     - apply S_Assign. reflexivity.  apply C_E_BinOpInt with (z_ir:=ir2) (z'_ir:=oneinRange). apply C_E_Var. reflexivity. apply C_E_Int.
                     - apply S_While. eapply S_IfFalse.
                     apply C_E_BinOpFalse with (z_ir:=zeroinRange) (z'_ir:=zeroinRange). apply C_E_Var. reflexivity. apply C_E_Int. reflexivity.
                     reflexivity. apply S_skip. 
                
                }
           
           }
     }
Qed.

Example test_dom : 2 ∉ (fun x => if x>?2 then Some (x*2) else None).
Proof. now intros [x contra]. Qed.