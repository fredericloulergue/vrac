Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import RAC.Semantics.
Require Import ZArith.ZArith.
Require Import String.
From Coq Require Import Lists.List.
Open Scope string_scope.
Open Scope Z_scope.


Open Scope mini_c_scope. 
Open Scope fsl_scope.

Fact ir3 : Int.inRange 3. now split. Qed.
Fact ir5 : Int.inRange 5. now split. Qed.
Fact ir10 : Int.inRange 10 . now split. Qed.
Fact ir14 : Int.inRange 14. now split. Qed.
Fact ir15 : Int.inRange 15. now split. Qed.
Definition zero := Int.of_z 0 zeroinRange.
Definition three := Int.of_z 3 ir3.
Definition five := Int.of_z 5 ir5.
Definition ten := Int.of_z 10 ir10.
Definition fifteen := Int.of_z 15 ir15.


Example imptest :
    forall o m,     
    let v := fst o in 
    let l := snd o in 
    c_stmt_sem
    o m 
    
    <{
        "x" := 5 ;
        "y" := 10;
        "z" := "x" + "y";
        "g" := 0;

        if ("z" <= 14)
            "g" := "z"
        else 
            "g" := "z" / 5

   }>
    
    (v{"x" \ five}{"y"\ten}{"z"\fifteen}{"g"\zero}{"g"\three}, l) m
   .
Proof.
    intros.
     apply S_Seq with (v{"x" \ five},l) m.
     apply S_Assign. apply C_E_Int.
     apply S_Seq with (v{"x" \ five}{"y" \ ten}, l) m.
     - apply S_Assign. apply C_E_Int.
     - apply S_Seq with (v{"x" \ five}{"y" \ ten}{"z" \ fifteen}, l) m.
        + apply S_Assign. apply C_E_BinOpInt with (z:=5) (z':=10) (z_ir:=ir5) (z'_ir:=ir10) ; 
          now apply C_E_Var. 
        + apply S_Seq  with (v{"x" \ five}{"y" \ ten}{"z" \ fifteen}{"g"\ zero}, l) m. 
          ++ apply S_Assign. apply C_E_Int.
          ++ apply S_IfFalse with zero.
            * apply C_E_BinOpFalse with 15 14 ir15 ir14 ; try now constructor.
            simpl. intro H. destruct H. reflexivity.
            * reflexivity.
            * apply S_Assign. apply C_E_BinOpInt with  (z:=15) (z':=5) (z_ir:=ir15) (z'_ir:=ir5); now constructor.
Qed.

Close Scope mini_c_scope.



Example test_dom : ~ dom (fun x => if x>?2 then Some (x*2) else None) 2.
Proof. intro contra. inversion contra. destruct H. discriminate. Qed.
