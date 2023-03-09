Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import RAC.Semantics.
Require Import ZArith.ZArith.
Require Import String.
From Coq Require Import Lists.List.
Open Scope string_scope.
Open Scope fsl_scope.
Open Scope Z_scope.
Open Scope list_scope.



Declare Scope mini_c_scope.

Declare Custom Entry mini_c.

Notation "<{ e }>" := e (at level 0, e custom mini_c at level 99) : mini_c_scope.
Notation "( x )" := x (in custom mini_c, x at level 99) : mini_c_scope.
Notation "x" := x (in custom mini_c at level 0, x constr at level 0) : mini_c_scope.
Notation "'skip'" := Skip  (in custom mini_c at level 0) : mini_c_scope.
Notation "'if' '(' cond ')' '{' _then '}' 'else' '{' _else '}'" := (If cond _then _else)  
    (in custom mini_c at level 89, cond at level 99, _then at level 99, _else at level 99) : mini_c_scope.
Notation "x + y"   := (C_Add x y) (in custom mini_c at level 50, left associativity) : mini_c_scope.
Notation "s1 ';' s2" := (Seq s1 s2) (at level 65, right associativity) : mini_c_scope.
Notation "x := y" := (Assign x y) (in custom mini_c at level 0, x constr at level 0, y at level 85, no associativity) : mini_c_scope.


Open Scope mini_c_scope. 

Lemma ir5 : Int.inRange 5. Proof. split ; reflexivity. Qed.
Lemma ir10 : Int.inRange 10. Proof. split ; reflexivity. Qed.
Lemma ir15 : Int.inRange 15. Proof. split ; reflexivity. Qed.
Definition five := Int.of_z 5 ir5.
Definition ten := Int.of_z 10 ir10.
Definition fifteen := Int.of_z 15 ir15.


Example stmt_5Plus10 :
    forall o m,     
    let v := fst o in 
    let l := snd o in 
    c_stmt_sem
    (
            (Assign "x" 5) ;
            (Assign "y" 10)  ;
            (Assign "z" (BinOpInt "x" C_Add "y"))
    )
    o m (v{"x" \ five}{"y"\ten}{"z"\fifteen}, l) m
   .
Proof.
    intros.
     apply S_Seq with (v{"x" \ five},l) m.
     apply S_Assign. apply E_Int.
     apply S_Seq with (v{"x" \ five}{"y" \ ten}, l) m.
     - apply S_Assign. apply E_Int.
     - apply S_Assign. apply E_BinOpInt with (z:=5) (z':=10) (z_ir:=ir5) (z'_ir:=ir10) ; apply E_Var.
        * reflexivity.
        * reflexivity.
Qed.

     
