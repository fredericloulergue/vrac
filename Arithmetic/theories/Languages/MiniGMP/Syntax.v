From RAC Require Import Notations.
From RAC.Languages Require Import MiniC.Syntax.
From Coq Require Import Strings.String.

Inductive _gmp_t := String | Mpz. 
Coercion gmp_t_ext (t:_gmp_t) : _c_type := T_Ext t.

Definition gmp_t := @_c_type _gmp_t.  (* type extension τ *)
Notation 𝔗 := gmp_t. (* minigmp types *)


(* a gmp expression is a regular c_expression where a variable can additionally be of type String or Mpz *)
Definition gmp_exp := @_c_exp _gmp_t.

Inductive _gmp_statement := 
    | Init (name:id) (* mpz allocation *)
    | Set_i (name:id) (i: c_exp) (* assignment from an int *)
    | Set_s (name:id) (l:string) (* assignment from a string literal *)
    | Set_z (name z:id)(* assignment from a mpz *)
    | Clear (name:id) (* mpz de-allocation *)
    | GMP_Add (lid rid res :id)
    | GMP_Sub (lid rid res :id)
    | GMP_Mul (lid rid res :id)
    | GMP_Div (lid rid res :id)
    | Comp (res lid rid :id) (* mpz comparison *)
    | Coerc (name n : id)  (* mpz coercion *)
    
    (* GMP_Decl added because translation seems to insert declarations inside statements 
        type is gmp_t because DECLS input is gmp_t
    *)
    (* | GMP_Decl (type: gmp_t) (name:id)  *)
.
#[global] Hint Constructors _gmp_statement  : rac_hint.
Definition gmp_routine := @_c_routine Empty_set _gmp_statement _gmp_t.


Declare Scope mini_gmp_scope.  
Delimit Scope mini_gmp_scope with gmp.
Declare Custom Entry gmp_stmt. 


Notation "e" := e (in custom gmp_stmt at level 0,  e constr at level 0) : mini_c_scope.
Notation "<( s )>" := s (at level 0, s custom gmp_stmt at level 99, format "<( s )>") : mini_gmp_scope.
Notation "'set_i' ( id , e )" := (Set_i id e) (in custom gmp_stmt) : mini_gmp_scope.
Notation "'set_s' ( id , l )" := (Set_s id l) (in custom gmp_stmt): mini_gmp_scope.
Notation "'set_z' ( id1 , id2 )" := (Set_z id1 id2) (in custom gmp_stmt): mini_gmp_scope.
Notation "'cl' ( id )" := (Clear id) (in custom gmp_stmt): mini_gmp_scope.
Notation "id = 'cmp' ( id1 , id2 )" := (Comp id id1 id2) (in custom gmp_stmt at level 99): mini_gmp_scope.
Notation "id = 'get_int' ( id1 )" := (Coerc id id1) (in custom gmp_stmt at level 99): mini_gmp_scope.
Notation "'init' ( id )" := (Init id) (in custom gmp_stmt) : mini_gmp_scope.
Notation "'add' ( id1 , id2 , id3 )" := (GMP_Add id1 id2 id3) (in custom gmp_stmt) : mini_gmp_scope.
Notation "'sub' ( id1 , id2 , id3 )" := (GMP_Sub id1 id2 id3) (in custom gmp_stmt) : mini_gmp_scope.
Notation "'mul' ( id1 , id2 , id3 )" := (GMP_Mul id1 id2 id3) (in custom gmp_stmt): mini_gmp_scope.
Notation "'div' ( id1 , id2 , id3 )" := (GMP_Div id1 id2 id3) (in custom gmp_stmt): mini_gmp_scope.
