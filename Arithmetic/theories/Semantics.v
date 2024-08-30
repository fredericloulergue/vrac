Require Import RAC.Definitions.
Require Import RAC.Notations.
Require Import RAC.Utils.
Require Import ZArith.ZArith.
From Coq Require Import Strings.String.
From Coq Require Import BinaryString.
Open Scope Z_scope.

Definition exp_sem_sig {T : Set} : Type := Env -> @_c_exp T -> 𝕍 -> Prop.
Definition stmt_sem_sig {S T: Set} : Type  :=  @fenv S T -> Env -> @_c_statement S T ->  Env -> Prop.
Definition Empty_exp_sem {T: Set} : @exp_sem_sig T := fun _ _ _ => False.
Definition Empty_stmt_sem {S T: Set} : @stmt_sem_sig S T := fun _ _ _ _ => False.

Declare Scope generic_exp_sem_scope.
Delimit Scope generic_exp_sem_scope with gesem.

(* extensible expression semantic *)
Inductive generic_exp_sem {T:Set} {ext_exp : @exp_sem_sig T} (ev:Env): @_c_exp T -> 𝕍 -> Prop :=
| C_E_Int (z:Z) irz : ev |= z => VInt (z ⁱⁿᵗ irz)
| C_E_Var (x:𝓥) z : 
    ev x = Some (Def (VInt z)) -> 
    ev |=  (C_Id x C_Int) => z
| C_E_BinOpInt e e' (z z':Z) op z_ir z'_ir
    (H:Int.inRange (⋄ op z z')) :
    ev |= e =>  VInt (z ⁱⁿᵗ z_ir) ->
    ev |= e' =>  VInt (z' ⁱⁿᵗ z'_ir) ->
    ev |=  BinOpInt e op e' => VInt ((⋄ op) z z' ⁱⁿᵗ H)
| C_E_BinOpTrue e e' (z z' : Z) z_ir z'_ir op :
    ev |= e => VInt (z ⁱⁿᵗ z_ir) ->
    ev |= e' => VInt (z' ⁱⁿᵗ z'_ir) ->
    (◁ op) z z' = true ->
    ev |= BinOpBool e op e' => VInt one
| C_E_BinOpFalse e e' (z z' : Z) op z_ir z'_ir :
    ev |= e => VInt (z ⁱⁿᵗ z_ir) -> 
    ev |= e' => VInt (z' ⁱⁿᵗ z'_ir) -> 
    ((◁ op) z z' = false ) ->
    ev |= BinOpBool e op e' => VInt zero
(* | C_Ext x v t: 
    (* variable must not be of type int (treated by C_E_Var) *)
    t <> C_Int ->
    
    (* variable must be bound and init *)
    ev x = Some (Def v) ->


    (* the external semantic can only add additional constraint, the result is always v *)
    ext_exp ev (C_Id x t) v ->

    ev |= (C_Id x t) => v *)

where  "env '|=' e => z" := (generic_exp_sem env e z) : generic_exp_sem_scope.

#[global] Hint Constructors generic_exp_sem  : rac_hint.


Declare Scope c_sem_scope.
Delimit Scope c_sem_scope with csem.


Definition c_exp_sem := @generic_exp_sem Empty_set Empty_exp_sem.

Notation "Ω '|=' e => v"  := (c_exp_sem Ω e v) : c_sem_scope.

Open Scope mini_c_scope.
From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.

Declare Scope generic_stmt_sem_scope.
Delimit Scope generic_stmt_sem_scope with gssem.

(* extensible statement semantic *)
Inductive generic_stmt_sem {S T: Set} {ext_exp: @exp_sem_sig T} {ext_stmt: @stmt_sem_sig S T} (f : @fenv S T) (ev:Env) : @_c_statement S T -> Env -> Prop := 
    | S_skip  :  (ev |= <{ skip }> => ev) f
    | S_Assign x z (e : @_c_exp T) : 
        (* must not be a compiler variable i.e. function return value *)
        is_comp_var x = false ->

        type_of_value (ev x) = Some C_Int ->
        (* value returned must be of same type*)
        type_of_value (Some z) = Some C_Int ->

        @generic_exp_sem T ext_exp ev e z -> 
        (ev |= <{x = e}> => (ev <| env ; vars ::= {{x\z}} |>)) f

    | S_IfTrue ev' z e s s' :
        @generic_exp_sem T ext_exp ev e z /\ ~ (z = VInt zero) ->
        (ev  |= s => ev') f ->
        (ev  |= <{ if e s else s'}> => ev') f

    | S_IfFalse ev' e s s' :
        @generic_exp_sem T ext_exp ev e (VInt zero) ->
        (ev |= s' => ev') f ->
        (ev |= <{ if e s else s'}> => ev') f

    | S_While e s  ev' :
        (ev |= <{ if e s ; while e s else skip }> => ev') f ->
        (ev |= <{ while e s }> => ev') f

    | S_Seq  ev' ev'' s s' :
        (ev |= s => ev') f ->
        (ev' |= s' => ev'') f ->
        (ev |= <{ s ; s' }> =>  ev'') f

    | S_FCall fname (b: @_c_statement S T) ev' c xargs eargs (zargs : 𝕍 ⃰ ) z : 
        List.length xargs = List.length eargs ->
        f.(funs) fname = Some (xargs,b) ->
        List.Forall2 (@generic_exp_sem T ext_exp ev) eargs zargs ->
        (empty_env <| env ; vars ::= p_map_addall_back xargs zargs |> |= b => ev') f -> 
        ~ List.In res_f (stmt_vars b) -> 
        ev' res_f = Some (Def z) -> (* must be a defined value *)
        (ev |= (FCall c fname eargs) => ev <| env ; vars ::= {{c\Def z}} |> <| mstate := ev' |>) f

    | S_PCall p b ev' xargs eargs zargs : 
        List.length xargs = List.length eargs ->
        f.(procs) p = Some (xargs,b) ->
        List.Forall2 (@generic_exp_sem T ext_exp ev) eargs zargs ->
        (empty_env <| env ; vars ::= p_map_addall_back xargs zargs |> |= b => ev') f -> 
        (ev |= PCall p eargs => ev <| mstate := ev' |>) f

    | S_Return e z : 
        (* not allowed to return an unassigned value *)
        @generic_exp_sem T ext_exp ev e (Def z) ->
        (ev |= <{ return e }> => ev <| env ; vars ::= {{res_f\Def z}} |>) f

    | S_PAssert  e z :
        @generic_exp_sem T ext_exp ev e z -> z <> VInt zero ->
        (ev |= <{ assert e }> => ev) f

    | S_ExtSem s ev' :  
        (* only S_Ext constructor allowed to use external semantic*)
        ext_stmt f ev (S_Ext s) ev' 
        -> (ev |= (S_Ext s) => ev') f
    
    where "env |= s => env'"  := (fun f => generic_stmt_sem f env s env') : generic_stmt_sem_scope.
    
#[global] Hint Constructors generic_stmt_sem  : rac_hint.


(* Declare Scope c_sem_scope.
Delimit Scope c_sem_scope with csem. 
Definition c_stmt_sem := @generic_stmt_sem Empty_set Empty_set Empty_exp_sem Empty_stmt_sem.
Notation "ev |= s => ev'"  := (c_stmt_sem ev s ev') : c_sem_scope. *)



(* Definition c_decl_sem (env env':Ω) (mem mem':𝓜) d : Prop := 
        forall x t u,
        env x  = None -> 
        (ty u) = Some t ->
        d = C_Decl t x -> env' = env <| vars ::= {{x\u}} |> /\ mem = mem'.
         *)


Open Scope mini_gmp_scope.
Declare Scope gmp_stmt_sem_scope.
Delimit Scope gmp_stmt_sem_scope with gmpssem.

Definition undef_type (u:undef) := match u with UMpz _ => Mpz | UInt _ => C_Int end.

Inductive _gmp_stmt_sem { S T : Set } (f : @fenv S T) (ev:Env) : gmp_statement -> Env -> Prop := 
    | S_init x (l:location):
        (forall v, ev v <> Some (Def (VMpz (Some l)))) ->
        (exists n, ev x = Some (Undef (UMpz n)))%type ->
        (ev |= <(init(x))> => ev <| env ; vars ::= {{x\Def (VMpz (Some l))}} |> <| mstate ::= {{l\Defined 0}} |>) f
    
    | S_clear x a u:   
        ev x = Some (Def (VMpz (Some a))) ->   
        (ev |= <(cl(x))> => ev <| env ; vars ::= {{x\(Def (VMpz None))}} |> <| mstate ::= {{a\Undefined u}} |>) f

    | S_set_i x y z a :  
        ev x = Some (Def (VMpz (Some a))) ->
        (ev |= y => VInt z)%csem ->
        (ev |= <(set_i(x,y))> => ev <| mstate ::= {{a\Defined (z ̇)}} |>) f

    | S_set_z x y z (a n : location) :  
        ev x = Some (Def (VMpz a)) ->
        ev y = Some (Def (VMpz n)) ->
        ev.(mstate) n = Some z ->
        (ev |= <(set_z(x,y))> => ev <| mstate ::= {{a\z}} |>) f 

    | S_get_int x y ly zy (ir:Int.inRange zy) :
        ev y = Some (Def (VMpz (Some ly))) ->
        ev.(mstate) ly = Some (Defined zy) -> 
        (ev |= <(x = get_int(y))> => ev <| env ; vars ::= {{x\VInt (zy ⁱⁿᵗ ir) : 𝕍}} |>) f

    | S_set_s s x zx lx :
        ev x = Some (Def (VMpz (Some lx))) ->
        BinaryString.to_Z s = zx ->
        (ev |= <(set_s(x,s))> => ev <| mstate ::= {{lx\Defined zx}} |> ) f

    | S_cmp c x (lx ly :location) zx y zy (b:𝕍):
        ev x = Some (Def (VMpz (Some lx))) ->
        ev y = Some (Def (VMpz (Some ly))) ->
        ev.(mstate) lx = Some (Defined zx) ->
        ev.(mstate) ly = Some (Defined zy) ->
        (
            (Z.gt zx zy <-> b = VInt one) /\
            (Z.lt zx zy <-> b = VInt sub_one) /\
            (Z.eq zx zy <-> b = VInt zero)
        ) ->
        (ev |= <(c = cmp(x,y))> => ev <| env ; vars ::= {{c\b}} |>) f
    
    | S_op bop r lr x y (lx ly : location) zx zy :
        ev x = Some (Def (VMpz (Some lx))) ->
        ev y = Some (Def (VMpz (Some ly))) ->
        ev.(mstate) lx = Some (Defined zx) ->
        ev.(mstate) ly = Some (Defined zy) ->
        ev r = Some (Def (VMpz (Some lr))) -> (* not in paper *)
        (ev |= op bop r x y => ev <| mstate ::= {{lr\Defined (⋄ (□ bop) zx zy) }} |>) f

where "ev |= s => ev'" := (fun f => _gmp_stmt_sem f ev s ev') : gmp_stmt_sem_scope.

#[global] Hint Constructors _gmp_stmt_sem  : rac_hint.




Definition gmp_stmt_sem := @generic_stmt_sem _gmp_statement _gmp_t Empty_exp_sem _gmp_stmt_sem.
(*
Notation "Ω ⋅ M |= s => Ω' ⋅ M'"  := (fun f => gmp_stmt_sem f Ω M s Ω' M') : gmp_sem_scope. 
 *)

Inductive fsl_term_sem (f: @fenv _fsl_statement Empty_set) (ev:Env) : ℨ -> Z -> Prop :=
    | S_T_Int z : fsl_term_sem f ev (T_Z z) z 
    
    | S_T_LVar x z : ev.(binds) x = Some z -> fsl_term_sem f ev (T_Id x FSL_Integer) z

    | S_T_Var x v : ev.(env) v = Some (Def (VInt x)) ->  fsl_term_sem f ev (T_Id v FSL_Int) x ̇ 

    | S_T_BinOpInt t t' z zint z' z'int op :  
        fsl_term_sem f ev t z ->
        fsl_term_sem f ev t' z' ->
        ~ (op = FSL_Div /\ z = 0)%type ->
        fsl_term_sem f ev (T_BinOp t op t') ((fsl_binop_int_model op) zint z'int)

    | S_T_CondTrue p t z t':
        fsl_pred_sem f ev p BTrue ->
        fsl_term_sem f ev t z ->
        fsl_term_sem f ev (T_Cond p t t') z

    |S_T_CondFalse p t t' z':
        fsl_pred_sem f ev p BFalse ->
        fsl_term_sem f ev t' z' ->
        fsl_term_sem f ev (T_Cond p t t') z'

    | S_T_Call fname b xargs targs zargs z :
        List.length xargs = List.length targs ->
        f.(lfuns) fname = Some (xargs,b) ->
        List.Forall2 (fsl_term_sem f ev) targs zargs ->
        fsl_term_sem f (empty_env <| env ; binds ::= p_map_addall_back xargs zargs |>) b z -> 
        fsl_term_sem f ev (T_Call fname targs) z 


with fsl_pred_sem (f: @fenv _fsl_statement Empty_set) (ev:Env) :  𝔅 -> 𝔹 -> Prop :=
    | S_P_True : fsl_pred_sem f ev P_True BTrue
    | S_P_False : fsl_pred_sem f ev P_False BFalse

    | S_P_BinOpTrue t t' z z' (op:fsl_binop_bool): 
        fsl_term_sem f ev t z ->
        fsl_term_sem f ev t' z' ->
        (fsl_binop_bool_model op) z z' ->
        fsl_pred_sem f ev (P_BinOp t op t) BTrue

    | S_P_BinOpFalse t t' z z' (op:fsl_binop_bool): 
        fsl_term_sem f ev t z ->
        fsl_term_sem f ev t' z' ->
        ~ (fsl_binop_bool_model op) z z' ->
        fsl_pred_sem f ev (P_BinOp t op t) BFalse

    | S_P_NotTrue p : 
        fsl_pred_sem f ev p BTrue ->
        fsl_pred_sem f ev (P_Not p) BFalse

    | S_P_NotFalse p : 
        fsl_pred_sem f ev p BFalse ->
        fsl_pred_sem f ev (P_Not p) BTrue 

    | S_P_DisjLeftTrue p p' : 
        fsl_pred_sem f ev p BTrue ->
        fsl_pred_sem f ev (P_Disj p p') BTrue 

    | S_P_DisjLeftFalse p p' z : 
        fsl_pred_sem f ev p BFalse ->
        fsl_pred_sem f ev p' z ->
        fsl_pred_sem f ev (P_Disj p p') z
    
    | S_P_Call p b xargs targs zargs z :
        List.length xargs = List.length targs ->
        f.(preds) p = Some (xargs,b) ->
        List.Forall2 (fsl_term_sem f ev) targs zargs ->
        fsl_pred_sem f (empty_env <| env ; binds ::= p_map_addall_back xargs zargs |>) b z -> 
        fsl_pred_sem f ev (P_Call p targs) z 
.

#[global] Hint Constructors fsl_term_sem : rac_hint.
#[global] Hint Constructors fsl_pred_sem : rac_hint.

Declare Scope fsl_sem_scope.
Delimit Scope fsl_sem_scope with fslsem.

(* Notation "Ω '|=' t => v" := (fsl_term_sem Ω t v) : fsl_sem_scope. *)

Inductive _fsl_assert_sem  (f : fenv ) (ev:Env) : fsl_statement -> Env -> Prop :=
| FSL_Assert (p:𝔅) : 
    fsl_pred_sem f ev p BTrue ->
    _fsl_assert_sem f ev (LAssert p) ev
.

#[global] Hint Constructors _fsl_assert_sem : rac_hint.


Definition fsl_stmt_sem := @generic_stmt_sem _fsl_statement Empty_set Empty_exp_sem _fsl_assert_sem.
Notation "ev |= s => ev'"  := (fun f => fsl_stmt_sem f ev s ev') : fsl_sem_scope. 



(* macro semantic, section E *)


Declare Scope macro_sem_scope.
Inductive macro_sem (ev:Env) (e:gmp_exp): Z -> Prop :=
| M_Int x : 
    ty e = C_Int -> 
    (ev |= gmp_exp_to_c_exp e => (VInt x))%csem ->
    ev |= e ⇝ x ̇
| M_Mpz l z : 
    ty e = Mpz ->
    ev (gmp_ty_mpz_to_var e) = Some (Def (VMpz (Some l))) ->
    ev.(mstate) l = Some (Defined z) ->
    ev |= e ⇝ z
where "ev '|=' e ⇝ z" := (macro_sem ev e z) : macro_sem_scope.

#[global] Hint Constructors macro_sem : rac_hint.



(* misc *)
Require Import Coq.Program.Equality. (* axiom eq_rect_eq *)

Fact ty_int_gmp_c_exp_equiv {ext_exp} (e:gmp_exp): forall env v, 
    ty e = C_Int -> 
    (env |= gmp_exp_to_c_exp e => v)%csem <-> generic_exp_sem env e v (ext_exp:=ext_exp).
Proof with eauto with rac_hint.
    intros env v Hint. split; intro H.
    - dependent induction H; destruct e eqn:E; simpl in *; subst; try congruence; injection x as Hz; subst.
        1,2: now constructor.
        1,2,3: destruct (ty g1) eqn:TG1; try discriminate ; destruct (ty g2) eqn:TG2; try discriminate...
    - induction H ; simpl in *.
        1,2: now repeat constructor.
        1,2,3: destruct (ty e) eqn:TE1; try discriminate ; destruct (ty e') eqn:TE2; try discriminate; econstructor.
        1,3,6: now apply IHgeneric_exp_sem1.
        1,2,4: now apply IHgeneric_exp_sem2.
        1,2: assumption.
Qed.
