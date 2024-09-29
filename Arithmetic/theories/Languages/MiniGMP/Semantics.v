From Coq Require Import ZArith.ZArith.
From Coq.Strings Require Import String BinaryString.

From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax.
From RAC.Languages Require Import MiniC.Semantics MiniGMP.Syntax.
 
Import RecordSetNotations FunctionalEnv.

#[local] Open Scope utils_scope.
#[local] Open Scope mini_c_scope.
#[local] Open Scope mini_gmp_scope.
Declare Scope ext_gmp_stmt_sem_scope.
Delimit Scope ext_gmp_stmt_sem_scope with extgmpssem.
Declare Scope gmp_stmt_sem_scope.
Delimit Scope gmp_stmt_sem_scope with gmpssem.

Definition declare_gmp_vars := @declare_vars _gmp_t (fun x => T_Ext Mpz).


Section GMPSemantics.
    Variable (fe: rac_prog_fenv).

    Inductive _gmp_stmt_sem  (fe:rac_prog_fenv) (ev:Env) :  gmp_statement -> Env -> Prop := 
        | S_init x (l:location) u:
            fresh_location ev l ->
            ev x = Some (Undef (UMpz u)) ->
            ev |= <(init(x))> => ev <| env ; vars ::= {{x\Def (VMpz (Some l))}} |> <| mstate ::= {{l\Defined 0}} |>
        
        | S_clear x a u:   
            ev x = Some (Def (VMpz (Some a))) ->   
            ev |= <(cl(x))> => ev <| env ; vars ::= {{x\(Def (VMpz None))}} |> <| mstate ::= {{a\Undefined u}} |>

        | S_set_i x y z a :  
            ev x = Some (Def (VMpz (Some a))) ->
            (ev |= y => VInt z)%csem ->
            ev |= <(set_i(x,y))> => ev <| mstate ::= {{a\Defined (z ̇)}} |>

        | S_set_z x y z (a n : location) :  
            ev x = Some (Def (VMpz a)) ->
            ev y = Some (Def (VMpz n)) ->
            ev.(mstate) n = Some (Defined z) ->
            ev |= <(set_z(x,y))> => ev <| mstate ::= {{a\Defined z}} |> 

        | S_get_int x y ly zy (ir:MI.inRange zy) :
            ev y = Some (Def (VMpz (Some ly))) ->
            ev.(mstate) ly = Some (Defined zy) -> 
            ev |= <(x = get_int(y))> => ev <| env ; vars ::= {{x\VInt (zy ⁱⁿᵗ ir) : 𝕍}} |>

        | S_set_s s x zx lx :
            ev x = Some (Def (VMpz (Some lx))) ->
            BinaryString.to_Z s = zx ->
            ev |= <(set_s(x,s))> => ev <| mstate ::= {{lx\Defined zx}} |> 

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
            ev |= <(c = cmp(x,y))> => ev <| env ; vars ::= {{c\b}} |>
        
        | S_op bop r lr x y (lx ly : location) zx zy :
            ev x = Some (Def (VMpz (Some lx))) ->
            ev y = Some (Def (VMpz (Some ly))) ->
            ev.(mstate) lx = Some (Defined zx) ->
            ev.(mstate) ly = Some (Defined zy) ->
            ev r = Some (Def (VMpz (Some lr))) -> (* not in paper *)
            ev |= fsl_to_gmp_op bop r x y => ev <| mstate ::= {{lr\Defined (⋄ (□ bop) zx zy) }} |>


    where "ev |= s => ev'" := (_gmp_stmt_sem fe (ev:Env) (s:_gmp_statement) (ev':Env)) : ext_gmp_stmt_sem_scope.

    Definition gmp_stmt_sem := @generic_stmt_sem _gmp_statement _gmp_t _gmp_stmt_sem _gmp_used_stmt_vars (fun _ => T_Ext Mpz).

    Definition gmp_pgrm_sem := 
        @generic_pgrm_sem Empty_set _gmp_statement _gmp_t _gmp_stmt_sem _gmp_used_stmt_vars (fun _ => T_Ext Mpz)  build_rac_fenv.

End GMPSemantics.

Notation "ev |= s => ev'" := (fun f => gmp_stmt_sem f ev s ev') : gmp_stmt_sem_scope.


#[global] Hint Constructors _gmp_stmt_sem  : rac_hint.
