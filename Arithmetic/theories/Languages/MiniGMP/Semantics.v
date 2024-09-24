From Coq Require Import Strings.String ZArith.ZArith BinaryString.
From RecordUpdate Require Import RecordUpdate.
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
            (forall v, ev v <> Some (Def (VMpz (Some l)))) ->
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

        | S_get_int x y ly zy (ir:Int.inRange zy) :
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

        | S_Scope decls (s:@c_statement _gmp_statement _gmp_t) ev_s ev_s':
            (*
                - A scope has var declarations that gets dropped at the end, except the memory state. 
                - This was missing in the original paper but required in the translation 
                as we must create a scope when we translate the assertions 
                - Note it complicate things because the statement are c instructions, not just gmp ones.
            *)
            declare_gmp_vars ev (list_to_ensemble decls) ev_s ->
            @generic_stmt_sem _gmp_statement _gmp_t _gmp_stmt_sem _gmp_stmt_vars fe ev_s s ev_s' -> 
            ev |= GMP_Scope decls s =>  ev <| mstate := ev_s' |>


    where "ev |= s => ev'" := (_gmp_stmt_sem fe (ev:Env) (s:_gmp_statement) (ev':Env)) : ext_gmp_stmt_sem_scope.

    Section Induction.

        (* Variable P : Env -> 𝐒 -> Env -> Prop.
        Variable P1 : forall x (l:location) u,
            (forall v, ev v <> Some (Def (VMpz (Some l)))) ->
            ev x = Some (Undef (UMpz u)) ->
            (ev |= <(init(x))> => ev <| env ; vars ::= {{x\Def (VMpz (Some l))}} |> <| mstate ::= {{l\Defined 0}} |>) f
        .
        
        Fixpoint _gmpt_stmt_sem_full_ind f ev s ev' (sem : (ev |= s => ev')%extgmpssem f) : P ev s ev' :=
        match s in (_gmp_stmt_sem _ _ g0 e0) return (P g0 e0) with
        | S_init _ _ x l u x0 x1 => P1 x l u x0 x1
        | S_clear _ _ x a u x0 => P2 x a u x0
        | S_set_i _ _ x y z a x0 x1 => P3 x y z a x0 x1
        | S_set_z _ _ x y z a n x0 x1 x2 => P4 x y z a n x0 x1 x2
        | S_get_int _ _ x y ly zy ir x0 x1 => P5 x y ly zy ir x0 x1
        | S_set_s _ _ s x zx lx x0 x1 => P6 s x zx lx x0 x1
        | S_cmp _ _ c x lx ly zx y zy b x0 x1 x2 x3 x4 =>
            P7 c x lx ly zx y zy b x0 x1 x2 x3 x4
        | S_op _ _ bop r lr x y lx ly zx zy x0 x1 x2 x3 x4 =>
            P8 bop r lr x y lx ly zx zy x0 x1 x2 x3 x4
        | S_Scope _ _ decls s ev_s ev_s' x x0 => P9 decls s ev_s ev_s' x x0
        end *)



    End Induction.

    Definition gmp_stmt_sem := @generic_stmt_sem _gmp_statement _gmp_t _gmp_stmt_sem _gmp_stmt_vars.

    Definition gmp_pgrm_sem := 
        @generic_pgrm_sem Empty_set _gmp_statement _gmp_t _gmp_stmt_sem _gmp_stmt_vars (fun _ => T_Ext Mpz)  build_rac_fenv.

End GMPSemantics.

Notation "ev |= s => ev'" := (fun f => gmp_stmt_sem f ev s ev') : gmp_stmt_sem_scope.


#[global] Hint Constructors _gmp_stmt_sem  : rac_hint.
