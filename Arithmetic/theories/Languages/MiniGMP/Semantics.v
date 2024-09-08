From Coq Require Import Strings.String ZArith.ZArith BinaryString.
From RecordUpdate Require Import RecordUpdate.
From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax.
From RAC.Languages Require Import MiniC.Semantics MiniGMP.Syntax.

Import RecordSetNotations FunctionalEnv.

Open Scope utils_scope.
Open Scope mini_c_scope.
Open Scope mini_gmp_scope.
Declare Scope gmp_stmt_sem_scope.
Delimit Scope gmp_stmt_sem_scope with gmpssem.


Inductive _gmp_stmt_sem  (f : @fenv _gmp_statement _gmp_t) (ev:Env) : gmp_statement -> Env -> Prop := 
    | S_init x (l:location) u:
        (forall v, ev v <> Some (Def (VMpz (Some l)))) ->
        ev x = Some (Undef (UMpz u)) ->
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
        ev.(mstate) n = Some (Defined z) ->
        (ev |= <(set_z(x,y))> => ev <| mstate ::= {{a\Defined z}} |>) f 

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
        (ev |= fsl_to_gmp_op bop r x y => ev <| mstate ::= {{lr\Defined (⋄ (□ bop) zx zy) }} |>) f

    | S_Scope d (s:@_c_statement _gmp_statement _gmp_t) ev_s:
        (*
            - A scope has var declarations that gets dropped at the end. 
            - This was missing in the original paper but required in the translation 
            as we must create a scope when we translate the assertions 
            - Note it complicate things because the statement are c instructions, not just gmp ones.
        *)
        @generic_stmt_sem _gmp_statement _gmp_t Empty_exp_sem _gmp_stmt_sem _gmp_stmt_vars f (add_gmp_decls d ev) s ev_s -> 
        (ev |= GMP_Scope d s =>  ev_s) f


where "ev |= s => ev'" := (fun f => _gmp_stmt_sem f ev s ev') : gmp_stmt_sem_scope.

#[global] Hint Constructors _gmp_stmt_sem  : rac_hint.


Definition gmp_stmt_sem := @generic_stmt_sem _gmp_statement _gmp_t Empty_exp_sem _gmp_stmt_sem _gmp_stmt_vars.
(*
Notation "Ω ⋅ M |= s => Ω' ⋅ M'"  := (fun f => gmp_stmt_sem f Ω M s Ω' M') : gmp_sem_scope. 
 *)


 Fact _no_mem_aliasing_gmp : _no_mem_aliasing _gmp_stmt_sem.
Proof with auto with rac_hint.
    intros exp_sem f ev s ev' Hnoalias H. induction H
    ; auto ;  try (rename v into l1) ;
    intros v v' ll l' Hvv' Hl Hl' leq ; subst ; autounfold with rac_hint in * ; simpl in *.
    - destruct (eq_dec x v).
        + subst. autounfold with rac_hint in *. rewrite p_map_same in Hl. rewrite p_map_not_same in Hl'... inversion Hl. 
            subst. now destruct H with v'.
        + rewrite p_map_not_same in Hl... destruct (eq_dec x v').
            * subst. rewrite p_map_same in Hl'. inversion Hl'. subst. now destruct H with v.
            * rewrite p_map_not_same in Hl'... destruct Hnoalias with v v' l' l'...
    - destruct (eq_dec x v).
        + subst. now rewrite p_map_same in Hl.
        + rewrite p_map_not_same in Hl... destruct (eq_dec l' a).
            * destruct Hnoalias with v x l' a... 
            * destruct (eq_dec x v').
                ** subst. rewrite p_map_same in Hl'... easy.
                ** rewrite p_map_not_same in Hl'... destruct Hnoalias with v v' l' l'...     
    - destruct (string_dec x v').
        + subst. rewrite p_map_same in Hl'. discriminate.
        + rewrite p_map_not_same in Hl'... destruct (string_dec x v).
            * subst. rewrite p_map_same in Hl... discriminate.
            * rewrite p_map_not_same in Hl... destruct Hnoalias with v v' l' l'...
    - assert (type_of_value (Some b) = Some C_Int). {
        destruct H3 as [sup [inf eq]]. destruct (Z.lt_trichotomy zx zy) as [Hinf | [Heq | Hsup]].
        - apply inf in Hinf. now subst.
        - apply eq in Heq. now subst.
        - apply Z.lt_gt in Hsup.  apply sup in Hsup. now subst. 
        } 
        destruct (string_dec c v').
        + subst. rewrite p_map_same in Hl'. injection Hl' as Hl'. now subst. 
        + rewrite p_map_not_same in Hl'... destruct (string_dec c v).
            * subst. rewrite p_map_same in Hl. injection Hl as Hl. now subst.
            * rewrite p_map_not_same in Hl... destruct Hnoalias with v v' l' l'...
    - admit.
Admitted.