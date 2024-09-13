From Coq Require Import List.
From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax.
From RAC.Languages Require Export MiniC.Semantics MiniGMP.Semantics MiniFSL.Semantics.

#[local] Open Scope c_sem_scope.
#[local] Open Scope utils_scope.


Import FunctionalEnv Domain.

Fixpoint flatten {S T}  (s: @_c_statement S T) : list (@_c_statement S T) := match s with
| Seq s1 s2 => flatten s1 ++ flatten s2
| Skip => nil
| _ => s::nil
end
.

Definition unflatten {S T}  : list (@_c_statement S T) -> @_c_statement S T := fun l =>
    List.fold_left (fun new_s  s => Seq new_s s) l Skip
.


(* [between left x right s] means [x] is between [left] and [right] inside [s] *)

Inductive between : gmp_statement -> gmp_statement -> gmp_statement -> gmp_statement ->  Prop :=
| Between_base : forall s1 s s2 s_whole, 
    flatten s_whole = flatten s1 ++ flatten s ++ flatten s2 -> 
    between s1 s s2 s_whole
| Between_add_l s1 s_whole : forall s1' s s2 s_whole',
    between s1 s s2 s_whole ->
    flatten s_whole' = flatten s1'++ flatten s_whole ->
    between s1' s s2 s_whole'

| Between_add_r s2 s_whole : forall s1 s  s2' s_whole',
    between s1 s s2 s_whole ->
    flatten s_whole' = flatten s_whole ++ flatten s2' ->
    between s1 s s2' s_whole' 
.



Definition In_stmt {S T} (s s' : @_c_statement S T) : Prop := List.In s (flatten s').


Definition Forall_routines {F S T } (pgrm : @_c_program F S T) 
    (PFuns : @_c_decl T * -> @_c_decl T * -> @_c_statement S T  -> Prop)
    (* (PLFun : fsl_statement -> Prop)
    (PPred : fsl_statement -> Prop) *)
    : Prop :=
    List.Forall (fun f => match f with
        | PFun _ _ args decls body => PFuns args decls body
        (* | F_Ext (LFun _ _ _ _) => True
        | F_Ext (Predicate _ _ _) => True *)
        | _ => True
        end
    ) (snd pgrm)
.


(* 
    well_formed_program :
    - all variables declared before usage
    - all functions defined before called
    - well typed
*)
Definition well_formed_pgrm (P : fsl_pgrm) (env : Env) (fenv: @fenv _fsl_statement Empty_set) := 
    Forall_routines P ( fun args decls b =>
        (* all used variables are declared *)
        (forall v, List.In v (fsl_stmt_vars b) -> v ∈ env) /\ 
        (* all functions are defined before being called *)
        (forall rvar fname args, 
            @In_stmt _fsl_statement Empty_set (FCall rvar fname args) b -> 
            fname ∈ fenv.(funs)
        
        ) /\
        True (* fixme: well typed ? *)
    )
.