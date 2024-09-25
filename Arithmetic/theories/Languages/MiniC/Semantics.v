From Coq Require Import Strings.String ZArith.ZArith Sets.Ensembles.

From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax.
From RAC.Environnement Require Import Facts.


Import RecordSetNotations.


Declare Scope c_sem_scope.
Delimit Scope c_sem_scope with csem.

Declare Scope generic_stmt_sem_scope.
Delimit Scope generic_stmt_sem_scope with gssem.

Declare Scope generic_exp_sem_scope.
Delimit Scope generic_exp_sem_scope with gesem.


#[local] Open Scope utils_scope.
#[local] Open Scope mini_c_scope.


Import FunctionalEnv Domain.


Definition compiler_prefix : id := "_".
Definition comp_var x : id  := (compiler_prefix ++ x)%string.
Definition is_comp_var := String.prefix compiler_prefix.
Definition res_f : id := comp_var "res".



Section GenericSemantics.
    Context {F S T : Set}.

    Notation c_type      := (@c_type T).
    Notation c_exp       := (@c_exp T).
    Notation c_statement := (@c_statement S T).
    Notation c_decl      := (@c_decl T).
    Notation c_routine   := (@c_routine F S T).
    Notation c_program   := (@c_program F S T).
    Notation fenv        := (@fenv S T).

    Definition generic_exp_sem_sig  (_:Env) : Type := c_exp -> 𝕍 -> Prop.
    Definition generic_stmt_sem_sig  (_:fenv) (_:Env) : Type := c_statement -> Env -> Prop.

    Definition Empty_exp_sem e : generic_exp_sem_sig e := fun _ _ => False.
    Definition Empty_stmt_sem f e : generic_stmt_sem_sig f e := fun _ _ => False.

    Variable (ext_exp_sem : forall e, generic_exp_sem_sig e) (ext_stmt_sem : forall f e, generic_stmt_sem_sig f e).
    
    Variable (rel : Env -> Env -> Prop).
    Variable (rel_s : Env -> Env -> σ -> Prop).

    Context {ext_stmt_vars : S -> StringSet.t} {ext_ty_val: 𝕍 -> c_type} .

    Section FunctionsEnv.

        Context {fe: fenv}.

        (* extensible expression semantic *)
        Inductive generic_exp_sem ev : generic_exp_sem_sig ev :=
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
        

        Definition generic_call_sem  
            {g_exp_s : forall e, generic_exp_sem_sig e}
            {g_stmt_s : forall e, generic_stmt_sem_sig fe e}
            (prj: fenv -> _)  (ev body_init_env:Env) name xargs eargs zargs b b_ev :=

            List.length xargs = List.length eargs /\
            let vargs := List.map (fun x => Def (VInt x)) zargs in 
            StringMap.find name (prj fe) = Some (xargs,b) /\
            List.Forall2 (g_exp_s ev) eargs vargs /\
            g_stmt_s (body_init_env <| env ; vars ::= p_map_addall_back xargs vargs |>) b b_ev.


        (* extensible statement semantic *)
        Inductive generic_stmt_sem ev : generic_stmt_sem_sig fe ev := 

        | S_Skip  :  (ev |= <{ skip }> => ev)
        | S_Assign x (z: Int.MI) (e : c_exp) : 
            (* must not be a compiler variable i.e. function return value *)
            is_comp_var x = false ->

            type_of_value (ev x) = Some C_Int ->
            generic_exp_sem ev e z -> 
            ev |= <{(Assign x e)}> => (ev <| env ; vars ::= {{x\Def z}} |>)

        | S_IfTrue ev' (z : Int.MI) e s s' :
            generic_exp_sem ev e z /\ ~ (z = VInt zero) ->
            ev  |= s => ev' ->
            ev  |= <{ if e s else s'}> => ev'

        | S_IfFalse ev' e s s' :
            @generic_exp_sem ev e (VInt zero) ->
            ev |= s' => ev' ->
            ev |= <{ if e s else s'}> => ev'

        | S_While e s  ev' :
            ev |= <{ if e s ; while e s else skip }> => ev' ->
            ev |= <{ while e s }> => ev'

        | S_Seq  ev' ev'' s s' :
            ev |= s => ev' ->
            ev' |= s' => ev'' ->
            ev |= <{ s ; s' }> =>  ev''

        | S_FCall fname b b_ev xargs eargs (zargs : Int.MI★) c z : 
            @generic_call_sem generic_exp_sem generic_stmt_sem 
            funs ev empty_env fname xargs eargs zargs b b_ev ->

            ~ StringSet.In res_f (stmt_vars b ext_stmt_vars) -> 
            b_ev res_f = Some (Def (VInt z)) -> (* must be a defined integer value *)
            ev |= FCall c fname eargs => ev <| env ; vars ::= {{c\Def z}} |> <| mstate := b_ev |>

        | S_PCall pname b b_ev xargs eargs (zargs : Int.MI★) : 
            @generic_call_sem generic_exp_sem generic_stmt_sem
            procs ev empty_env pname xargs eargs zargs b b_ev ->

            ev |= PCall pname eargs => ev <| mstate := b_ev |>

        | S_Return e (z: Int.MI) : 
            generic_exp_sem ev e (Def (VInt z)) ->
            ev |= <{ return e }> => ev <| env ; vars ::= {{res_f\Def (VInt z)}} |>

        | S_PAssert e (z: Int.MI) :
            generic_exp_sem ev e z -> z <> VInt zero ->
            ev |= <{ assert e }> => ev

        | S_ExtSem s ev' :  
            (* only S_Ext constructor allowed to use external semantic*)
            ext_stmt_sem fe ev (S_Ext s) ev' 
            -> ev |= (S_Ext s) => ev'

        where "env |= s => env'"  := (generic_stmt_sem env s env') : generic_stmt_sem_scope.


        Section Induction.

        Variable P :  Env -> c_statement -> Env -> Prop.
        Variable P1 : forall ev, P ev <{skip}> ev.
        Variable P2 : forall (ev : Env) (x : id) (z : Int.MI) (e : c_exp),
            is_comp_var x = false ->
            type_of_value (ev x) = Some C_Int ->
            (ev |= e => z)%gesem ->
            P ev (Assign x e) (ev <| env; vars ::= {{x \Def z}} |>)
        .

        Variable P3 : forall (ev ev' : Env) (z : Int.MI) (e : c_exp) (s : c_statement) (s' : Syntax.c_statement),
            (ev |= e => z)%gesem /\ z <> zero ->
            (ev |= s => ev')%gssem -> P ev s ev' -> P ev <{if e s else s'}> ev'
        .
        Variable P4 : forall (ev ev' : Env) (e : c_exp) (s s' : c_statement),
            (ev |= e => zero)%gesem ->
            (ev |= s' => ev')%gssem -> P ev s' ev' -> P ev <{if e s else s'}> ev'
        .
        Variable P5 :  forall (ev : Env) (e : c_exp) (s : c_statement) (ev' : Env),
            (ev |= <{if e s; while e s else skip}> => ev')%gssem ->
            P ev <{if e s; while e s else skip}> ev' -> P ev <{while e s}> ev'
        .
        Variable P6 : forall (ev ev' ev'' : Env) (s s' : c_statement),
            (ev |= s => ev')%gssem ->
            P ev s ev' ->
            (ev' |= s' => ev'')%gssem -> 
            P ev' s' ev'' -> 
            P ev <{s; s'}> ev''
        .
        Variable P7 : forall (ev : Env) (fname : StringMap.key) (b : c_statement) (b_ev : Env) (xargs : 𝓥★) (eargs : c_exp★) (zargs : Int.MI★) (c : id)  (z : Int.MI),
            (* inlining of generic_call_sem *)
            List.length xargs = List.length eargs ->
            let vargs := List.map (fun x => Def (VInt x)) zargs in 
            StringMap.find fname fe.(funs) = Some (xargs,b) ->
            List.Forall2 (generic_exp_sem ev) eargs vargs ->
            generic_stmt_sem (empty_env <| env ; vars ::= p_map_addall_back xargs vargs |>) b b_ev ->
            P  (empty_env <| env ; vars ::= p_map_addall_back xargs vargs |>) b b_ev ->
            ~ StringSet.In res_f (stmt_vars b ext_stmt_vars) ->
            b_ev res_f = Some (Def z) ->
            P ev (FCall c fname eargs) (ev <| env; vars ::= {{c \Def z}} |> <| mstate := b_ev |>)
        .
        Variable P8 : forall (ev : Env) (pname : StringMap.key) 
          (b : c_statement) (b_ev : Env) (xargs : 𝓥★) 
          (eargs : c_exp★) (zargs : Int.MI★),
            (* inlining of generic_call_sem *)
            List.length xargs = List.length eargs ->
            let vargs := List.map (fun x => Def (VInt x)) zargs in 
            StringMap.find pname fe.(procs) = Some (xargs,b) ->
            List.Forall2 (generic_exp_sem ev) eargs vargs ->
            generic_stmt_sem (empty_env <| env ; vars ::= p_map_addall_back xargs vargs |>) b b_ev ->
            P (empty_env <| env ; vars ::= p_map_addall_back xargs vargs |>) b b_ev ->
            P ev (PCall pname eargs) (ev <| mstate := b_ev |>)
        .

        Variable P9 : forall (ev : Env) (e : c_exp) (z : Int.MI),
            (ev |= e => z)%gesem ->
            P ev <{return e}> (ev <| env; vars ::= {{res_f \Def z}} |>)
        .
        Variable P10 : forall (ev : Env) (e : c_exp) (z : Int.MI),
        (ev |= e => z)%gesem -> z <> zero -> P ev <{assert e}> ev
        .
        Variable P11 : forall (ev : Env) (s : S) (ev' : Env),
            ext_stmt_sem fe ev (S_Ext s) ev' -> P ev (S_Ext s) ev'
        .


        Fixpoint generic_stmt_sem_full_ind  ev s ev' (sem : (ev |= s => ev')%gssem) : P ev s ev' := match sem with
        | S_Skip _ => P1 ev
        | S_Assign _ x z Hcomp Hty Hesem Hsem => P2 ev x z Hcomp Hty Hesem Hsem
        | S_IfTrue _ ev' z e0 s s' a g0 => P3 ev ev' z e0 s s' a g0 (generic_stmt_sem_full_ind ev s ev' g0)
        | S_IfFalse _ ev' e0 s s' g0 g1 => P4 ev ev' e0 s s' g0 g1 (generic_stmt_sem_full_ind ev s' ev' g1)
        | S_While _ e0 s ev' g0 => P5 ev e0 s ev' g0 (generic_stmt_sem_full_ind ev <{if e0  s; while e0 s else  skip}> ev' g0)
        | S_Seq _ ev' ev'' s s' g0 g1 => P6 ev ev' ev'' s s' g0 (generic_stmt_sem_full_ind ev s ev' g0) g1 (generic_stmt_sem_full_ind ev' s' ev'' g1)
        | S_FCall _ fname b b_ev xargs eargs zargs c0 z (conj H1 (conj H2 (conj H3 H4))) n e0 => 
            let vargs := List.map (fun x => Def (VInt x)) zargs in
            P7 ev fname b b_ev xargs eargs zargs c0 z H1 H2 H3 H4 (generic_stmt_sem_full_ind (empty_env <| env ; vars ::= p_map_addall_back xargs vargs |>) b b_ev H4) n e0
        | S_PCall _ pname b b_ev xargs eargs zargs (conj H1 (conj H2 (conj H3 H4))) => 
            let vargs := List.map (fun x => Def (VInt x)) zargs in
            P8 ev pname b b_ev xargs eargs zargs H1 H2 H3 H4 (generic_stmt_sem_full_ind (empty_env <| env ; vars ::= p_map_addall_back xargs vargs |>) b b_ev H4)
        | S_Return _ e0 z g0 => P9 ev e0 z g0
        | S_PAssert _ e0 z g0 n => P10 ev e0 z g0 n
        | S_ExtSem _ s ev' s0 => P11 ev s ev' s0
        end
        .
        End Induction.



        Inductive generic_decl_sem  (ev:Env) : c_decl -> Env -> Prop :=
        | D_Decl x (t: c_type) u:
            ev.(vars) x  = None -> 
            _type_of_value ext_ty_val (Some (Undef u)) = Some t ->
            generic_decl_sem ev (C_Decl t x) (ev <| env ;vars ::= {{x\Undef u}} |>)
        .



        Inductive declare_vars (e : Env) : Ensemble c_decl -> Env -> Prop :=
        | DV_nil : 
            declare_vars e (Empty_set _) e

        | DV_cons decls d e': 
            generic_decl_sem e d e' -> 
            declare_vars e (Add _ decls d) e'
        .



        Definition _untouched_var_same_eval_exp : Prop := 
            forall (ev:Env) e v x,
            ~ StringSet.In v (exp_vars e) -> 
            generic_exp_sem ev e x ->
            (forall x', ext_exp_sem (ev <| env ; vars ::= {{v\x'}} |>)  e x)
            /\ 
            (forall l z', 
            no_aliasing ev ->
            ev v = Some (Def (VMpz (Some l))) -> generic_exp_sem (ev <| mstate ::= {{l\z'}} |>) e x)
        .

        Definition _untouched_var_same_eval_stmt : Prop := 
            forall ev ev' s x, 
            ext_stmt_sem fe ev s ev' ->
            ~ StringSet.In x (stmt_vars s ext_stmt_vars) /\ is_comp_var x = false -> 
            ev x = ev' x
        .

        Definition _no_mem_aliasing : Prop := 
            forall (ev:Env) s (ev':Env), 
            no_aliasing ev
            -> ext_stmt_sem fe ev s ev' 
            -> no_aliasing ev'
        .

        Definition _determinist_exp_eval : Prop := 
            forall e ev v, ext_exp_sem ev e v ->  
            forall v', ext_exp_sem ev e v' -> v = v'
        .


        Definition _determinist_stmt_eval : Prop := 
            _determinist_exp_eval -> 
            forall s ev ev',  ext_stmt_sem fe ev s ev' ->  
            forall ev'', ext_stmt_sem fe ev s ev'' -> ev' = ev''
        .

        Definition _LC1_weakening_of_expression_semantics : Prop := 
            forall e ev (x:𝕍), 
            ext_exp_sem ev e x <-> (forall ev', rel ev ev' -> ext_exp_sem ev' e x)
        .

        Definition _LC21_weakening_of_statement_semantics : Prop := 
            (*
            should be in both directions according to the article but right to left does not work :
            We will see if the 'bad' direction is used in the proof 
            If this is the cast, one direction is trying to add to have a new env_01 = ev_0 + a and a new env_02 = ev_0 + b so that 
                (ev0 + a) inter ev0 + b) = ev1
            *)  
            _LC1_weakening_of_expression_semantics  ->
            forall ev₀ s ev₁,
            ext_stmt_sem fe ev₀ s ev₁ ->
            ( forall ev₀' sub, rel_s ev₀ ev₀' sub ->
                exists ev₁', 
                rel_s ev₁ ev₁' sub /\ ext_stmt_sem fe ev₀' s ev₁')
        .

        Definition _LC22_weakening_of_statement_semantics : Prop := 
            _LC1_weakening_of_expression_semantics ->
            forall ev₀ ev₀' s ev₁ sub,
            ext_stmt_sem fe ev₀ s ev₁ /\ rel_s ev₀ ev₀' sub  ->
            (
                forall ev₁',
                ext_stmt_sem fe ev₀' s ev₁'->
                (* if v is a compiler variable, i.e. a function return value, v can change*)
                (forall (v:𝓥), (v ∉ ev₀) /\ is_comp_var v = false  -> ev₀' v = ev₁' v)%dom_
                /\
                (forall (x:location), (forall v, ev₀ v <> Some (Def (VMpz x))) -> ev₀'.(mstate) (proj1_sig sub x) = ev₁'.(mstate) (proj1_sig sub x))
            )
        .

        (* required to prove _LC23_weakening_of_statement_semantics *)
        Definition _LC1_weakening_of_expression_semantics_3 : Prop := 
            forall ev e z sub,
            ext_exp_sem ev e z ->
            
            forall ev', rel_s ev' ev sub ->
            (
                (forall v, (dom ev - dom ev') v -> ~ StringSet.In v (exp_vars e))
                /\
                (forall x, (dom ev.(mstate) - dom ev'.(mstate)) x -> (exists v, ev v = Some (induced (proj1_sig sub) (Def (VMpz x))) /\ ~ StringSet.In v (exp_vars e)))
            )%dom_ ->

            ext_exp_sem  ev' e z
        .

        Definition _LC23_weakening_of_statement_semantics : Prop := 
            forall ev₀  s ev₁ sub,
            ext_stmt_sem fe ev₀ s ev₁ -> 

            forall ev₀', rel_s ev₀' ev₀ sub ->
            (
                (forall v, (dom ev₀ - dom ev₀') v -> ~ StringSet.In v (stmt_vars s ext_stmt_vars))
                /\
                (
                    forall x, (dom ev₀.(mstate) - dom ev₀'.(mstate)) x -> 
                    (exists v, ev₀ v = Some (induced (proj1_sig sub) (Def (VMpz x))) 
                    /\ ~ StringSet.In v (stmt_vars s ext_stmt_vars))
                )
            )%dom_ ->

            exists ev₁', ext_stmt_sem fe ev₀' s ev₁'
        .

    End FunctionsEnv.

    Inductive generic_pgrm_sem {build_fenv : @c_routine★ -> fenv} (ev:Env) (P : c_program) : Env -> Prop :=

    | P_Pgrm b z ev_decls b_ev:

        (* add global declarations to the env *)
        declare_vars ev (list_to_ensemble (fst P)) ev_decls ->

        (* add all functions to fenv *)
        let fe := build_fenv (snd P) in

        (** call the main function with the given parameters 
            (same as function call except the evaluation env for the body is not initially empty and we keep the whole final env) 
        *) 
        @generic_call_sem fe generic_exp_sem (fun e => @generic_stmt_sem fe e)
        funs ev ev_decls "main"%string nil nil nil b b_ev ->


        ~ StringSet.In res_f (stmt_vars b ext_stmt_vars) -> 
        b_ev res_f = Some (Def (VInt z)) -> (* must return a defined integer value *)
        generic_pgrm_sem ev P b_ev
    .

End GenericSemantics.


Fact weakening_of_empty_expression_semantics {T} : 
    @_LC1_weakening_of_expression_semantics T (@Empty_exp_sem T) exist_env_mem_partial_order. 
Proof.
    unfold _LC1_weakening_of_expression_semantics. intros. split ; unfold Empty_exp_sem.
    - intros [].
    - intro H. apply H with ev... apply refl_env_mem_partial_order.
Qed.


Fact weakening_of_empty_statement_semantics_1 {S T} rel rel_s f exp_sem:
    @_LC21_weakening_of_statement_semantics S T exp_sem (@Empty_stmt_sem S T) rel rel_s f.
Proof.
    easy. 
Qed.


Fact weakening_of_empty_statement_semantics_2 {S T} rel rel_s f exp_sem: 
    @_LC22_weakening_of_statement_semantics S T exp_sem (@Empty_stmt_sem S T) rel rel_s f.
Proof. 
    easy. 
Qed.


Fact weakening_of_empty_expression_semantics_3 {T} rel : 
    @_LC1_weakening_of_expression_semantics_3 T (@Empty_exp_sem T) rel.
Proof. 
    easy.
Qed.


Fact weakening_of_empty_statement_semantics_3 {S T} rel rel_s stmt_vars :
    @_LC23_weakening_of_statement_semantics S T (@Empty_stmt_sem S T)  rel rel_s stmt_vars.
Proof. 
    easy. 
Qed.


Definition c_exp_sem :=  @generic_exp_sem Datatypes.Empty_set.
Notation "Ω '|=' e => v"  := (c_exp_sem Ω e v) : c_sem_scope.


#[global] Hint Constructors generic_exp_sem : rac_hint.
#[global] Hint Constructors generic_stmt_sem : rac_hint.
