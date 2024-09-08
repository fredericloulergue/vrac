From Coq Require Import List String BinaryString ZArith.
From MMaps Require Import MMaps.
From RecordUpdate Require Import RecordUpdate.
From RAC Require Import Utils Environnement Macros Oracle.
From RAC.Languages Require Import Syntax Semantics.

Import ListNotations.
Import RecordSetNotations.

Export CounterMonad.

Open Scope string_scope.
Open Scope mini_c_scope.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope mini_gmp_scope.


Definition var_list := (𝓥 ⨉ gmp_t)*.

(* helper functions *)
Definition DECLS (vars:var_list) : list gmp_decl := (* generates declarations *)
    List.fold_right (
        fun (v:𝓥 ⨉ _) decls  => 
            let (s,t) := v in 
            (C_Decl t s) :: decls
    ) [] vars .

Definition INITS (vars : var_list) : gmp_statement := (* generates initialization *)
    List.fold_right 
    (
        fun (v:𝓥 ⨉ _) a => let (z,t) := v in 
        match t with
        | C_Int => a
        | T_Ext Mpz => 
            let init : gmp_statement  := <( init(z) )> in 
            <{init ; a}>  
        | _ => Skip (* cannot happen  *)
        end      
    ) Skip vars.

Definition CLEARS (vars : var_list) : gmp_statement := (* generates deallocation *)
List.fold_right 
(
    fun (v:𝓥 ⨉ _) a => let (z,t) := v in 
    match t with
    | T_Ext Mpz =>
        let cl : gmp_statement := <( cl(z) )> in 
        <{cl  ; a }>
    | C_Int | _  => a
    end        
) Skip vars.



Module Translation (Oracle : Oracle).
    Import Oracle FunctionalEnv.

    Definition Γᵥ := 𝔏 ⇀ 𝓥 ⨉ 𝐼. (* environment for logic bindings : variable and interval infered from it *)


    Definition Γ := Γᵥ ⨉ Γᵢ.
    Notation "'Γ' '(' x ')' " := (Γᵥ x, Γᵢ x).


    Module 𝐼_as_OT <: OrderedType := PairOrderedType(Z_as_OT)(Z_as_OT).  
    (* maps of ordered maps over ordered type are ordered *)
    Module TypingEnv_as_OT <: OrderedType := StringEnv.Decidable(𝐼_as_OT).
    (* we get an ordered type for the product of 𝔏 and  StringEnv.t *)
    Module String_TypingEnv_as_OT <: OrderedType := PairOrderedType(String_as_OT)(TypingEnv_as_OT).
    (* finally, we get our environnement of global definitions *)
    Module GlobalDef := MMapsEnv(String_TypingEnv_as_OT).
    Definition ψ : Type :=  GlobalDef.t 𝓥.  (* ψ(id,tenv) returns the name of the specialized version of [id] for [tenv] *)



    Record translation_result {T : Type} := mkTR
    {
        chunk: T ;  (* code chunk  resulting of the translation *)
        tenv: ψ; (* global definitions i.e. routines generated by the translation *)
        glob:gmp_routine*; (* mini-c globals generated during translation (global var + routine) *)
    }.
    #[export] Instance etaTR {T : Type}: Settable _ := settable! (mkTR T) <chunk;tenv;glob>.


    Record translated_statement {T: Type} := mkSTR
    {
        tr : @translation_result T;

        (* fresh variables generated by the translation *)
        decls: var_list ;

        (* variable containing the result *)
        (* can't just be the varname because CMP expects an expression as 2nd and 3rd param 
            so we need both the id and type.
            Even though we only use C_Int most of the time, the oracle outputs gmp_t so it must be gmp_t
        *)
        res: 𝓥  ⨉ gmp_t;
    }.
    #[export] Instance etaSTR {T : Type}: Settable _ := settable! (mkSTR T) <tr;decls;res>.


    Definition fresh_variable :=  c <- fresh ;;; ("_v" ++ string_of_nat c)%string. 

    Definition fresh_fname id :=  c <- fresh ;;; ("_id" ++ id ++ string_of_nat c)%string. 


    (* Since predicates are evaluated to 0 or 1, their result always fits in an int.*)


    Fixpoint translate_predicate (f : fenv) (bindings:Γᵥ) (t_env:Γᵢ) (e: ψ) (p : predicate) (fuel:nat) : state  := 
    match fuel with 
    | O => 
        (* fixme: use error monad (out of fuel) *)
        ret (mkSTR gmp_statement (mkTR gmp_statement Skip e nil) nil  ("",C_Int))  
    | S n =>

        match p with
        | P_True => 
            c <- fresh_variable ;;
            let decl := [(c,C_Int)] in
            let code := <{ c = 1 }> in
            ret (mkSTR gmp_statement (mkTR gmp_statement code e nil) decl (c,C_Int))
        | P_False => 
            c <- fresh_variable ;; 
            let decl := [(c,C_Int)] in
            let code := <{ c = 0 }> in
            ret (mkSTR gmp_statement (mkTR gmp_statement code e nil) decl  (c, C_Int))

        | P_Not p => 
            c <- fresh_variable ;; 
            p_tr <- translate_predicate f bindings t_env e p n ;;;
            let _res := C_Id (fst p_tr.(res)) (snd p_tr.(res)) in
            let decl := (c,C_Int)::p_tr.(decls) in
            let code := <{ (p_tr.(tr).(chunk gmp_statement)) ; if _res c = 0 else c = 1 }> in
            mkSTR gmp_statement (mkTR gmp_statement code p_tr.(tr).(tenv gmp_statement) nil) decl (c, C_Int)
        
        | P_Disj p1 p2 => 
            c <- fresh_variable ;;
            tr_p1 <- translate_predicate f bindings t_env e p1 n ;;
            let p1_res := C_Id (fst tr_p1.(res)) (snd tr_p1.(res)) in
            let p1_code := tr_p1.(tr).(chunk gmp_statement) in
            tr_p2 <- translate_predicate f bindings t_env tr_p1.(tr).(tenv gmp_statement) p2  n;;;
            let p2_res := C_Id (fst tr_p2.(res)) (snd tr_p2.(res)) in
            let p2_code := tr_p2.(tr).(chunk gmp_statement) in
            let decl := (c,C_Int)::tr_p1.(decls) ++ tr_p2.(decls) in
            let code := <{ p1_code ; if p1_res c = 1 else <{ p2_code ; <{c = p2_res}> }> }> 
            in
            mkSTR gmp_statement (mkTR gmp_statement code tr_p2.(tr).(tenv gmp_statement) nil) decl  (c,C_Int)

        | P_BinOp t1 fsl_op t2 =>
            c <- fresh_variable ;;

            tr_t1 <- translate_term f bindings t_env e t1 n ;;
            let t1_code := tr_t1.(tr).(chunk gmp_statement) in
            tr_t2 <- translate_term f bindings t_env tr_t1.(tr).(tenv gmp_statement) t2  n;;
            let t2_code := tr_t2.(tr).(chunk gmp_statement) in

            let decl := ("v1", T_Ext Mpz)::("v2",T_Ext Mpz)::(c,C_Int)::tr_t1.(decls) ++ tr_t2.(decls) in

            let (ct1,tt1) := tr_t1.(res) in 
            let (ct2,tt2) := tr_t1.(res) in 
            let comp := CMP c (C_Id ct1 tt1) (C_Id ct2 tt2) "v1" "v2" in 

            let code := <{ t1_code ; t2_code; comp ; (Assign c (BinOpBool (C_Id c C_Int) (◖fsl_op) 0)) }>  in
            ret (mkSTR gmp_statement (mkTR gmp_statement code tr_t2.(tr).(tenv gmp_statement) []) decl  (c,C_Int))

        | P_Call pname args as call =>  
            match f.(preds) pname with 
            | None => 
                (* fixme: use error monad (predicate must be declared) *)
                ret (mkSTR gmp_statement (mkTR gmp_statement Skip e nil) nil  ("",C_Int))
            | Some (params,_) =>
                (* value returned by the function call *)
                c <- fresh_variable ;;

                (* for each pair of function argument and parameter *)
                let f_res := fold_left2 ( fun done arg param => 
                    done <- done ;;

                    (* get current declarations, translation and bindings environment *)
                    let '(curr_decls,curr_args_ids,curr_tr, binds) := done : (_⨉_⨉_) in 
                    

                    (* translate the argument *)
                    t_tr <- translate_term f bindings t_env curr_tr.(tenv) arg n ;;

                    let new_tr := curr_tr 
                        <| tenv := t_tr.(tr).(tenv) |> (* pass the updated env *)
                        <| chunk ::= fun s => Seq s t_tr.(tr).(chunk) |> (* append the code generated by the translation of t*)
                        <| glob ::= fun globs => app globs t_tr.(tr).(glob) |> (* append the new globals *)
                    in 

                    (* building the fresh binding env for parameters *)
                    v <- fresh_variable ;;;
                    let interval := 𝓘 arg t_env in

                    (* collect and append  *)
                    ( 
                        curr_decls ++ t_tr.(decls), (* the new fresh variables from the translation of the argument *)
                        curr_args_ids ++ [C_Id (fst t_tr.(res)) (snd t_tr.(res))], (* the variable used to represent the argument *)
                        new_tr, (* the updated function translation  *)
                        binds{param\(v,interval)} (* the updated bindings *)
                    )

                ) (ret ([(c,C_Int)], ([] : list _c_exp), mkTR gmp_statement Skip e [], ⊥)) args params  in

                
                f_res <- f_res ;;

                let '(decls,params_id,f_tr,binds) := f_res in 
                
                (* last env needed for function generation *)
                let last_env := f_tr.(tenv) in 

                (* get specialized function name, env and globals  *)
                gf <- match GlobalDef.find (pname,t_env) e with
                (* function already exists for current binders, no generation required, 
                    env is the same as the current one 
                    no new globals 
                *)
                | Some name => ret (name,e,[]) 
                | None => (* no function specialized for those binders, generate a new one *)
                    new_f <- function_generation f binds t_env last_env pname n ;;;
                    (* one new global : the function declaration itself *)
                    (new_f.(chunk), new_f.(tenv), new_f.(glob))
                end ;;;

                let '(gf_name,gf_env,gf_globs) := gf in  
                
                (* append function globals to the globals *)
                let globs := f_tr.(glob) ++ gf_globs in

                (* return value *)
                let res := (c,C_Int) (* c is int because return value is either 0 or 1 *) in 

                (* create calling code *)
                let code := PCall gf_name params_id in

                mkSTR gmp_statement (mkTR _ code gf_env globs) decls res
            end 
        end
    end

    with translate_term (f : @fenv _fsl_statement Empty_set) (bindings : Γᵥ) (t_env:Γᵢ) (e: ψ) (t : fsl_term) (fuel:nat) {struct fuel}
        : @state translated_statement := 

    match fuel with 
    | O => 
        (* fixme: use error monad (out of fuel) *)
        ret (mkSTR gmp_statement (mkTR gmp_statement Skip e nil) nil  ("",C_Int))  
    | S n =>
        match t with
        | T_Id v FSL_Int => (* program variable *)
            ret (mkSTR gmp_statement (mkTR gmp_statement Skip e nil) nil (v,C_Int))

        | T_Id v FSL_Integer => (* logic var *)
            let res := match bindings v with 
                | Some x => fst x
                | None => 
                    (* fixme: use error monad (bindings v necessarily succeeds,section 4.5.) *)
                    "fixme" 
            end  
            in 
            ret (mkSTR gmp_statement (mkTR gmp_statement Skip e nil) nil (v,T_Ext Mpz))

        | T_Z z =>
            let τ := 𝒯 z t_env in
            c <- fresh_variable ;;
            let decl := [(c,τ)]  in 
            let code := Z_ASSGN C_Int c z in
            ret (mkSTR gmp_statement (mkTR gmp_statement code e nil) decl (c,C_Int))

        | T_BinOp t1 _op t2 => 
            let τ := 𝒯 (T_BinOp t1 _op t2) t_env in
            c <- fresh_variable ;;
            v1 <- fresh_variable ;;
            v2 <- fresh_variable ;;
            r <- fresh_variable ;;
            t1_tr <- translate_term f bindings t_env e t1  n ;; 
            let t1_code := t1_tr.(tr).(chunk gmp_statement) in
            let t1_res := C_Id (fst t1_tr.(res)) (snd t1_tr.(res)) in
            t2_tr <- translate_term f bindings t_env t1_tr.(tr).(tenv gmp_statement) t2  n;; 
            let t2_code := t2_tr.(tr).(chunk gmp_statement) in
            let t2_res :=  C_Id (fst t2_tr.(res)) (snd t2_tr.(res)) in
            let decl := (c,τ) :: (v1,T_Ext Mpz) :: (v2,T_Ext Mpz) :: (r,T_Ext Mpz) :: t1_tr.(decls) ++ t2_tr.(decls) in
            let assgn := binop_ASSGN _op (c,τ) t1_res t2_res r v1 v2 in
            let code := <{ t1_code ; t2_code ; assgn }> in
            ret (mkSTR gmp_statement (mkTR gmp_statement code t2_tr.(tr).(tenv gmp_statement) nil) decl (c,C_Int))

        | T_Cond p t1 t2 as cond => 
            c <- fresh_variable ;;
            let τ := 𝒯  cond t_env in
            p_tr <- translate_predicate f bindings t_env e p n ;;
            t1_tr <- translate_term f bindings t_env p_tr.(tr).(tenv gmp_statement) t1  n ;; 
            let t1_code := t1_tr.(tr).(chunk gmp_statement) in
            let t1_res := C_Id (fst t1_tr.(res)) (snd t1_tr.(res))  in
            t2_tr <- translate_term f bindings t_env t1_tr.(tr).(tenv gmp_statement) t2  n;;;
            let t2_code := t2_tr.(tr).(chunk gmp_statement) in
            let t2_res := C_Id (fst t2_tr.(res)) (snd t2_tr.(res)) in
            let p_code  := p_tr.(tr).(chunk gmp_statement) in 
            let p_res := C_Id (fst p_tr.(res)) (snd p_tr.(res)) in
            let t1_assgn := τ_ASSGN τ c t1_res in
            let t2_assgn := τ_ASSGN τ c t2_res in
            let decl := (c,τ) :: p_tr.(decls) ++ t1_tr.(decls) ++ t2_tr.(decls) in
            let code := 
                <{
                    p_code;
                    if (p_res) <{ t1_code ; t1_assgn}> 
                    else <{t2_code ; t2_assgn }>
                }> in
            mkSTR gmp_statement (mkTR gmp_statement code t2_tr.(tr).(tenv gmp_statement) nil) decl  (c,C_Int)

        | T_Call fname args as call =>  
            match f.(lfuns) fname with 
            | None => 
                (* fixme: use error monad (logic function must be declared) *)
                ret (mkSTR gmp_statement (mkTR gmp_statement Skip e nil) nil  ("",C_Int))

            | Some (params,_) =>

                let rtype :=  𝒯 call t_env in 
                
                (* value returned by the function call *)
                c <- fresh_variable ;;

                (* for each pair of function argument and parameter *)
                let f_res := fold_left2 ( fun done arg param => 
                    done <- done ;;

                    (* get current declarations, translation and bindings environment *)
                    let '(curr_decls,curr_args_ids,curr_tr, binds) := done : (_ ⨉ _ ⨉ _) in 
                    

                    (* translate the argument *)
                    t_tr <- translate_term f bindings t_env curr_tr.(tenv) arg n ;;

                    let new_tr := curr_tr 
                        <| tenv := t_tr.(tr).(tenv) |> (* pass the updated env *)
                        <| chunk ::= fun s => Seq s t_tr.(tr).(chunk) |> (* append the code generated by the translation of t*)
                        <| glob ::= fun globs => app globs t_tr.(tr).(glob) |> (* append the new globals *)
                    in 

                    (* building the fresh binding env for parameters *)
                    v <- fresh_variable ;;;
                    let interval := 𝓘 arg t_env  in

                    (* collect and append  *)
                    ( 
                        curr_decls ++ t_tr.(decls), (* the new fresh variables from the translation of the argument *)
                        curr_args_ids ++ [C_Id (fst t_tr.(res)) (snd t_tr.(res))], (* the variable used to represent the argument *)
                        new_tr, (* the updated function translation  *)
                        binds{param\(v,interval)} (* the updated bindings *)
                    )

                ) (ret ([(c,rtype)], ([] : list _c_exp), mkTR gmp_statement Skip e [], ⊥)) args params  in

                
                f_res <- f_res ;;

                let '(decls,params_id,f_tr,binds) := f_res in 
                
                (* last env needed for function generation *)
                let last_env := f_tr.(tenv) in 

                (* get specialized function name, env and globals  *)
                gf <- match GlobalDef.find (fname,t_env) e with
                (* function already exists for current binders, no generation required, 
                    env is the same as the current one 
                    no new globals 
                *)
                | Some name => ret (name,e,[]) 
                | None => (* no function specialized for those binders, generate a new one *)
                    new_f <- function_generation f binds t_env last_env fname n ;;;
                    (* one new global : the function declaration itself *)
                    (new_f.(chunk), new_f.(tenv), new_f.(glob))
                end ;;;

                let '(gf_name,gf_env,gf_globs) := gf in  
                
                (* append function globals to the globals *)
                let globs := f_tr.(glob) ++ gf_globs in

                (* return value *)
                let res := (c,C_Int) (*fixme : what type is c ? *) in 

                (* create calling code *)
                let code : gmp_statement := match rtype with
                    | C_Int => FCall c gf_name params_id
                    | T_Ext (Mpz) => 
                        let firstparam := C_Id (fst res) (snd res) in 
                        PCall gf_name (firstparam :: params_id)
                    | _ => 
                        (* not possible *)
                        (* fixme: use error monad (rtype is either int or mpz) *)
                        Skip 
                end in


                mkSTR gmp_statement (mkTR _ code gf_env globs) decls res
            end
        end 
    end
    with function_generation (f:@fenv _fsl_statement Empty_set) (bindings:  Γᵥ) (t_env:Γᵢ) (env: ψ) (fname: id) (fuel:nat) {struct fuel}
    : @state (@translation_result 𝓥) := 
    match fuel with 
    | O => 
        (* fixme: use error monad (out of fuel) *)
        ret (mkTR _ "fixme" env []) 
    | S n =>
        match f.(lfuns) fname with
        | None => 
            (* fixme: use error monad (logic functions must be declared) *)
            ret (mkTR _ "fixme" env [])
        | Some (params,b) => 
            (* get the return type *)
            let rtype := 𝒯 b t_env in

            (* generate a fresh name for the new function *)
            fres <- fresh_fname fname;;

            (* process body *)

            tr_b <- translate_term f bindings t_env env b n ;;

            (* global declarations generated by the body , appended before function declaration  *)
            let globals := tr_b.(tr).(glob) in

            (* prepare env update : 
                indexed by the original name of the function and what binders interval Γᵢ it is for ;
                returns the unique generated function id for those binders
            *)
            let upd_binding := GlobalDef.add (fname,t_env) fres in

            let new_env := upd_binding tr_b.(tr).(tenv) in        

            (* in case the result is too big to fit in a machine integer *)
            let retvar := "_ret" in

            (*  build the signature of the function *)
            let signature : list _c_decl   -> _c_statement -> gmp_routine := 
                (* figure out the type and id of parameters *)
                let params := map (fun p => 
                    let i := match StringEnv.find p t_env with
                        | Some i => i 
                        | None => 
                            (*fixme: use error monad (p must be in t_env )  *) 
                             (0,0) 
                        end
                    in
                    (* get the corresponding id *)
                    let v := match bindings p with 
                        | Some (v,_) => v 
                        | None => 
                            (*fixme: use error monad (p must be in bindings)  *)
                            "fixme" 
                        end 
                    in 

                    C_Decl (ϴ i) v
                ) params in 

                match rtype with
                | C_Int => 
                    PFun C_Int fres params
                | T_Ext Mpz  => 
                    (* if rtype is mpz, pass function result using first argument *)
                    PFun Void fres ((C_Decl (T_Ext Mpz) retvar)::params)
                | _ => 
                    (* fixme: use error monad (rtype is either int or mpz) *)
                    PFun C_Int "" [] 

            end 
            in
            
            (* build the body *)
            (* reprocess body with original ψ + new f entry *)
            tr_b <- translate_term f bindings t_env (upd_binding env) b n;;;

            let '(body_res_id,body_res_ty) as bres := tr_b.(res) in 
            (* body epilogue *)
            let bdecls := DECLS [bres] in
            let inits := INITS [bres] in 

            let code := tr_b.(tr).(chunk) in
            
            let rv := (C_Id body_res_id body_res_ty) in
            let cl := CLEARS [bres] in
            (* body prologue *)
            let ret_and_cleanup := match rtype with
            | C_Int =>  <{ cl ; return rv}>
            | T_Ext Mpz => 
                let setret : gmp_statement := Set_z retvar body_res_id
                in <{ setret ;  cl }>
            | _ => Skip end 
            in
            let body := <{ inits ; code ; ret_and_cleanup }> in 
            let gen_f := signature bdecls body in
            mkTR _ fres new_env (globals++[gen_f]) (* function declarations is put with the other globals *)
        end 
    end
    .

    Definition c_decl_to_gmp_decl (d:@_c_decl Empty_set) : gmp_decl := 
        let '(C_Decl t id) := d in C_Decl (c_t_to_gmp_t t) id
    .

    Set Printing Implicit.
    (* translation of statements *)
    Fixpoint translate_statement (f:fenv) (bindings : Γᵥ) (t_env:Γᵢ) (env: ψ) (s : fsl_statement) : @state (@translation_result gmp_statement) := 
        match s with
        | S_Ext (LAssert p)  => 
            p_tr <- translate_predicate f bindings t_env env p 100;;; (* fixme explicit fuel value *)
            let d := DECLS p_tr.(decls) in
            let i := INITS p_tr.(decls) in
            let c := p_tr.(tr).(chunk gmp_statement) in
            let res := C_Id (fst p_tr.(res)) (snd p_tr.(res)) in
            let asrt := PAssert res in
            let clr := CLEARS p_tr.(decls) in 
            p_tr.(tr) 
                <| chunk := (GMP_Scope d <{i ;c ; asrt ; clr }> : gmp_statement) |> 
                 (* Before, we propagated declarations global declarations
                    because the syntax forbids declarations to be put in a statement.
                    It was a hack that required a different treatement inside translate_program might not have been correct.
                    Now, with GMP_Scope added to the gmp syntax, this is not necessary.

                    <| glob ::= fun l => l ++ (map GDecl d) |>
                *)            
        
        | FCall x f args => 
            let args := map c_exp_to_gmp_exp args in 
            ret (mkTR gmp_statement (FCall x f args) env nil)


        | Seq s1 s2  => 
            s1_tr <- translate_statement f bindings t_env env s1 ;;
            s2_tr <- translate_statement f bindings t_env s1_tr.(tenv) s2 ;;;
            s2_tr <| chunk := Seq s1_tr.(chunk) s2_tr.(chunk) |> <| glob ::= app s1_tr.(glob) |>

        | If e s1 s2 => 
            let e := c_exp_to_gmp_exp e in 
            s1_tr <- translate_statement f bindings t_env env s1 ;;
            s2_tr <- translate_statement f bindings t_env s1_tr.(tenv) s2 ;;;
            s2_tr <| chunk := If e s1_tr.(chunk) s2_tr.(chunk) |> <| glob ::= app s1_tr.(glob) |>

        | While e b =>  
            let e := c_exp_to_gmp_exp e in 
            tr <- translate_statement f bindings t_env env b ;;; 
            tr <| chunk := (While e tr.(chunk)) |>

        | Assign id e => ret (mkTR gmp_statement (Assign id (c_exp_to_gmp_exp e)) env nil)

        | PAssert e => 
            let e := c_exp_to_gmp_exp e in 
            ret (mkTR gmp_statement (PAssert e) env nil)
        | Return e => 
            let e := c_exp_to_gmp_exp e in 
            ret (mkTR gmp_statement (Return e) env nil)
        | PCall id args => let args := map c_exp_to_gmp_exp args in ret (mkTR gmp_statement (PCall id args) env nil)
        | Skip => ret (mkTR gmp_statement Skip env nil)
    end.


    Definition build_fenv (routines: list fsl_routine) : @fenv _fsl_statement Empty_set := 
        let extract_c_args : _c_decl* -> 𝓥* := List.map (fun d => let 'C_Decl _ x := d in x) in
        let extract_fsl_args : fsl_decl*-> 𝓥* := List.map (fun d => let 'FSL_Decl _ x := d in x) in
        List.fold_left (fun fenv r => 
        match r with 
        | PFun rtype name args _ body => 
            match rtype with 
            | Void => 
                (* procedure *)
                {|  funs := fenv.(funs); 
                    procs := fenv.(procs){name\(extract_c_args args,body)}; 
                    lfuns := fenv.(lfuns); 
                    preds := fenv.(preds)
                |}
            | C_Int =>  
                (* function *)
                {|  funs := fenv.(funs){name\(extract_c_args args,body)}; 
                    procs := fenv.(procs); 
                    lfuns := fenv.(lfuns); 
                    preds := fenv.(preds)
                |}
            | T_Ext _ => 
                (* PFun can't have T_Ext rtype *)
                fenv
            end
        | F_Ext (LFun rtype name args body) => 
            (* logic function *)
            {|  funs := fenv.(funs); 
                procs := fenv.(procs); 
                lfuns := fenv.(lfuns){name\(extract_fsl_args args,body)}; 
                preds := fenv.(preds)
            |}

        | F_Ext (Predicate name args body) => 
            (* predicate *)
            {|
                funs := fenv.(funs); 
                procs := fenv.(procs); 
                lfuns := fenv.(lfuns); 
                preds := fenv.(preds){name\(extract_fsl_args args,body)}
            |}
        end
        ) routines {|funs := ⊥ ; procs := ⊥ ; lfuns := ⊥; preds := ⊥|}
        .

    Definition translate_program (p: fsl_pgrm) : rac_pgrm := 

        let '(decls,routines) := p in  

        (* gather all routines definitions in fenv *)
        let fenv := build_fenv routines in 

        (* perform the static analysis *)
        let t_env := Oracle.get_Γᵢ p in

        (* begin by converting c decls to gmp_decls *)
        let gmp_decls := map c_decl_to_gmp_decl decls in

        (* for each new function, reset binders  *)
        let empty_bindings := ⊥ in

        (* generate from left to right the globals and function definitions *)
        let res := List.fold_left (
            fun (done : @state ((gmp_routine* ⨉ gmp_routine*) ⨉ ψ)%type) (doing:fsl_routine)  => 
                (* get the generated functions, translated functions and last ψ computed so far *)
                done_res <- done ;;

                let '(gen_f,tr_f, env) := done_res in 

                match doing with 
                | PFun rtype name args decls body =>
                    (* arguments and declarations are untouched *)
                    let args := map c_decl_to_gmp_decl args in 
                    let decls := map c_decl_to_gmp_decl decls in 

                    (* translate the body of the function, passing to it the last ψ *)
                    body_tr <- translate_statement fenv empty_bindings t_env env body ;;; 
                    
                    let tr_res := mkTR gmp_routine 
                        (PFun (c_t_to_gmp_t rtype) name args decls body_tr.(chunk))  
                        body_tr.(tenv) 
                        body_tr.(glob) in

                    (* append to the end of the other functions the newly translated one *)
                    let tr_f := tr_f++[tr_res.(chunk)] in  
                    
                    (* append the newly generated functions associated to the end of the others *)
                    let gen_f := gen_f++tr_res.(glob) in

                    (gen_f,tr_f, tr_res.(tenv))

                | _ => 
                    (* entry point is c functions only *)
                    ret done_res
                end
                
        ) routines (ret ([], [], GlobalDef.empty))
        in
        let '(gen_f,tr_f) := fst (exec res) (* discard generation_env *) in 
        (gmp_decls,gen_f++tr_f) (* first the generated functions and then the translated ones *)
    .
End Translation.