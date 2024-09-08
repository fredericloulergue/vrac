From Coq Require Import ZArith.ZArith Strings.String.
From RecordUpdate Require Import RecordUpdate.
From RAC Require Import Utils Environnement.
From RAC.Languages Require Import Syntax.

Import FunctionalEnv.
Open Scope utils.
Open Scope string_scope.
(* invariants for routine translation *)

(* notations *)
Inductive add_var (e : Env) (τ:gmp_t) (v:id) (z:Z) : Env -> Prop :=
| typeInt irz : 
    τ = C_Int ->
    add_var e τ v z (e <| env ; vars ::= {{v\(VInt (z ⁱⁿᵗ irz)) :𝕍}} |>)%utils

| typeMpz x (n:Int.MI) :
    τ  = Mpz ->
    (forall v',  e v' <> Some (Def (VMpz (Some x))) )->
    add_var e τ v z 
    ( e 
    <| env ; vars ::= {{ v\Def (VMpz (Some x)) }} |>
    <| mstate ::= {{x\Defined (proj1_sig n)}} |> 
    )
.

Example add_var_int : forall (ir3 :Int.inRange 3),
add_var empty_env C_Int "y" 3 (empty_env  <| env ; vars := ⊥{"y"\Def (VInt ( 3ⁱⁿᵗ ir3))} |>).
Proof. now constructor. Qed.

Definition 𝐴 := list (gmp_t ⨉ id ⨉ Z).

(* Fixpoint add_var_𝐴 (env : Ω) (mem_state : 𝓜) (A : 𝐴) : Ω * 𝓜 -> Prop := match A with 
    | nil => fun x => x
    | cons (t,v,z) tl => fun x => add_var env mem_state t v z (fst x, snd x)
end. *)


(*fixme fixpoint or List.fold *)
(*)
Definition add_var_𝐴 (env : Ω) (mem_state : 𝓜) (A : 𝐴) : Prop :=
    List.fold_left (
        fun (acc:Prop) (args:gmp_t * id * Z)  => 
            let '(t,id,z) := args in
            add_var env mem_state t id z  (env,mem_state) /\ acc 
    ) A (env,mem_state)
 . *)

Inductive add_var_𝐴 (e : Env) : 𝐴 -> Env -> Prop := 
| add_var_nil : add_var_𝐴  e nil e

| add_var_cons t v z A e': 
    True -> 
    add_var e t v z e' -> 
    add_var_𝐴 e A e'
.



Example add_var_mpz  : 
add_var empty_env Mpz "y" 3  
    ( empty_env 
        <| env ; vars := ⊥{"y"\Def 1%nat} |>
        <| mstate := ⊥{(1%nat)\(Defined 3)} |>
    )
.
Proof.
    assert (ir3: Int.inRange 3). easy.
    now apply (typeMpz empty_env Mpz "y" 3 1%nat (3ⁱⁿᵗ ir3)).
Qed.



(* Compute add_var_𝐴 (⊥,⊥) ⊥ nil. *)

Example envaddnil : add_var_𝐴 empty_env nil empty_env.
Proof.
 constructor.
Qed.

Open Scope list.

Example envaddone : add_var_𝐴 empty_env  ((T_Ext Mpz, "y", 3)::nil) 
    (empty_env 
        <| env ; vars := ⊥{"y"\Def (VMpz 1%nat)} |>
        <| mstate := ⊥{1%nat\(Defined 3)} |>
    )
.
Proof.
    assert (ir3: Int.inRange 3). easy.
    eapply add_var_cons with (t:=Mpz) (v:="y") (z:=3).
 - auto.
 - apply (typeMpz empty_env Mpz "y" 3 1%nat (3ⁱⁿᵗ ir3)).
    * reflexivity.
    * intro v. intro contra. inversion contra.
Qed.




(*

(* synchronicity invariant *)
Definition I1 (env:Ω) (ienv:Γ) := ((dom env.(binds)) = (dom (fst ienv) + dom (snd ienv)))%utils.

(* suitability invariant *)
Definition I2 (env:ψ) := True. (* todo *)


*)


(*

Inductive pgrm_var_representation (iop:ϴ) (e : Env) (ienv:Γ) : Env -> Prop :=
| empty ΩΓ 𝓜Γ :   
    I1 e ienv ->
    let A := nil  (* { (iop ((snd ienv) v), v, (snd env) v ) | v in dom ienv  } *)
    in
    add_var_𝐴 e A {|env:=ΩΓ; mstate:=𝓜Γ|} -> 
    pgrm_var_representation iop e ienv{|env:=ΩΓ; mstate:=𝓜Γ|}
.

(* Definition well_formed_program :=
    - all variables declared before usage
    - all functions defined before called
    - well typed
*)


*)