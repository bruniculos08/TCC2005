From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssreflect.ssrnat.
Require Export Arith.
Require Export Bool.
Require Export PeanoNat.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Printing Coercions.

Record multiple (n : nat) : Type := Build
{       
        x : nat;
        axiom : (n %| x)%N        
}.

(* Definition multiple_to_nat {n} (a : multiple n) :=
match a with
| Build m _ => m
end.  *)

Definition multiple_nat (n : nat) (e : multiple n) : nat :=
    let: @Build _ t _ := e in t.

(* Fail Check (forall (n : nat) (a : multiple n), a + 0 = a).
Check (forall (n : nat) (a : multiple n), (x _ a) + 0 = (x _ a)). *)

(* Coercion multiple_nat : multiple >-> nat. *)
Coercion x : multiple >-> nat.

Check (forall (n : nat) (a : multiple n), a + 0 = a).

Lemma Ex1 {n}: 
forall (a b : multiple n), (n %| a + b).
Proof.
move=> a b. case: a => a pDa. case: b => b pDb.
rewrite //= (dvdn_add pDa pDb) //.
Qed.

(* "Exemplo_smaller_axiom" *)
Lemma exemplo_multiple_axiom {n}:
        forall (a : multiple n), (n %| a).
Proof.
move=> [a H] //=.
Qed.

(* "Exemplo_aplicacao_f_mod" *)
Lemma exemplo_aplicacao_f_mul {n}:
        forall (f : nat -> nat) (a : multiple n), (n %| ((f a) * n)).
Proof.
move=> f a. rewrite dvdn_mull //.
Qed.

(* "Exemplo_a_provar"
Lemma Ex4 {n}:
        forall (a : multiple n), n %| (((fun x => x + 8) (((fun x => 2 * x) a) * n)) * n).
Proof.
move=> a. rewrite dvdn_mull //=.
Qed. *)

Notation "X (*...*)" :=
(let x := X in let y := _ in x) (at level 100, format "X (*...*)").

Notation "[LHS 'of' equation ]" :=
        (let LHS := _ in
                let _infer_LHS := equation : LHS = _ in LHS) (at level 4).

Notation "[unify X 'with' Y ]" :=
        (let unification := erefl _ : X = Y in True).

Fail Check (forall n (a : multiple n) (f : nat -> nat),
        let LHS := [LHS of Ex2 _] in
        let RDX := (n %| (f a) * n) in
        [unify LHS with RDX]).

Check (forall n (a : multiple n) (f : nat -> nat),
        let LHS := [LHS of Ex2 (@Build n ((f a) * n) (Ex3 f a))] in
        let RDX := (n %| (f a) * n) in
        [unify LHS with RDX]).

Canonical f_mul_multiple (n : nat) (f : nat -> nat) (a : multiple n) := 
        (@Build n ((f a) * n) (@Ex3 n f a)).

(* "Exemplo_a_provar" *)
Lemma exemplo_a_provar {n}:
        forall (a : multiple n), (n %| ((fun x => x + 8) (((fun x => 2 * x) a) * n)) * n).
Proof.
move=> a //=.
rewrite /is_true.
rewrite addnC.
rewrite Ex2.
by [].
Qed.

(* Because of the last canonical the following works now: *)
Check (forall n (a : multiple n) (f : nat -> nat),
        let LHS := [LHS of Ex2 _] in
        let RDX := (n %| (f a) * n) in
        [unify LHS with RDX]).

(* ------------------------------------------------------------------- *)

Definition quotient {n} (x : multiple n) :=
        x %/ n.
        
Fail Check (fun {n} (a b : multiple n) => quotient (a + b)).

Canonical multiple_sum {n} (a b : multiple n) : (multiple n) :=
        @Build n (a + b) (@Ex1 n a b).

(* Check (fun (n : nat) (a b : multiple n) => @quotient n (a + b)). *)

Record smaller (n : nat) : Type := Create
{       y :> nat;
        H : y < n   }.

(* Check (forall (n : nat) (a : smaller n), (y a) + 0 = 0). *)

(* "Exemplo_smaller_axiom" *)
Lemma Exemplo_smaller_axiom {n}:
forall (a : smaller n), a < n.
Proof.
move=> a. case: a => a H //=.
Qed.

(* Canonical smaller_subn {n} (b : nat) (a : smaller n) : (smaller n) :=
        @Create n (a - b) (Exemplo_smaller_axiom b a). *)

(* "Exemplo_aplicacao_f_mod" *)
Lemma Exemplo_aplicacao_f_mod {n}:
forall (f : nat -> nat) (a : smaller n), (f a) %% n < n.
Proof.
move=> f a. case: a => a H /=.
rewrite ltn_pmod //. move: H. by case: n.
Qed.

Fail Check (forall n (f : nat -> nat) (a : smaller n),
    let LHS := [LHS of Exemplo_smaller_axiom _] in
    let RDX := (((f a) %% n) < n) in
    [unify LHS with RDX]).

Check (forall n (f : nat -> nat) (a : smaller n), 
        let LHS := [LHS of Exemplo_smaller_axiom (Create n ((f a) %% n) (Exemplo_aplicacao_f_mod f a))] in
        let RDX := (((f a) %% n) < n) in
        [unify LHS with RDX]).

Canonical f_mod_smaller {n} (f : nat -> nat) (a : smaller n) : smaller n := 
        (Create n ((f a) %% n) (Exemplo_aplicacao_f_mod f a)).

Example Exemplo_a_provar {n} :
        forall (a : smaller n), ((fun x => x + 8)
        ((( fun x => 2 * x) a) %% n)) %% n < n = (a < n).
Proof.
move=> a.
rewrite Exemplo_smaller_axiom.
rewrite addnC.
rewrite Exemplo_smaller_axiom.
by [].
Qed.

Definition limit {n} (x : smaller n) := n.

Check (fun (n b : nat) (a : smaller n) => limit (a - b)).

