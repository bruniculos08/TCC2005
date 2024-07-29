From Coq Require Import Unicode.Utf8_core.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssreflect.ssrnat.
Require Export Arith.
Require Export Bool.
Require Export PeanoNat.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Printing Coercions.

From HB Require Import structures.
Import generic_quotient.
HB.about eqType.
HB.howto eqType.
HB.about bool.
HB.about isQuotient.
HB.about isQuotient.repr_of.

Section Zmodp_Learn.

Variable p' : nat.
Local Notation p := p'.+1.
Implicit Types x y z : 'I_p.

(* Standard injection; val (inZp i) = i %% p *)
Definition inZp i := @Ordinal p (i %% p) (ltn_pmod i (ltn0Sn p')).
Lemma modZp x : x %% p = x.
    rewrite modn_small.
    { reflexivity. }
    { rewrite ltn_ord. reflexivity. }
Qed.

Lemma batata: ∀ x,
    x + 0 = x.
Proof.
    intros. 
    rewrite addc.
