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

Section Own.


Inductive nodd (n : nat) : Type :=
    Nodd m of (odd m = false).
    
Coercion nat_of_nodd n (p : nodd n) := let: @Nodd _ m _ := p in m. 

Variable n' : nat.
Implicit Types x y z : nodd n'.

(* Search (odd). *)

Lemma odd_add n:
    odd (n + odd n) = false.
Proof.
    case Ho : (odd n).
        rewrite //=. rewrite addn1 oddS Ho //=.
    rewrite //= addn0. move=>//.
Qed.
Definition pairs_in n m := @Nodd n (m + (odd m)) (odd_add m).

(* Lemma valNood x :
    pairs_in n' x = x.
Proof.
    move: (@val_inj nat odd nodd).
    case: x => x Hx. 
    rewrite /pairs_in //=.
    move: (@val_inj nat odd) => H.
    rewrite /injective in H. *)

Definition pair0 := pairs_in 0.
Definition pair1 := pairs_in 1.
Definition pair_add x y := pairs_in (x + y).
Definition pair_mul x y := pairs_in (x * y).

(* Lemma oddnodd (x : nodd) :
    x + odd x = x.
Proof.
    case: x => m Hm. rewrite //= Hm //= addn0.
    by [].
Qed.
 *)

(* Lemma pair_add0z : 
    left_id pair0 pair_add.
Proof.
    move=> x.
    rewrite /pair_add.
    case: x => x Hx. rewrite //= addn0 add0n.
    rewrite /pairs_in.  
    rewrite Hx. *)
End Own.

Section Zmodp_Learn.

Variable p' : nat.
Local Notation p := p'.+1.
Implicit Types x y z : 'I_p.

Check 'I_p.

(* Standard injection; val (inZp i) = i %% p *)
Definition inZp i := @Ordinal p (i %% p) (ltn_pmod i (ltn0Sn p')).
Lemma modZp x : x %% p = x.
    rewrite modn_small.
    { reflexivity. }
    { rewrite ltn_ord. reflexivity. }
Qed.

Check (leq _ 1).

(* Lemma valZpK x : 
    inZp x = x.
Proof.
    apply: (@val_inj nat _ 'I_p). 
    by apply: val_inj; rewrite /= modZp. 
Qed.

Lemma batata: ∀ x,
    x + 0 = x.
Proof.
    intros. 
    rewrite addc.
Abort. *)

End Zmodp_Learn.

