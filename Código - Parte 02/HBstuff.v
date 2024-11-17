From HB Require Import structures.
Require Import ssreflect.
From mathcomp Require Import all_algebra ssrnat ssrint ssrfun.

Module LearnHB.

HB.mixin Record Monoid_of_Type M := {
    zero : M;
    add : M -> M -> M;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add;
}.

HB.structure Definition Monoid := { M of Monoid_of_Type M }.

HB.mixin Record Ring_of_Monoid R of Monoid R := {
    one : R;
    opp : R -> R;
    mul : R -> R -> R;
    addNr : left_inverse zero opp add;
    addrN : right_inverse zero opp add;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
    mulrDl : left_distributive mul add; 
    mulrDr : right_distributive mul add; 
}.

HB.structure Definition Ring := { R of Monoid R & Ring_of_Monoid R }.

Lemma addrC {R : Ring.type} : commutative (@add R).
Proof.
rewrite /commutative => x y. 
rewrite -(addr0 x).
Abort. 

Lemma magic_trick (R : Ring.type) (x : R) :
add x zero = x.
Proof.
Set Printing Coercions.
by rewrite addr0.
Qed.

Lemma addz0 (x : int) :
intZmod.addz x 0 = x.
Proof.
by rewrite intZmod.addzC intZmod.add0z.
Qed.

Definition Z_Monoid_axioms : Monoid_of_Type int :=
Monoid_of_Type.Build int 0%Z intZmod.addz intZmod.addzA intZmod.add0z addz0.

HB.instance int Z_Monoid_axioms.

HB.about int.
HB.about Monoid.



End LearnHB.

Module Simpler.

HB.mixin Record Assoc_of_Type M := {
    add : M -> M -> M;
    assoc : forall (a b c : M), add (add a b) c = add a (add b c);
}.

HB.structure Definition Assoc := { M of Assoc_of_Type M }.

Lemma assocn (a b c : nat) : 
    ((a + b) + c = a + (b + c)).
Proof.
by rewrite addnA.
Qed. 

Definition N_Assoc_axioms : Assoc_of_Type nat :=
    Assoc_of_Type.Build nat addn assocn.

HB.instance nat N_Assoc_axioms.

Example magic_trick (a b c : nat) :
add (add a b) c = add a (add b c).
Proof.
by rewrite assoc.
Qed.

Notation "x + y" := (@add _ x y).

HB.mixin Record CommAndAssoc_of_Type M of Assoc M := {
    comm : forall (a b : M), a + b = b + a;
}.

Module End.
