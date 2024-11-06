From Coq Require Import Unicode.Utf8_core.

Module withCoercions.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssreflect.ssrnat.
Require Export Arith.
Require Export Bool.
Require Export PeanoNat.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Printing Coercions.

Record smaller (n : nat) : Type := Build
{
    x : nat;
    axiom : x < n
}.

(*  "The two following function definitions (the first is commented) for coercion WORK for mantaing record type information after coercion:" *)
Definition smaller_nat (n : nat) (e : smaller n) : nat :=
    let t := (x n e) in t.

(* Definition smaller_nat := x. *)

 (* "The following coercion definiton DOES NOT WORK work for mantaing record type
    information after coercion:" *)
(* Definition smaller_nat (n : nat) (e : smaller n) : nat :=
    match e with
    | Build t _ => t
    end. *)

Coercion smaller_nat : smaller >-> nat.
(* Coercion x : smaller >-> nat. *)

Check (∀ (n : nat) (a : smaller n), a + 0 = 0).

Theorem Ex1 {n} :
    ∀ (b : nat) (a : smaller n), a - b < n .
Proof.
    intros. destruct a. simpl.
    (* unfold x. remember zmodn_nat as f. subst f.
    unfold zmodn_nat.*) destruct b.
    { rewrite subn0. assumption. }
    { 
        destruct x0.
        { rewrite sub0n. assumption. }
        { 
            rewrite subSS.
            assert (x0 - b < x0.+1).
            {
                apply sub_ord_proof.   
            }
            pose proof (@ltn_trans (x0.+1) (x0 - b) n).
            apply H0.
            { assumption. }
            { assumption. }
        }
    }
Qed.

Canonical subn_smaller {n : nat} (b : nat) (a : smaller n) : smaller n := Build n (a - b) (Ex1 b a). 

Theorem Ex2 {n} :
   ∀ (f : nat -> nat) (a : smaller n), (f a) %% n < n.
Proof.
    intros. destruct n.
    - destruct a. inversion axiom0.
    - assert(0 < n.+1).
    { auto. }
    { apply (@ltn_pmod (f a) n.+1) in H. assumption. }
Qed.

Lemma Ex3 {n} :
    ∀ (a : smaller n),
    a < n.
Proof.
    intros. destruct a. simpl. assumption.
Qed.

Theorem Ex4 {n} : 
    ∀ (a : smaller n), (a %% n < n).
Proof.
    destruct n.
    { intros. destruct a. unfold is_true in axiom0. inversion axiom0. }
    { intros. apply ltn_pmod. auto. }
Qed.

(* Canonical mod_smaller {n : nat} (a : smaller n) : smaller n := Build n (a %% n) (@Ex4 n a). *)

(* Lemma AA: 
    1 < 2 = true.
Proof.
    reflexivity.
Qed.

Definition BB := Build 2 1 AA.

Check (@mod_zmod 2 BB).

Compute (rev [seq 2 * x | x <- rev [::5;2]]). *)

Notation "X (*...*)" :=
    (let x := X in let y := _ in x) (at level 100, format "X  (*...*)").

Notation "[LHS 'of' equation ]" := 
    (let LHS := _ in 
        let _infer_LHS := equation : LHS = _ in LHS) (at level 4).

Notation "[unify X 'with' Y ]" := 
    (let unification := erefl _ : X = Y in True).

(* Set Printing All.
Set Printing Coercions.

Print Ex3. *)

(* Check (∀ n (f : nat -> nat) (a : smaller n),
    let LHS := [LHS of ((fun (n : nat) (a : smaller n) =>
    match a as s return (s < n) with
    | {| x := x0; axiom := axiom |} =>
        (fun (x1 : nat) (axiom0 : x1 < n) =>
           axiom0 : {| x := x1; axiom := axiom0 |} < n) x0 axiom
    end
       ) n _)] in
    let RDX := (((f a) %% n) < n) in
    [unify LHS with RDX]). *)

Fail Check (∀ n (f : nat -> nat) (a : smaller n),
    let LHS := [LHS of Ex3 _] in
    let RDX := (((f a) %% n) < n) in
    [unify LHS with RDX]).

Check (∀ n (f : nat -> nat) (a : smaller n),
    let LHS := [LHS of Ex3 (Build n ((f a) %% n) (Ex2 f a))] in
    let RDX := (((f a) %% n) < n) in
    [unify LHS with RDX]).

(* Canonical f_mod_smaller {n : nat} (f : nat -> nat) (a : smaller n) : smaller n := 
    Build n ((f a) %% n) (Ex2 f a). *)

Example Ex5 {n} :
    ∀ (a : smaller n), ((((fun x => 2 + x) a) %% n)) < n = (a < n).
Proof.
    intros. rewrite Ex3.
    (* rewrite addnC. *)
    rewrite Ex2.
    reflexivity.
Qed.

From HB Require Import structures.
Import generic_quotient.
HB.about eqType.
HB.howto eqType.
HB.about bool.
HB.about isQuotient.
HB.about isQuotient.repr_of.

(* Print ltn_pmod. *)
Print ltn0Sn.
Print Ordinal.

Example Ex6 {n} :
    ∀ (a : smaller n), (a %% n) < n = (a < n).
Proof.
    intros. rewrite Ex3.
    remember (@id nat).
    assert ((x n a) = n0 (x n a)).
    {
        rewrite Heqn0. reflexivity.      
    }
    (* rewrite //=.
    rewrite H.
    rewrite Ex3.
    reflexivity.
Qed. *)
Abort.

Print associative.
Print rel.
Print pred.
Compute (rel nat).

Record Monoid : Type := monoid 
{
    sort :> Type;
    bin_op : sort -> sort -> sort;
    associative_axiom : associative bin_op;
    e : sort;
    neutral_axiom : ∀ x : sort, bin_op x e = x /\ bin_op e x = x
}.

(* Instancing addition as a member of Monoid *)

Lemma add_0_neutral:
    ∀ x : nat, x + 0 = x /\ 0 + x = x.
Proof.
    induction x0.
    { split. reflexivity. reflexivity. }
    { split.
        { rewrite addn0. reflexivity. }
        { rewrite addnC. rewrite addn0. reflexivity. }
    }
Qed.

Search addn.

Notation "x ⊗ y" := (@bin_op _ x y) (at level 1). 
Notation "0" := (@e _).

Definition add_monoid := monoid nat addn  addnA 0%nat add_0_neutral.

Fail Check (1 ⊗ 2).

Canonical add_monoid.

Check (1 ⊗ 2).

Lemma Ex6: 
    ∀ (M : Monoid), ∀ (a b : M), a ⊗ (0 ⊗ b) = 0 ⊗ (a ⊗ b).
Proof.
    intros. pose proof (neutral_axiom M b). destruct H.
    rewrite H0. pose proof (neutral_axiom M (a ⊗ b)).
    destruct H1. rewrite H2. reflexivity.
Qed.

Lemma Ex7: 
    ∀ (M : Monoid), ∀ (a b : M), a ⊗ b = 0 ⊗ (a ⊗ b).
Proof.
    intros. pose proof (neutral_axiom M (a ⊗ b)). destruct H.
    rewrite H0. reflexivity.
Qed.

Example add_1_neutral:
    ∀ a b : nat, a + (0%nat + (S b)) = 0%nat + (a + (S b)).
Proof.
    (* intros. rewrite add0n. apply Ex7.  *)
    intros. apply Ex6.
Qed.

Lemma mul_1_neutral: 
    ∀ a : nat, a * 1 = a /\ 1 * a = a.
Proof.
    intros. split.
    { by rewrite muln1. }
    { rewrite mulnC. by rewrite muln1. }
Qed.

Canonical mul_monoid := monoid nat muln mulnA 1 mul_1_neutral.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

Check (fun (x y : nat) => (bin_op _) x y).

Compute (bin_op _ 1 1).

Notation "x $$ y" := (bin_op _ x y) (at level 100).

Check (fun (x y : nat) => (x $$ y)).

Definition Ex8 {f : Monoid} (t1 : f * f) (t2 : f * f) :=
    match t1, t2 with
    | (a, b), (c, d) => (a $$ c, b $$ d)
    end. 

Compute (Ex8 (1, 1) (2, 5)).


End withCoercions.

Module myGroups.

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Import intZmod.
Require Export Arith.
Require Export Bool.
Require Export PeanoNat.

Record group : Type := Group 
{
    sort :> Type;
    bin_op : sort -> sort -> sort;
    associative_axiom : associative bin_op;
    e : sort;
    neutral_left : left_id e bin_op;
    neutral_right : right_id e bin_op;
    inverse_left : ∀ x : sort, ∃ y : sort, bin_op y x = e; 
    inverse_right : ∀ x : sort, ∃ y : sort, bin_op x y = e 
}.

Theorem inverse_left_int:
    ∀ x : int, ∃ y : int, addz y x = 0.
Proof.
    intros. exists (oppz x). unfold oppz.
    destruct x.
    { destruct n. simpl. reflexivity. simpl. unfold "<".
    rewrite subnn. reflexivity. }
    { simpl. unfold "<". rewrite subnn. reflexivity. }
Qed.

Theorem inverse_right_int:
    ∀ x : int, ∃ y : int, addz x y = 0.
Proof.
    intros. exists (oppz x). rewrite addzC. unfold oppz. 
    destruct x.
    { destruct n. simpl. reflexivity. simpl. unfold "<".
    rewrite subnn. reflexivity. }
    { simpl. unfold "<". rewrite subnn. reflexivity. }
Qed.

Theorem addz0:
    right_id 0%Z addz.
Proof.
    unfold right_id. intro. rewrite intZmod.addzC. apply intZmod.add0z.
Qed.

Notation "x ⊗ y" := (@bin_op _ x y) (at level 10).
Notation "0" := (@e _).

Fail Check (1%Z ⊗ 1%Z). 

Definition int_group :=
    Group int addz addzA 0%Z add0z addz0 inverse_left_int inverse_right_int.

Canonical int_group.

Check (1%Z ⊗ 1%Z).

Theorem Ex9: 
    ∀ (G : group) (a b : G), (a ⊗ b) ⊗ 0 = (a ⊗ 0) ⊗ b.
Proof.
    intros. rewrite (neutral_right G). rewrite (neutral_right G).
    reflexivity. 
Qed.

(* Notation "x + y" := (addz x y). *)

Theorem Ex10:
    ∀ a b : int, (a ⊗ b) ⊗ 0%Z = (a ⊗ 0%Z) ⊗ b.
Proof.
    move=> a b. 
    rewrite ?addzC.
    rewrite /(_ ⊗ _) //=.
    rewrite addzC.
Qed.

Check (Posz).

End myGroups.

From mathcomp Require Import -(coercions) all_ssreflect.
From mathcomp Require Import -(coercions) ssreflect.ssrnat.
Require Export Arith.
Require Export Bool.
Require Export PeanoNat.

(* "Equivalente defintion for the following record named 'eqType':" *)

(* Inductive eqType : Type :=
    | Pack (sort : Type) (op : sort -> sort -> bool) (axiom : ∀ x y, reflect (x = y) (op x y)).
    
Definition sort (e : eqType) : Type :=
    match e with
    | Pack t _ _ => t
    end.
Definition op (e : eqType) : (sort e -> sort e -> bool) :=
    match e with
    | Pack _ f _ => f
    end.
(* Definition axiom (e : eqType) : (∀ x y, reflect (x = y) ((op e) x y)) := *)
Definition axiom (e : eqType) : (eq_axiom (op e)) :=
    match e with
    | Pack _ _ a => a
    end. *)

Print rel.
Print pred.

Record eqType : Type := Pack
{
    sort : Type;
    eq_op : sort -> sort -> bool;
    axiom : eq_axiom eq_op
}. 

Theorem axiom_nat: ∀ x y : nat, reflect (x = y) (eqn x y).
Proof.
    intros x y. Search (reflect _ _). generalize dependent y.
    induction x.
    {
        destruct y. apply ReflectT. reflexivity.
        simpl. apply ReflectF. intro. inversion H.    
    }
    {
        intros. destruct y.
        {
            simpl. apply ReflectF. intro. inversion H.   
        }
        {
            simpl. assert (x.+1 = y.+1 <-> x = y).
            { 
                split.
                {
                    intros. injection H. trivial.   
                }
                {
                    intros. apply f_equal. assumption.   
                }
            }
            {
                symmetry in H. apply (@equivP (x = y)).
                {
                    apply IHx.   
                }
                {
                    assumption.   
                }   
            } 
        }   
    } 
Qed.

Definition natEqType := Pack nat eqn axiom_nat.

Check (axiom natEqType).
Print eq_axiom.

Compute (@eq_op natEqType 1 1).

Notation "x == y" := (@eq_op _ x y).

Fail Check (3 == 2).

Canonical natEqType.

Check (3 == 2).

Definition cmp_option (e : eqType) (o1 o2 : option (sort e)) :=
    match o1, o2 with
    | Some e1, Some e2 => eq_op e e1 e2
    | None, Some _ => false
    | Some _, None => false
    | None, None => true
    end.

Theorem axiom_option: 
   ∀ e : eqType, eq_axiom (cmp_option e).
   
   (* ∀ x y : option (sort e), reflect (x = y) (@cmp_option e x y). *)
Proof.
    intros. unfold Equality.axiom. destruct e. simpl in y. simpl in x. unfold cmp_option. simpl.
    destruct x.
    {
        destruct y.
        {
            assert (Some s = Some s0 <-> s = s0).
            {
                split.
                { intros. injection H. trivial. }
                { intros. apply f_equal. assumption. }      
            }
            apply (@equivP (s = s0)).
            { apply axiom0. }
            { symmetry. assumption. }   
        }
        apply ReflectF. intro. inversion H.   
    }
    {
        destruct y.
        { apply ReflectF. intro. inversion H. }
        { apply ReflectT. reflexivity. }      
    }
Qed.

Definition optionEqType (e : eqType) := Pack (option (sort e)) (cmp_option e) (axiom_option e).

Fail Check (Some 1 == Some 2).

Canonical optionEqType.


Check (Some 1 == Some 2).

About option.
Print option.
Compute option.
Search (option).