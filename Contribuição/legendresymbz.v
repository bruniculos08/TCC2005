From mathcomp Require Import all_ssreflect ssreflect eqtype all_algebra
ssrbool bigop ssrnat ssrint ssralg intdiv seq prime order perm zmodp all_solvable.
From contributions Require Import primez inversezmodp.

Import Order.Theory.
From Coq Require Import Logic.Decidable.

Import GRing.Theory.

Set Implicit Arguments.     
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Module Legendre. *)

    Definition legendre_symb {p : int} (pL2 : (2 < p)%R) (pP : primez.primez p) (a : int) :=
        if (a ^ ((p - 1) %/ 2)%Z == 1 %[mod p])%Z then 1%Z
        else if (p %| a)%Z then 0%Z
        else (-1)%Z.

    Theorem eulerz_criterion {p : int} (a : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
        (a ^ ((p - 1) %/ 2)%Z = (legendre_symb pL2 pP a) %[mod p])%Z.
    Proof.
    case pDa : (p %| a)%Z.
    move: pDa => /dvdz_mod0P pDa.
    rewrite /legendre_symb.
    clear pL2.
    move: pP pDa.
    case: p => // p pP aE0.
    rewrite subzn.
    rewrite natz /exprz //= mul1n.
    rewrite -(modzXm _ a) aE0 exprnP /exprz -rmorphXn //= natrXE.
    case H : ((p - 1) %/ 2) => [|k].
        rewrite expn0 eqxx.
        rewrite //=.
    rewrite exp0n.
    rewrite eqz_mod_dvd add0r !dvdzE //= Euclid_dvd1.
    rewrite -(absz_nat p) -dvdzE -(subr0 a) -eqz_mod_dvd aE0 !mod0z //=.
    move: pP => /andP [_ pP] //=.
    rewrite //=.
    apply prime_gt0.
    move: pP => /andP [_ pP] //=.
    rewrite /legendre_symb.
    move: pP pDa.
    clear pL2.
    case : p => // p pP pDa.
    rewrite pDa.
    apply negbT in pDa.
    move: pDa => /negP pDa.
    move: (primez.pred_primez_half_mod pP pDa) => /orP H.
    case: H => [H| /eqP H].
        rewrite H. apply/eqP. rewrite H //=.
    rewrite H.
    move: pP => /andP [pL0 //= pP].
    move: (even_prime pP) => [-> //= | podd].
    rewrite -(eqz_modDl 1) //= subrr -PoszD addn1.
    rewrite eqz_mod_dvd sub0r dvdzE //= (dvdn_prime2 pP); last by [].
    have -> : (p == 2) = false.
        apply/eqP => p2.
        rewrite p2 //= in podd.
    by [].
    Qed.

    (* 
        Propriedades sobre Símbolo de Legendre a serem
        provadas:

        (i) se a = b %[mod p] então (a/p) = (b/p)

        (ii) se ~~(p %| a) então (a²/p) = 1

        (iii) (-1/p) = (-1)^(p.-1./2), ou seja, -1 é resíduo
        quadrático módulo p (isto é, (-1/p) = 1) se e somente se p = 1 %[mod 4]
        e não é um resíduo quadrático módulo p (isto é, (-1/p) = -1) se e 
        somente se p = 3 %[mod 4].

        (iv) (a*b / p) = (a/p) * (b/p)
    *)

    Lemma legendre_symbE (p a b : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
        (a == b %[mod p])%Z -> ((legendre_symb pL2 pP a) == (legendre_symb pL2 pP b)).
    Proof.
    move: pP pL2.
    case: p => // p pP pL2 /eqP amodb.
    rewrite /legendre_symb.
    clear pL2.
    rewrite (@subzn p); last by move: pP amodb; case: p.
    rewrite divz_nat addn1 /exprz.    
    rewrite -(modzXm _ a) -(modzXm _ b) amodb (modzXm _ b).
    rewrite -(subr0 b) -eqz_mod_dvd -amodb !eqz_mod_dvd !subr0 //=.
    Qed.

    Lemma legendre_symb_Ndvd (p a b : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
        ~~(p %| a)%Z -> (legendre_symb pL2 pP (a^2)) == 1.
    Proof.
    rewrite /legendre_symb.
    move: pP pL2.
    case: p => // p pP pL2.
    rewrite !(@subzn p); last by move: pP pL2; case: p => [// | p].
    move=> /negP pDa.
    move: (primez.pred_primez_half_mod pP pDa).
    rewrite !(@subzn p); last by move: pP pL2 pDa; case: p => [// | p].
    rewrite !divz_nat exprzAC /exprz //= addn1 => /orP [/eqP aexp |/eqP aexp].
    rewrite -(modzXm _ (a ^+ ((p - 1) %/ 2))) aexp modzXm !exprnP exp1rz eqz_mod_dvd subrr dvdz0 //=.
    rewrite -(modzXm _ (a ^+ ((p - 1) %/ 2))) aexp modzXm !exprnP.
    rewrite exprSz expr1z -mulrzz mulNrNz intz eqz_mod_dvd subrr dvdz0 //=.
    Qed.

    Lemma legendre_symb_Neg1 (p : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
        ((legendre_symb pL2 pP (-1)) == 1) = (p == 1 %[mod 4])%Z.
    Proof.
    apply Bool.eq_true_iff_eq.
    split.
    rewrite /legendre_symb. 
    move: pP pL2.
    case: p => // p.
    move=> pP pL2 leg_symb.
    rewrite eqz_mod_dvd subzn; last by rewrite prime_gt0 //=.
    rewrite dvdzE //= !add1n. apply/dvdnP.
    exists ((p.-1./2)./2).
    have -> : 4 = 2 * 2 by rewrite //=.
    rewrite mulnA !muln2 !even_halfK.
        by rewrite subn1.
    Set Printing Coercions.
    move: leg_symb.
    move=> leg_symb. rewrite -oddS.
    rewrite (@ltn_predK 0); last by rewrite prime_gt0.
    move: pP => /andP [pL0 pP].
    move: (even_prime pP) => //= [p2 | podd].
    rewrite p2 //= in pL2.
    rewrite //=.
    move: leg_symb.
    rewrite !dvdzE //= subzn; last by rewrite prime_gt0.
    rewrite !divz_nat addn1 !Euclid_dvd1; last by [].
    rewrite /exprz //= (intEsg (-1)) //= mulr1 sgz_odd; last by [].
    rewrite !subn1 !divn2 => leg_symb.
    apply/negP => oddhalf.
    move: leg_symb.
    rewrite oddhalf //= expr1 sgzN1 eqz_mod_dvd.
    rewrite -(mul1r (-1)%R) -mulrDl -PoszD addn1 -!mulrzz mulrN1z !dvdzE //=.
    rewrite dvdn_divisors; last by [].
    rewrite /divisors //= /(_ \in _) //=.
    have -> : p == 1 = false.
            apply negbTE. apply/eqP => p1.
            rewrite p1 //= in pL2.
    have -> : p == 2 = false.
        apply negbTE. apply/eqP => p2.
        rewrite p2 //= in pL2.
    rewrite //= => /eqP.
    Set Printing Coercions.
    rewrite eqz_mod_dvd dvdzE //= !add1n.
    move: pL2 pP.
    case: p => // p.
    move=> pL2 pP.
    rewrite subzn; last by rewrite prime_gt0.
    rewrite //= /legendre_symb => /dvdnP [k Hk].
    rewrite subzn; last by rewrite prime_gt0.
    rewrite divz_nat addn1 /exprz.
    rewrite /exprz //= (intEsg (-1)) //= mulr1 sgz_odd; last by [].
    rewrite Hk.
    have -> : 4 = 2 * 2 by rewrite //=.
    rewrite !muln2 divn2 sgzN1 dvdzE //=.
    rewrite -muln2 mulnA muln2.
    move: (half_bit_double (k*2) false).
    rewrite //= add0n. move=> ->.
    rewrite muln2 odd_double //= expr0 eqxx //=.
    Qed.

    Lemma legendre_symb_or (p a : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
        ((legendre_symb pL2 pP a) == 1)%Z || ((legendre_symb pL2 pP a) == -1)%Z || ((legendre_symb pL2 pP a) == 0)%Z.
    Proof.
    rewrite /legendre_symb.
    case: (a ^ ((p - 1) %/ 2)%Z  == 1  %[mod p])%Z => //=.
    case: (p %| a)%Z => //=.
    Qed.

    Lemma legendre_symb_mod (p a b : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
        ((legendre_symb pL2 pP a) == (legendre_symb pL2 pP b)) = ((legendre_symb pL2 pP a) == (legendre_symb pL2 pP b) %[mod p])%Z.
    Proof.
    move: (legendre_symb_or a pL2 pP) => /orP [/orP [/eqP ->|/eqP ->] |/eqP ->].
    apply Bool.eq_true_iff_eq. split.
        move=> /eqP ->; rewrite eqxx //=.
    move: (legendre_symb_or b pL2 pP) => /orP [/orP [/eqP ->|/eqP ->] |/eqP ->].
        rewrite //=.
    rewrite eqz_mod_dvd.
    have -> : (1%Z - (-1)%Z)%R = 2%Z.
        rewrite //=.
    move: pP pL2.
    case: p => // p.
    rewrite dvdzE ltz_nat addn1 //= => pP pL2.
    rewrite gtnNdvd; last by []; last by [].
    rewrite //=.
    rewrite eqz_mod_dvd dvdzE //= addn0.
    move: pP pL2. case: p => // p //= pP.
    rewrite Euclid_dvd1; last by [].
    rewrite //=.
    apply Bool.eq_true_iff_eq. split.
    move=> /eqP ->. by rewrite eqxx.
    move: (legendre_symb_or b pL2 pP) => /orP [/orP [/eqP ->|/eqP ->] |/eqP ->].
    rewrite eqz_mod_dvd.
    have -> : ((-1)%Z - 1%Z)%R = (-2)%Z.
        rewrite //=.
    rewrite dvdzE //=.
    move: pL2 pP. case: p => p //= pL2 pP.
    rewrite gtnNdvd; last by []; last by [].
    rewrite //=.
    rewrite //=.
    rewrite eqz_mod_dvd dvdzE //= subn0.
    move: pL2 pP. case: p => p //= pL2 pP.
    rewrite Euclid_dvd1; last by [].
    rewrite //=.
    move: (legendre_symb_or b pL2 pP) => /orP [/orP [/eqP ->|/eqP ->] |/eqP ->].
    apply Bool.eq_true_iff_eq. split.
        rewrite //=. 
    rewrite eqz_mod_dvd dvdzE //= subn0.
    move: pP pL2. case: p => p pP pL2 //=.
    rewrite Euclid_dvd1; last by [].
    rewrite //=.
    apply Bool.eq_true_iff_eq. split.
        rewrite //=.
    rewrite eqz_mod_dvd dvdzE //= add0n.
    move: pP pL2. case: p => p pP pL2 //=.
    rewrite Euclid_dvd1; last by [].
    rewrite //=.
    rewrite !eqxx //=.
    Qed.

    Lemma legendre_symb_mul (p a b : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
        (legendre_symb pL2 pP (a * b)%R) = ((legendre_symb pL2 pP a) * (legendre_symb pL2 pP b))%R.
    Proof.
    rewrite /legendre_symb. Set Printing Coercions.
    move: pP pL2. case: p => // p.
    move=> pP pL2.
    rewrite -mulrzz exprz_pMzl.
    move: pP pL2.
    rewrite !mulrzz => pP pL2.
    rewrite -modzMml -modzMmr.
    case pDa : (p %| `|a|).
    have -> : (a ^ ((Posz p - 1) %/ 2)%Z %% Posz p)%Z = (0%Z %% Posz p)%Z.
        apply/eqP. rewrite eqz_mod_dvd subr0 dvdzE //=.
        rewrite subzn; last by rewrite prime_gt0.
        rewrite divz_nat addn1 /exprz abszX Euclid_dvdX; last by [].
        rewrite pDa //= subn1 divn2 half_gt0 ltn_predRL //=.
    rewrite {1}mod0z mul0r !dvdzE //= abszM Euclid_dvdM; last by [].
    rewrite pDa //= !eqz_mod_dvd sub0r !dvdzE //= Euclid_dvd1; last by [].
    rewrite mul0r //=.
    rewrite !dvdzE //= pDa abszM Euclid_dvdM; last by [].
    rewrite pDa //=.
    case pDb : (p %| `|b|).
    have -> : (b ^ ((Posz p - 1) %/ 2)%Z %% Posz p)%Z = (0%Z %% Posz p)%Z.
        apply/eqP. rewrite eqz_mod_dvd subr0 dvdzE //=.
        rewrite subzn; last by rewrite prime_gt0.
        rewrite divz_nat addn1 /exprz abszX Euclid_dvdX; last by [].
        rewrite pDb //= subn1 divn2 half_gt0 ltn_predRL //=.
    rewrite {1}mod0z mulr0 eqz_mod_dvd sub0r dvdzE //= Euclid_dvd1; last by [].
    rewrite mulr0 //=.
    have {}pDa : ~ (p %| a)%Z.
        rewrite dvdzE //= pDa //.
    have {}pDb : ~ (p %| b)%Z.
        rewrite dvdzE //= pDb //.
    move : (@primez.pred_primez_half_mod b p pP pDb) => /orP [/eqP ->|/eqP ->].
        rewrite eqxx modzMm !mulr1 //=.
    move : (@primez.pred_primez_half_mod a p pP pDa) => /orP [/eqP -> |/eqP ->].
        rewrite modzMm !eqz_mod_dvd !dvdzE.
        have -> : ((1 * -1 - 1)%R = -2)%Z by rewrite //=.
        rewrite //= subnn dvdn0 mul1r //=.
    rewrite modzMm !eqz_mod_dvd !dvdzE //= muln1 subnn dvdn0 addn0.
        by case: (p %| 2)%N.
    rewrite subzn. rewrite divz_nat addn1 lez_nat leq0n //=.
    rewrite ltz_nat addn1 in pL2. move: pP pL2. by case: p.
    Qed.

(* End Legendre. *)