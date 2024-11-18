From contributions Require Import primez.
From mathcomp Require Import all_ssreflect all_algebra.
From extra Require Import euler.

Set Implicit Arguments.     
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Minhas possíveis contribuições: *)

Definition resz_quad p a := has (fun i => ((i * i)%:Z  == a %[mod p])%Z) (iota 0 `|p|).

Definition legendre_symb {p : int} (pL2 : (2 < p)%R) (pP : primez.primez p) (a : int) :=
    if (p %| a)%Z then 0%Z
    else if (resz_quad p a) then 1%Z else (-1)%Z.

Lemma eulerz_criterion {p : int} (pL2 : (2 < p)%R) (pP : primez.primez p) (a : int):
    (a ^ ((p - 1) %/ 2)%Z = (legendre_symb pL2 pP a) %[mod p])%Z.
Proof.
move: pL2 pP.
case: p => // p.
rewrite /legendre_symb ltz_nat addn1 => pL2 /andP [_ /= pP].
rewrite subzn; last by rewrite prime_gt0.
rewrite divz_nat addn1 /exprz.
case pDa: (p %| a)%Z.
    rewrite -(modzXm _ a).
    move: pDa.
    rewrite -{1}(GRing.subr0 a) -eqz_mod_dvd => /eqP ->.
    rewrite mod0z -GRing.rmorphXn /= natrXE exp0n.
    by rewrite mod0z.
    by rewrite subn1 divn2 half_gt0 ltn_predRL pL2.
case resz_quad_case: (resz_quad p a).
    move: resz_quad_case => /hasP /= [x].
    rewrite -(modzXm _ a).
    rewrite mem_iota add0n => /andP [xL0 xLp] /eqP xmod.
    rewrite -xmod.
    rewrite modzXm.
    rewrite -GRing.rmorphXn /=.
    rewrite mulnn natrXE -expnM mul2n divn2 subn1.
    rewrite halfK.
    have: (odd p.-1) = false.
        move: pL2 pP pDa xLp xmod.
        case: p => //= p pL2 pP pDa xLp xmod.
        apply/eqP. rewrite eqbF_neg -oddS.
        move: (even_prime pP) pL2 => [-> //= | -> //=].
    move=> -> //=. 
    rewrite subn0.
    rewrite GRing.rmorphXn /= exprnP -subn1 -subzn; last by apply prime_gt0.
    rewrite primez.fermatz_little_pred //=.
rewrite -(GRing.subr0 (Posz x)) -eqz_mod_dvd !modz_nat => /eqP xmod0.
move: xmod. rewrite -modz_mod !modz_nat -modnMml.
injection xmod0 => ->.
rewrite mod0n mul0n -modz_nat mod0n.
move=> /eqP.
rewrite eqz_mod_dvd dvdzE GRing.sub0r abszN -dvdzE pDa //.
pose m := `|a %% p|%Z.
rewrite -(modzXm _ a) -(@gez0_abs (a %% p)%Z); last first.
    rewrite modz_ge0 //. move: pP pL2 pDa resz_quad_case m. case: p => // p.
rewrite -/m.
have pDm : (p %| m)%N = false.
    apply/negP.
    rewrite -(absz_nat p) -(absz_nat m) -dvdzE -(GRing.subr0 (Posz m)) //=.
    move: pDa => /negP.
    rewrite -(GRing.subr0 a) -!eqz_mod_dvd /not => pDa pDm.
    apply pDa.
    rewrite -modz_mod -(@gez0_abs (a %% p)%Z); last first.
        rewrite modz_ge0 //. move: m pP pL2 pDa pDm resz_quad_case. case: p => // p.
    rewrite -/m.
    apply pDm.
have not_res_quad: res_quad p m = false.
    apply/negP.
    rewrite /res_quad.
    move=> /hasP //= [x]. rewrite mem_iota add0n => /andP [_ xLp] /eqP xmod.
    move: resz_quad_case. rewrite /resz_quad. move=>/hasP H. apply H.
    clear H. exists x.
    rewrite /= mem_iota add0n xLp //.
    rewrite -(modz_mod a) -(@gez0_abs (a %% p)%Z); last first.
        rewrite modz_ge0 //. move: m xLp pDm pP pL2 pDa xmod. case: p => // p.
    rewrite -/m !modz_nat xmod //.
    rewrite subn1 divn2.
    rewrite -(modz_mod (-1)%Z) modNz_nat; last by apply prime_gt0.
    rewrite mod0n GRing.subr0 -modz_mod. rewrite -GRing.rmorphXn /= modz_nat.
    rewrite euler_criterion.
    rewrite not_res_quad //= -modz_nat modz_mod 
    -subn1 -subzn. by [].
    by rewrite prime_gt0. by rewrite pP.
    by rewrite pDm.
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
rewrite /legendre_symb. rewrite /resz_quad amodb.
have -> : (p %| a)%Z = (p %| b)%Z.
    rewrite -(GRing.subr0 a) -(GRing.subr0 b) -!eqz_mod_dvd amodb //=.
by [].
Qed.

Lemma legendre_symb_Ndvd (p a b : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
    ~~(p %| a)%Z -> (legendre_symb pL2 pP (a^2)) == 1.
Proof.
rewrite /legendre_symb.
move: pP pL2.
case: p => // p pP pL2.
rewrite exprSz expr1z (primez.Euclidz_dvdM _ _ pP) Bool.orb_diag -eqbF_neg.
move=> /eqP pDa. rewrite pDa.
apply /eqP.
have: (resz_quad (Posz p) (a * a)).
    apply/hasP. rewrite /=.
    have H: (`|a %% Posz p|%Z < p)%N.
        rewrite -ltz_nat gez0_abs; last first. 
            rewrite modz_ge0 //.
            apply /eqP => pE0. move: pP. rewrite pE0 //.
        rewrite ltz_pmod //=.
        rewrite ltz_nat prime_gt0 //.
    pose x := `|(a %% Posz p)%Z|.
    exists x.
    rewrite mem_iota.
    rewrite /x //= PoszM.
    rewrite /x //= PoszM.
        rewrite (@gez0_abs (a %% p)%Z); last first.
            rewrite modz_ge0 //.
            apply /eqP => pE0. move: pP. rewrite pE0 //.
    by rewrite modzMml modzMmr.
move=> -> //=.
Qed.

Lemma legendre_symb_Neg1 (p : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
    ((legendre_symb pL2 pP (-1)) == 1) = (p == 1 %[mod 4])%Z.
Proof.
apply Bool.eq_true_iff_eq.
split.
move: pL2 pP.
case: p => // p pL2 pP /eqP leg1.
move: (eulerz_criterion pL2 pP (-1)).
rewrite leg1 subzn; last by rewrite prime_gt0.
rewrite divz_nat addn1 (intEsg (-1)) //= GRing.mulr1 subn1 divn2 /exprz sgz_odd; last by [].
case podd: (odd p.-1./2).
    rewrite //= GRing.expr1. move=> /eqP.
    rewrite eqz_mod_dvd /sgz //=.
    have -> : ((-1) - 1%Z)%R = (-2)%Z by [].
    rewrite dvdzE //=.
    rewrite -(subn0 2%N) -eqn_mod_dvd //=.
    rewrite modn_small //= mod0n //=.
    rewrite //= GRing.expr0.
move=> _. rewrite eqz_mod_dvd subzn; last by rewrite prime_gt0. rewrite dvdzE //= !add1n. apply/dvdnP.
exists (p.-1./2./2).
have -> : (4 = 2 * 2)%N by [].
rewrite mulnA !muln2 subn1.
rewrite halfK podd //= subn0 halfK.
have: (odd p.-1) = false. apply /eqP.
rewrite eqbF_neg -oddS prednK; last by rewrite prime_gt0.
case: (@even_prime p).
    by [].
move=> p2. clear leg1. rewrite ltz_nat p2 //= in pL2.
rewrite //=.
move=> -> //=; rewrite subn0 //.
move: pL2 pP.
case: p => // p pL2 pP.
rewrite eqz_mod_dvd dvdzE //= !add1n subzn; last by rewrite prime_gt0.
rewrite //=. move=> /dvdnP [k Hk].
move: (eulerz_criterion pL2 pP (-1)).
    rewrite subzn; last by rewrite prime_gt0.
    rewrite divz_nat addn1 divn2 Hk.
    have -> : (4 = 2 * 2)%N by [].
    rewrite mulnA !muln2.
    move: (half_bit_double k.*2 false).
    rewrite //= add0n => ->.
    rewrite -{1}(@ltr0_sgz _ (-1)%Z); last by [].
    rewrite /exprz sgz_odd; last by [].
    rewrite odd_double //= GRing.expr0.
rewrite /legendre_symb dvdzE //= Euclid_dvd1; last by [].
case: (resz_quad (Posz p) (-1)).
    rewrite //=.
move=> /eqP. rewrite eqz_mod_dvd.
have -> : (1 - (-1)%Z)%R = 2 by [].
rewrite dvdzE //= -(subn0 2%N) -eqn_mod_dvd //=.
rewrite modn_small //= mod0n //=.
Qed.

Lemma legendre_symb_or (p a : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
    ((legendre_symb pL2 pP a) == 1)%Z || ((legendre_symb pL2 pP a) == -1)%Z || ((legendre_symb pL2 pP a) == 0)%Z.
Proof.
rewrite /legendre_symb.
case pDa : (p %| a)%Z => //=.
case: (resz_quad p a) => //=.
Qed.

Lemma legendre_symb_mod (p a b : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
    ((legendre_symb pL2 pP a) == (legendre_symb pL2 pP b)) = ((legendre_symb pL2 pP a) == (legendre_symb pL2 pP b) %[mod p])%Z.
Proof.
move: pL2 pP.
case: p => // p pL2 pP.
move: (legendre_symb_or a pL2 pP) => /orP [/orP [/eqP ->|/eqP ->] |/eqP ->].
move: (legendre_symb_or b pL2 pP) => /orP [/orP [/eqP ->|/eqP ->] |/eqP ->].
    by rewrite !eqxx.
    rewrite eqz_mod_dvd dvdzE //= addn1.
    rewrite gtnNdvd //=.
    rewrite eqz_mod_dvd GRing.subr0 dvdzE /= gtnNdvd //=.
    rewrite prime_gt1 //.
move: (legendre_symb_or b pL2 pP) => /orP [/orP [/eqP ->|/eqP ->] |/eqP ->].
    rewrite eqz_mod_dvd dvdzE /= addn0 gtnNdvd //=.
    by rewrite !eqxx.
    rewrite eqz_mod_dvd dvdzE /= sub0n gtnNdvd //.
    by rewrite prime_gt1.
move: (legendre_symb_or b pL2 pP) => /orP [/orP [/eqP ->|/eqP ->] |/eqP ->].
    rewrite eqz_mod_dvd dvdzE /= subn0 gtnNdvd //=.
    by rewrite prime_gt1.
    rewrite eqz_mod_dvd dvdzE /= add0n gtnNdvd //=.
    by rewrite prime_gt1.
    by rewrite !eqxx.
Qed.

Lemma res_quad_eq_leg (p a : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
    legendre_symb pL2 pP a = (if (p %| a)%Z then 0%Z else if 
    res_quad `|p| (`|a %% p|%Z) then 1%Z else (-1)%Z).
Proof.
move: pL2 pP.
case: p => // p pL2 pP.
rewrite absz_nat /legendre_symb /res_quad.
case pDa : (p %| a)%Z => //.
case Hi: (has (fun i : nat => i * i  == `|(a %% p)%Z|  %[mod p]) (iota 0 p))%N.
move: Hi => /hasP [x Hi].
rewrite mem_iota add0n in Hi => Hx.
have -> : resz_quad (Posz p) a.
    rewrite /resz_quad.
    rewrite -(modz_mod a) -(@gez0_abs (a %% p)%Z); last first.
        rewrite modz_ge0 //. apply/eqP. move=> pE0. rewrite pE0 // in pP.
    move: Hi => /andP [_ Hi].
    rewrite //=.
    apply/hasP.
    exists x.
    rewrite mem_iota add0n //=.
    rewrite //= !modz_nat. apply/eqP. f_equal.
    apply/eqP. apply Hx. rewrite //.
apply/eqP.
have: ~~ (resz_quad (Posz p) a).
    rewrite /resz_quad /=.
    rewrite -(modz_mod a) -(@gez0_abs (a %% p)%Z); last first.
        rewrite modz_ge0 //. apply/eqP => pE0. rewrite pE0 // in pP.
    apply/negP => /hasP //= [x H amod].
    move: Hi => /eqP Hi.
    rewrite eqbF_neg in Hi.
    move: Hi => /negP Hi.
    apply Hi.
    apply/hasP.
    exists x.
    move: H.
    rewrite //=.
    move: amod. rewrite !modz_nat => /eqP amod.
    injection amod => {}amod.
    rewrite amod eqxx //.
rewrite -eqbF_neg => /eqP -> //.
Qed.

Lemma legendre_symb_mul (p a b : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
    (legendre_symb pL2 pP (a * b)%R) = ((legendre_symb pL2 pP a) * (legendre_symb pL2 pP b))%R.
Proof.
move: pL2 pP.
case: p => // p pL2 pP.
have pDp2 : (p %| p.-2)%N = false.
    rewrite -subn2 dvdn_subr.
    rewrite gtnNdvd //. by rewrite prime_gt1. 
    by rewrite dvdnn.
rewrite !res_quad_eq_leg primez.Euclidz_dvdM; last by [].
case pDa: (p %| a)%Z => //=.
    by rewrite GRing.mul0r.
case pDb: (p %| b)%Z => //=.
    by rewrite GRing.mulr0.
rewrite -modzMml -modzMmr.
pose m := `|(a %% p)%Z|.
pose n := `|(b %% p)%Z|.
rewrite -(@gez0_abs (a %% p)%Z); last first.
    rewrite modz_ge0 //. apply/eqP. move=> pE0. rewrite pE0 // in pP.
rewrite -(@gez0_abs (b %% p)%Z); last first.
    rewrite modz_ge0 //. apply/eqP. move=> pE0. rewrite pE0 // in pP.
rewrite -/m -/n -PoszM modz_nat !absz_nat /res_quad modn_mod.
have pDm : ~~ (p %| m)%N.
    rewrite /m -{1}(absz_nat p) -dvdzE.
    apply/negP. rewrite -(GRing.subr0 (a %% p)%Z) -eqz_mod_dvd.
    rewrite modz_mod eqz_mod_dvd GRing.subr0 pDa //=. 
have pDn : ~~ (p %| n)%N.
    rewrite /m -{1}(absz_nat p) -dvdzE.
    apply/negP. rewrite -(GRing.subr0 (b %% p)%Z) -eqz_mod_dvd.
    rewrite modz_mod eqz_mod_dvd GRing.subr0 pDb //=.
have pDmn: ~~ (p %| m * n)%N.
    rewrite Euclid_dvdM; last by [].
    rewrite -eqbF_neg in pDm.
    rewrite -eqbF_neg in pDn.
    move: pDm pDn => /eqP -> /eqP -> //=.
clear pDa pDb.
move: pP => /andP [_ //= pP].
rewrite ltz_nat addn1 in pL2.
move: (euler_criterion _ _ pP pDm) => Em.
move: (euler_criterion _ _ pP pDn) => En.
move: (euler_criterion _ _ pP pDmn) => Emn.
case Hm: (has (fun i : nat => i * i  == m  %[mod p])%N (iota 0 p)).
case Hn: (has (fun i : nat => i * i  == n  %[mod p])%N (iota 0 p)).
move: Hm Hn => /hasP [x] xLp /eqP Hx /hasP [y] yLp /eqP Hy.
move: xLp yLp. rewrite !mem_iota add0n => xLp yLp.
have -> : (has (fun i : nat => i * i  == m * n  %[mod p])%N (iota 0 p)).
    apply/hasP. exists ((x * y) %% p)%N.
    rewrite mem_iota add0n ltn_pmod //.
    rewrite prime_gt0 //.
rewrite modnMml modnMmr -mulnA (mulnC y) -mulnA mulnA -modnMml -modnMmr Hx Hy modnMml modnMmr eqxx //.
rewrite //=.
rewrite GRing.mul1r.
have -> : (has (fun i : nat => i * i  == m * n  %[mod p])%N (iota 0 p)) = false.
    rewrite /res_quad Hm in Em.
    rewrite /res_quad Hn in En.
    rewrite -(muln1 (n ^ p.-1./2)) -modnMmr -Em modnMmr -expnMn mulnC in En.
    rewrite /res_quad En in Emn.
    apply/eqP. rewrite eqbF_neg. apply/negP => Hmn.
    rewrite Hmn in Emn. move: Emn => /eqP.
    rewrite eqn_mod_dvd. rewrite subn1 pDp2 //.
    rewrite ltn_predRL prime_gt1 //. rewrite //.
case Hn: (has (fun i : nat => i * i  == n  %[mod p])%N (iota 0 p)).
    rewrite GRing.mulr1.
    rewrite /res_quad Hm in Em.
    rewrite /res_quad Hn in En.
    rewrite -(muln1 (m ^ _) ) -modnMmr -En modnMmr in Em.
    rewrite -expnMn in Em.
    rewrite Em /res_quad in Emn.
    move: Emn => /eqP.
    case Hmn: (has (fun i : nat => i * i  == m * n  %[mod p])%N (iota 0 p)).
    rewrite eqn_mod_dvd.
    rewrite subn1 pDp2 //=.
    rewrite ltn_predRL prime_gt1 //.
rewrite //=.
have -> : ((-1)%Z * (-1)%Z)%R = 1%Z by [].
rewrite expnMn in Emn.
rewrite /res_quad Hm in Em.    
rewrite /res_quad Hn in En.
rewrite -modnMml -modnMmr Em En modnMml modnMmr in Emn.
case Hmn: (has (fun i : nat => i * i  == m * n  %[mod p])%N (iota 0 p)) => //.
move: Emn => /eqP.
rewrite /res_quad Hmn eqn_mod_dvd -{3}(muln1 p.-1).
rewrite -mulnBr subn1 (Euclid_dvdM _ _ pP) pDp2 orbC /=.
rewrite -subn1 dvdn_subr.
rewrite Euclid_dvd1 //=.
rewrite prime_gt0 //=.
rewrite dvdnn //=.
rewrite muln1 mulnn -{1}(expn1 p.-1) leq_pexp2l //=.
rewrite -ltnS prednK.
rewrite prime_gt1 //.
rewrite prime_gt0 //.
Qed.