From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.     
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope int_scope with Z.
Open Scope int_scope.

Definition primez (n : int) := (0 <= n)%R && (prime `|n|).

Lemma primez_gcd1 (a p : int):
(primez p) -> ~~ (p %| a) -> gcdz p a == 1.
Proof.
case: p => // p /andP[pL2 /= pP].
rewrite dvdzE /=.
move: pP.
by move=> /(prime_coprime `|a|) <-.  
Qed.

Lemma primez_coprime (p a : int):
primez p -> (0 < `|a| < p)%R -> coprimez a p.
Proof.
case: p => p // /andP[pL2 /=pP] /andP[aL0 aLp].
rewrite coprimez_sym coprimezE /= prime_coprime.
apply/negPf. rewrite gtnNdvd //. by [].
Qed.
    
Lemma mulr_modp_neq0 (a b p : int):
primez p -> a * b = 1 %[mod p] -> b != 0.
Proof.
case: p => p // /andP[pL2 /= pP] aMb.
apply/negP => /eqP bE0.
move: aMb => /eqP. rewrite bE0 GRing.mulr0 eqz_mod_dvd.
rewrite GRing.add0r dvdzE /=. apply/negP. by rewrite (Euclid_dvd1 pP).
Qed.

Lemma primez_neq0 (p : int): 
primez p -> p != 0.
Proof.
case: p => p //.
by case: p.
Qed.

Lemma coprime0z (a b : int):
(coprimez 0 b) -> (`|b| == 1%R).
Proof.
by rewrite /coprimez gcd0z.
Qed.

Lemma primez_abs (p : int):
(primez p) -> p = `|p|.
Proof.
by case: p => p //.
Qed.

Lemma primez_gt0 (p : int):
(primez p) -> (0 < p)%R.
Proof.
case: p => // p. by case: p.
Qed.
    
Lemma primez_gt1 (p : int):
(primez p) -> (1 < p)%R.
Proof.
case: p => // p. case: p => // p.
rewrite ltz_nat; case: p => // p.
Qed.

Lemma primez_le2 (p : int):
(primez p) -> (2 <= p)%R.
Proof.
case: p => // p ; case: p => // p; case: p => // p.
Qed.

Lemma Euclidz_dvd1 (p : int):
(primez p) -> ~~(p %| 1).
Proof.
case: p => // p. rewrite dvdzE /= dvdn1.
by case: p => // p; case: p => // p.
Qed.

Lemma Euclidz_dvdM (a b p : int):
(primez p) -> (p %| (a * b)%R) = (p %| a) || (p %| b).
Proof.
rewrite /primez => /andP [pL0 pP]. rewrite !dvdzE abszM.
apply (prime.Euclid_dvdM _ _ pP).
Qed.

Lemma primez_1modp (p : int):
primez p -> 1 %% p = 1.
Proof.
move=> pP. move: (primez_gt1 pP) (primez_abs pP) => pL1 pabs.
rewrite pabs modz_small. by [].
apply /andP. split.
    by [].
    by rewrite -pabs.
Qed.

(*  A prova do seguinte lema se baseou na prova do lema      
"prime_modn_expSn" disponível em: https://github.com/thery/
mathcomp-extra/blob/640bc1a2634a609b8fd8a7c2023654ac3d9bc0a8/rsa.v *)
Lemma primez_modn_expSn (p n : int) : 
(0 <= n)%R -> primez.primez p -> ((n + 1) ^ p)%R = ((n ^ p) + 1)%R %[mod p].
Proof.
case: n => // n nL0.
case: p => // p pP.
rewrite -[((_ ^ _) + 1)%R]GRing.addr0.
rewrite -PoszD /exprz -!GRing.rmorphXn //= natrXE -PoszD !modz_nat addnC.
apply f_equal.
rewrite add1n addn1 addn0.
by apply prime_modn_expSn.
Qed.

(*  A prova do seguinte lema se baseou na prova do lema 
"fermat_little" disponível em: https://github.com/thery/
mathcomp-extra/blob/640bc1a2634a609b8fd8a7c2023654ac3d9bc0a8/rsa.v  *)
Lemma fermatz_little a p : primez p -> a ^ p = a %[mod p].
Proof.
case: p => // p.
move=> /andP[pL0 pP].
clear pL0.
rewrite absz_nat in pP.
rewrite /exprz -modzXm -{2}(modz_mod a) -(@gez0_abs (a %% p)%Z);
    last by apply modz_ge0; move: pP; case: p => // p.
rewrite /exprz -GRing.rmorphXn //= natrXE !modz_nat. 
f_equal.
by apply fermat_little.
Qed.

Lemma fermatz_little_pred (a p : int) : 
primez p -> ~(p %| a) -> a ^ (p - 1) = 1 %[mod p].
Proof. 
case: p => // p /andP [_ pP].
rewrite absz_nat in pP.
move=> /negP /dvdz_mod0P /eqP pNDa.
rewrite -(@gez0_abs (a %% p)%Z) in pNDa;
    last by apply modz_ge0; move: pP; case: p => // p.
rewrite subzn; last by apply (prime_gt0 pP).
rewrite /exprz -modzXm -(@gez0_abs (a %% p)%Z); last by
    apply modz_ge0; move: pNDa pP; case: p => // p.
rewrite -GRing.rmorphXn !modz_nat natrXE; f_equal.
pose x := `|(a %% Posz p)%Z|.
have: ~ (p %| x)%N.
    move=> pDx. rewrite gez0_abs in pNDa; last first.
        rewrite modz_ge0 //. move: pP x pDx.
        case: p => // p.
    move: (prime_gt0 pP) => pL0.
    rewrite -ltz_nat in pL0.
    move: (ltz_pmod a pL0).
    rewrite -(@gez0_abs (a %% p)%Z); last first.
        rewrite modz_ge0 //. move: pP x pDx pL0 pNDa.
        case: p => // p.
    rewrite ltz_nat.
    rewrite /x in pDx.
    rewrite ltz_nat in pL0.
    rewrite -(@gez0_abs (a %% p)%Z) in pNDa; last first.
        rewrite modz_ge0 //. move: pP x pDx pL0.
        case: p => // p.
    move=> aMpLp.
    have aMpL0: `|(a %% Posz p)%Z|%N > 0.
        rewrite absz_gt0. apply/negP => /eqP ampD0.
        move: pNDa. rewrite ampD0 //.
    move: (dvdn_leq aMpL0 pDx). rewrite leqNgt aMpLp //.
move: pNDa.
rewrite -!/x.
move=> _ pNDa.
have a_gt0 : 0 < x by case: x pNDa.
have aCp : coprime x p by rewrite coprime_sym prime_coprime //; apply/negP.
have aE : ((egcdn x p).1 * x = 1 %[mod p])%N.
by case: egcdnP => //= km kn -> _; rewrite (eqP aCp) modnMDl.
rewrite -[_^ _]muln1 -modnMmr -[in LHS]aE // modnMmr.
rewrite subn1 mulnC -mulnA -expnS prednK ?prime_gt0 //.
by rewrite -modnMmr fermat_little // modnMmr aE.
Qed.

Lemma pred_primez_half_mod (a p : int):
primez p -> ~(p %| a) -> (a ^ ((p - 1) %/ 2)%Z == 1 %[mod p]) || (a ^ ((p - 1) %/ 2)%Z == -1 %[mod p]).
Proof.
case: p => // p pP pDa.
move: (fermatz_little_pred pP pDa).
rewrite -{1}(@mulzK (Posz p - 1) 2); last by rewrite //=.
rewrite !(@subzn p _); last by rewrite -ltz_nat (primez_gt0 pP).
move: pP => /andP[pL0 pP]. rewrite //= in pP.
move: (even_prime pP) => [pE2 | podd].
    rewrite pE2 //=.
have: (2%Z %| Posz (p - 1)).
    rewrite dvdzE //= dvdn2 -oddS -addn1 subnK //=.
    by rewrite prime_gt0 //=.
move=> pD2. rewrite -(divz_mulAC); last by rewrite pD2.
rewrite divz_nat /exprz //= -!(modzXm _ a _).
    rewrite -(@gez0_abs (a %% p)%Z); last first.
        apply modz_ge0. move: pDa podd pD2 pP pL0. case: p => //.
move: pDa pL0 pP podd pD2; case: p => {}p.
move=> pD2 podd pP pL0 pDa //=.
move=> pDa pL0 pP podd pD2.
have pDamod: ~ (p.+1 %| (a %% p.+1))%Z.
    move: pDa. rewrite -{1}(GRing.subr0 a) -{1}(GRing.subr0 (a %% p.+1)%Z) -!eqz_mod_dvd.
    by rewrite modz_mod.
rewrite dvdzE in pDamod.
rewrite -!GRing.rmorphXn //= !natrXE.
case Hx : `|a %% Posz p.+1| => [|x].
    rewrite Hx //= in pDamod.
rewrite {1}modz_nat {1}(modz_nat 1 _) => xfermat.
injection xfermat => /eqP {}xfermat.
rewrite eqn_mod_dvd in xfermat.
rewrite -[X in (_ %| X)%N]subn0 in xfermat.
rewrite -eqn_mod_dvd expnM -{4}(exp1n 2%N) subn_sqr in xfermat.
rewrite eqn_mod_dvd //= subn0 Euclid_dvdM in xfermat.
rewrite -eqn_mod_dvd in xfermat.
apply/orP.
move: xfermat => /orP [xfermat|xfermat].
    by left; rewrite !modz_nat.
by right; rewrite eqz_mod_dvd //=.
by rewrite expn_gt0.
by [].
by [].
by rewrite expn_gt0.
Qed.

Lemma pred_primez_half_mod_full (a p : int):
primez p -> (a ^ ((p - 1) %/ 2)%Z == 1 %[mod p]) || (a ^ ((p - 1) %/ 2)%Z == -1 %[mod p]) || (a ^ ((p - 1) %/ 2)%Z == 0 %[mod p]).
Proof.
case: p => // p pP.
case: (@even_prime p) => //= [-> //= | podd].
case pDa : (p %| a).
apply/orP. right.
rewrite subzn; last by rewrite prime_gt0.
rewrite divz_nat addn1 /exprz eqz_mod_dvd dvdzE //= GRing.subr0 abszX.
rewrite dvdzE //= in pDa.
rewrite Euclid_dvdX; last by [].
rewrite pDa //= subn1 divn2 half_gt0 ltn_predRL //=.
apply odd_prime_gt2; rewrite //=.
apply/orP. left. apply pred_primez_half_mod; rewrite //=; rewrite pDa //=.
Qed.

Lemma if_quadratic_residuez p a:
(primez p) -> ~(p %| a) -> (exists (x : int), x ^ 2 == a %[mod p])%R -> 
(a ^ ((p - 1) %/ 2)%Z == 1 %[mod p]).
Proof. 
case: p => // p.
move=> pP pNDa [x /eqP Hx].
rewrite subzn; last by rewrite prime_gt0.
rewrite /exprz //= -modzXm addn1 mul1n.
rewrite -Hx modzXm.
rewrite /exprz //= addn1.
rewrite !exprnP exprz_exp -exprnP.
move: pP => /andP [pL0 pP].
move: (even_prime pP) => //= [-> | podd] //=.
rewrite mul2n divn2 halfK.
have -> : (odd (p - 1) = false).
    move: pNDa pL0 pP podd Hx.
    case: p => [ //= |p].
    move=> pNDa pL0 pP podd Hx.
    apply negbTE.
    rewrite subSS subn0 -oddS //.
rewrite //= subn0 exprnP -subzn.
apply/eqP.
apply fermatz_little_pred.
rewrite //=.
move=> pDx. apply pNDa. rewrite -(GRing.subr0 a) -eqz_mod_dvd.
rewrite -Hx /exprz //= addn1 GRing.expr2 eqz_mod_dvd GRing.subr0 Euclidz_dvdM.
rewrite pDx //=.
rewrite //=.
apply (prime_gt0 pP).
Qed.