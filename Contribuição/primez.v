From mathcomp Require Import all_ssreflect ssreflect eqtype all_algebra
ssrbool bigop ssrnat ssrint ssralg intdiv seq prime order perm zmodp all_solvable.
Import Order.Theory.
From Coq Require Import Logic.Decidable.

Import GRing.Theory.

Set Implicit Arguments.     
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*  Teoremas que deveriam estar na biblioteca: *)
Module missing.
    Lemma absz_div_mul (a n : int):
        ((a %/ n)%Z * n)%R = ((a %/ `|n|)%Z * `|n|)%R.
    Proof.
    case: n => n.
    { by []. }
    { 
        rewrite NegzE divzN -mulrzz mulNrNz mulrzz.
        rewrite [X in _ = ((_ %/ X)%Z * X)%R]ltz0_abs; last by [].
        by rewrite -mulrN1z mulNrNz mulrzz mulr1.
    }
    Qed. 

    Lemma absz_le_mul (a n : int):
        (((a %/ n)%Z * n)%R <= `|a|%R)%R.
    Proof.
    rewrite absz_div_mul.
    case: a => a.
    (* caso: a = |a| *)
    {
        rewrite -[X in (_ <= X)%R]abszE absz_nat divz_nat.
        apply div.leq_trunc_div.
    }
    (* caso: a = -|a| *)
    {
        rewrite NegzE.
        rewrite [X in (_ <= X)%R]ltz0_abs; last by [].
        rewrite -mulrN1z -[X in (_ <= X)%R]mulrN1z.
        rewrite mulrN1z mulNrNz mulrzz mulr1.
        case Hn : `|n| => [|k]. 
            rewrite -[X in ((_ %/ X)%Z * X <= _)%R]abszE Hn //=.
        rewrite divNz_nat; last by rewrite Hn //=.
        rewrite mulrC -mulrzz mulrNz. rewrite Hn.
        rewrite -abszE Hn mulrzz. 
        case H : (k.+1 * (div.divn a k.+1).+1) => [|x].
            move: H => /eqP H. rewrite -eqz_nat //= in H.
        move: H => /eqP H. rewrite -eqz_nat //= in H.
    }
    Qed.

    Lemma absz_mod (a n : int):
        (n != 0)%Z -> (a %% n)%Z = `|(a %% n)%Z|.
    Proof.
    rewrite /modz absz_div_mul.
    case: a => a.
    {   (* caso a seja um número positivo: *)
        rewrite abszE divz_nat subzn; 
            last by rewrite div.leq_trunc_div.
        by rewrite -abszE absz_nat. }
    {   (* caso a seja um negativo: *)
        rewrite NegzE => nD0.
        rewrite divNz_nat. 
        rewrite -[X in (_ + X)%R = _]mulrN1z.
        rewrite abszE.
        rewrite -[X in _ = `|(_ - X)|%R]mulrN1z.
        rewrite mulNrNz mulrzz mulr1.
        rewrite -[X in _ = `|_ + X|%R]mulrN1z.
        rewrite mulNrNz mulrzz mulr1.
        rewrite -mulrz_nat mulrzz mulr1.
        rewrite addrC -abszE distnEl.
            rewrite subzn. by rewrite -natz.
            rewrite mulnC div.ltn_ceil //=.
            by rewrite absz_gt0.
            rewrite mulnC div.ltn_ceil //=.
            by rewrite absz_gt0.
            by rewrite absz_gt0.    }
    Qed.

    Lemma dvdN_mod (p a : int):
        ~ (p %| a)%Z -> ~ (p %| (a %% p))%Z.
    Proof.
    rewrite !dvdzE -modz_abs.
    case: `|p| => {}p.
    by rewrite //= modz0 ; rewrite //=.
    have: `|(a %% p.+1)%Z| < `|p.+1|.
        rewrite -ltz_nat -absz_mod.
        by apply ltz_mod.
        by rewrite //=.
    rewrite //=. 
    move=> xDSp SpNDa SpDx.
    case Hx: `|(a %% p.+1)%Z| => [|x].
    move: Hx => /eqP.
    rewrite -eqz_nat -(absz_mod a).
    move=> /eqP /dvdz_mod0P => SpDa.
    rewrite dvdzE //= in SpDa. rewrite //=.
    move: Hx => /eqP.
    rewrite -eqz_nat -(absz_mod a).
    move=> /eqP => Hx.
    rewrite Hx in SpDx ; rewrite Hx in xDSp.
    have: p.+1 <= x.+1.
        apply dvdn_leq.
        by [].
        by [].
    rewrite //= in xDSp ; rewrite //= in SpDx.
    rewrite leqNgt xDSp //=. rewrite //=.
    Qed.
            
End missing.
(*  Fim dos teoremas que deveriam estar na biblioteca. *)

(* Module primez. *)
    Delimit Scope int_scope with Z.
    Open Scope int_scope.

    Definition primez (n : int) := (0 <= n)%R && (prime `|n|).
    
    Lemma primez_gcd1 (a p : int):
        (primez p) -> ~~ (p %| a) -> gcdz p a == 1.
    Proof.
    rewrite /primez.
    move=> /andP [H0 Hp]. rewrite dvdzE.
    move: Hp.
    by move=> /(prime_coprime `|a|) <-. 
    Qed.

    Lemma primez_coprime (p a : int):
        primez p -> (0 < `|a| < p)%R -> coprimez a p.
    Proof.
    move=> pP /andP[a_pos aLp].
    have a_pos' :  (0 < `|a|)%nat.
        move=>//.
    rewrite coprimez_sym coprimezE prime_coprime //=.
    apply/negP => /(div.dvdn_leq a_pos').
    move: pP. rewrite /primez. move=> /andP [pP p0].
    apply gez0_abs in pP.
    rewrite leqNgt -!ltz_nat.
    rewrite -pP in aLp.
    by rewrite abszE aLp.
    by move: pP; move=> /andP [pP p0].
    Qed.

    Lemma primez_Ndvd (p a : int):
        (primez p) -> (0 < a < p)%R -> ~~ (p %| a).
    Proof.
    move=> pP a0p.
    have {}Habs : a = `|a|.
        move: pP a0p. rewrite /primez => /andP [pL0 pP] /andP [aL0 aLp].
        symmetry. by apply gtz0_abs.
    rewrite Habs in a0p.
    move: (primez_coprime pP a0p).
    rewrite coprimezE dvdzE => apC.
    apply/negP => /div.dvdnP [k pDa].
    rewrite pDa /div.coprime div.gcdnC div.gcdnMl in apC.
    move: apC => /eqP apC.
    rewrite /primez apC in pP. move: pP => /andP [pL0 pP].
    rewrite //= in pP.
    Qed. 
        
    Lemma mulr_modp_neq0 (a b p : int):
        primez p -> a * b = 1 %[mod p] -> b != 0.
    Proof.
    move=> pP Hab. apply/eqP.
    move=> Hb. rewrite Hb in Hab.
    rewrite mulr0 in Hab.
    move: Hab => /eqP Hab.
    rewrite eqz_mod_dvd dvdzE //= subn0 in Hab.
    rewrite /primez in pP.
    move: pP => /andP [p0 pP].
    apply Euclid_dvd1 in pP.
    rewrite pP in Hab.
    move=>//.
    Qed.

    Lemma primez_neq0 (p : int): 
        primez p -> p != 0.
    Proof.
    move=> pP. apply /eqP.
    move=> p0. rewrite p0 //= in pP.
    Qed.

    Lemma coprime0z (a b : int):
        (coprimez 0 b) -> (`|b| == 1%R).
    Proof.
    by rewrite /coprimez gcd0z.
    Qed.

    Lemma primez_abs (p : int):
        (primez p) -> p = `|p|.
    Proof.
    rewrite /primez => /andP [p0 pP].
    rewrite gez0_abs //=.
    Qed.

    Lemma primez_gt0 (p : int):
        (primez p) -> (0 < p)%R.
    Proof.
    rewrite /primez => /andP [p0 pP].
    rewrite Num.Internals.le0r in p0.
    move: p0 => /orP [p0 | pL0].
        move: p0 => /eqP p0.
        rewrite p0 //= in pP.
    move=> //=.
    Qed.
        
    Lemma primez_gt1 (p : int):
        (primez p) -> (1 < p)%R.
    Proof.
    move=> pP. move: (primez_abs pP) => Hp.
    rewrite Hp. move: (primez_gt0 pP) => pL0.
    rewrite Hp in pL0. rewrite ltz_nat.
    rewrite ltz_nat in pL0. rewrite ltn_neqAle.
    apply/andP. split.
        apply/eqP. move=> H. rewrite /primez in pP.
        rewrite -H in pP. move: pP => /andP [p0 pP].
        rewrite //= in pP.
    move=>//.
    Qed.

    Lemma primez_le2 (p : int):
        (primez p) -> (2 <= p)%R.
    Proof.
    move=> pP. move: (primez_gt1 pP) => pL1.
    apply primez_abs in pP. rewrite pP. rewrite pP in pL1.
    rewrite lez_nat. rewrite ltz_nat in pL1.
    rewrite ltn_neqAle. by rewrite ltn_neqAle in pL1.
    Qed.

    Lemma Euclidz_dvd1 (p : int):
        (primez p) -> ~~(p %| 1).
    Proof.
    move=> pP. move: (primez_abs pP) => pabs.
    apply/negP. move=> pD1. rewrite dvdz1 in pD1.
    move: pD1 => /eqP pD1. rewrite pD1 in pabs.
    rewrite pabs //= in pP.
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

    (*  A prova do seguinte lema se baseou na prova do lema "prime_modn_expSn" 
        disponível em: https://github.com/thery/mathcomp-extra/blob/640bc1a2634a609b8fd8a7c2023654ac3d9bc0a8/rsa.v  *)

    Lemma primez_modn_expSn (p n : int) : (0 <= n)%R -> primez.primez p -> ((n + 1) ^ p)%R = ((n ^ p) + 1)%R %[mod p].
    Proof.
    case: n => // n nL0.
    case: p => // p pP.
    rewrite -[((_ ^ _) + 1)%R]addr0.
    (* Set Printing Coercions. *)
    rewrite -PoszD /exprz -!rmorphXn //= natrXE -PoszD !modz_nat addnC.
    apply f_equal.
    rewrite add1n addn1 addn0.
    by apply prime_modn_expSn.
    Qed.

    (*  A prova do seguinte lema se baseou na prova do lema "fermat_little" 
        disponível em: https://github.com/thery/mathcomp-extra/blob/640bc1a2634a609b8fd8a7c2023654ac3d9bc0a8/rsa.v  *)
    
    Lemma fermatz_little a p : primez p -> a ^ p = a %[mod p].
    Proof.
    case: p => // p.
    move=> /andP[pL0 pP].
    clear pL0.
    rewrite absz_nat in pP.
    rewrite /exprz -modzXm -{2}(modz_mod a) (missing.absz_mod a);
        last by apply/eqP; move=> p0; injection p0 => {}p0;
        rewrite p0 //= in pP.
    (* Set Printing Coercions. *)
    rewrite /exprz -rmorphXn //= natrXE !modz_nat. 
    f_equal.
    by apply fermat_little.
    Qed.

    Lemma fermatz_little_pred (a p : int) : primez p -> ~(p %| a) -> a ^ (p - 1) = 1 %[mod p].
    Proof. 
    case: p => // p /andP [_ pP].
    rewrite absz_nat in pP.
    move=> /negP /dvdz_mod0P /eqP pNDa.
    rewrite missing.absz_mod in pNDa;
        last by apply /eqP;
        move=> pE0;
        injection pE0 => {}pE0;
        rewrite pE0 //= in pP.
    rewrite subzn; last by apply (prime_gt0 pP).
    (* Set Printing Coercions. *)
    rewrite /exprz -modzXm (missing.absz_mod a);
        last by apply /eqP;
        move=> pE0;
        injection pE0 => {}pE0;
        rewrite pE0 //= in pP.
    rewrite -rmorphXn !modz_nat natrXE; f_equal.
    pose x := `|(a %% Posz p)%Z|.
    have: ~ (p %| x)%N.
        move=> pDx. rewrite -missing.absz_mod in pNDa.
        move: (prime_gt0 pP) => pL0.
        rewrite -ltz_nat in pL0.
        move: (ltz_pmod a pL0).
        rewrite missing.absz_mod.
        rewrite ltz_nat.
        rewrite /x in pDx.
        rewrite ltz_nat in pL0.
        rewrite missing.absz_mod in pNDa.
        have: `|(a %% Posz p)%Z|%N > 0.
            rewrite absz_gt0 missing.absz_mod //=.
        apply/eqP => pD0.
        injection pD0 => {}pD0.
        rewrite pD0 //= in pL0.
        move=> xL0 xLp.
        move: (dvdn_leq xL0 pDx) => pLx.
        rewrite ltn_geF // in xLp.
    apply/eqP => pE0.
    injection pE0 => {}pE0.
    rewrite pE0 //= in pL0.
    apply/eqP => pE0.
    injection pE0 => {}pE0.
    rewrite pE0 //= in pL0.
    apply/eqP => pE0.
    injection pE0 => {}pE0.
    rewrite pE0 //= in pP.
    clear pNDa.
    move=> pNDa.
    rewrite -/x.
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
    rewrite divz_nat /exprz //= -!(modzXm _ a _) (missing.absz_mod a);
    last by move: pDa pL0 pP podd pD2; case: p.
    move: pDa pL0 pP podd pD2; case: p => {}p.
    move=> pD2 podd pP pL0 pDa //=.
    move=> pDa pL0 pP podd pD2.
    move: (missing.dvdN_mod pDa) => pDamod.
    rewrite dvdzE in pDamod.
    rewrite -!rmorphXn //= !natrXE.
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
    rewrite divz_nat addn1 /exprz eqz_mod_dvd dvdzE //= subr0 abszX.
    rewrite dvdzE //= in pDa.
    rewrite Euclid_dvdX; last by [].
    rewrite pDa //= subn1 divn2 half_gt0 ltn_predRL //=.
    apply odd_prime_gt2; rewrite //=.
    apply/orP. left. apply pred_primez_half_mod; rewrite //=; rewrite pDa //=.
    Qed.

    Lemma if_quadratic_residuez p a:
        (primez p) -> ~(p %| a) -> 
        (exists (x : int), x ^ 2 == a %[mod p])%R -> 
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
    move=> pDx. apply pNDa. rewrite -(subr0 a) -eqz_mod_dvd.
    rewrite -Hx /exprz //= addn1 expr2 eqz_mod_dvd subr0 Euclidz_dvdM.
    rewrite pDx //=.
    rewrite //=.
    apply (prime_gt0 pP).
    Qed.

    Lemma quadratic_residue_only_if (p a : nat):
        (prime p)%N -> ~(p %| a)%N -> 
        (a ^ ((p - 1) %/ 2)%N == 1 %[mod p])%N -> (exists (x : nat), x ^ 2 == a %[mod p])%N.
    Proof.
        move=> pP pNDa.
        (* ... *)
    Abort.

    Close Scope int_scope.

(* End primez. *)