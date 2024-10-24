From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssreflect eqtype all_algebra
ssrbool bigop ssrnat ssrint ssralg intdiv seq prime order perm zmodp all_solvable.
Import Order.Theory.
From Coq Require Import Logic.Decidable.

Import GRing.Theory.

Set Implicit Arguments.     
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*  Algumas provas neste arquivo foram obtidas de https://github.com/thery/mathcomp-extra/ *)

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

(*  Módulo específico para primos inteiros: *)
Module primez.
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

End primez.

(*  Implementação de Inverso Multiplicativo em Coq *)
Module inversezmodp.
    Delimit Scope int_scope with Z.
    Open Scope int_scope.

    Print GRing.sqrrN.
    HB.about int.
    HB.about nat.
    HB.about eqType.
    HB.about GRing.Ring.    
    HB.about GRing.SemiRing.
    HB.about GRing.Zmodule.
    HB.about GRing.addNr.

    (* Definição de inverso multiplicativo como proposição booleana: *)
    (* Definition inv_mulz_b (m a : int) {n} : bool := a * m == 1 %[mod n].
    Compute (@inv_mulz_b 8 15 7).
    Compute (@inv_mulz_b 8 2 7). *)
    Definition inv_mulz (m a : int) {n} : bool := a * m == 1 %[mod n].
    Compute (@inv_mulz 8 15 7).
    Compute (@inv_mulz 8 2 7).

    (* Definição de inverso multiplicativo como proposição: *)
    (* Definition inv_mulz (m a : int) {n} : Prop := a * m = 1 %[mod n].
    Compute (@inv_mulz 8 15 7).
    Compute (@inv_mulz 8 2 7). *)

    (* Notação para inverso multiplicativo: *)
    Notation "a ^ -1 == m %[mod n ]" := (@inv_mulz m a n) (at level 30) : int_scope.

    Lemma aux1 (a b c n : int) :
        a * b = c  %[mod n] -> exists u v, (u * b + v * n = c)%R.
    Proof.
    move=> abH. exists a; exists ((c - a * b) %/ n) => /=.
    rewrite divzK; first by rewrite addrC subrK.
    by rewrite -eqz_mod_dvd; apply/eqP.
    Qed.

    Lemma dvdz_add (a b n : int) : (n %| a) -> (n %| b) -> (n %| (a + b)%R).
    Proof.
    move=> /dvdzP [q1 ->] /dvdzP [q2 ->].
    by rewrite -GRing.mulrDl dvdz_mull.
    Qed.

    Lemma dvdz_sub (a b n : int) : (n %| a) -> (n %| b) -> (n %| (a - b)%R).
    Proof.
    (* Eu creio que a seta "->" realiza substituição no goal: *)
    move=> /dvdzP [q1->] /dvdzP [q2->].
    rewrite -mulN1r mulrA [X in _ %| (_ + X)%R]mulrC.
    by rewrite mulN1r mulrC -GRing.mulrDl dvdz_mull.
    Qed.

    Lemma aux2 (a b c : int) :
        (exists (x y : int), (x * a + y * b)%R = c%R) <-> (gcdz a b %| c).
    Proof.
    split => [[x [y <-]]|/dvdzP[v->]].
        apply: dvdz_add; first by apply/dvdz_mull/dvdz_gcdl.
        by apply/dvdz_mull/dvdz_gcdr.
    have [x y <- _]:= egcdzP a b.
    by exists (v * x)%R; exists (v * y)%R; rewrite mulrDr !mulrA.
    Qed.
    
    (* Lema 6 do TCC: *)
    Lemma cond_inv (a n : int) :
        (exists b : int, a ^ -1 == b %[mod n]) <-> ((gcdz a n)%R == 1%R).
    Proof.
    split => [[b /eqP /[1!mulrC]] /aux1 /aux2 /[!dvdz1] // |].
    rewrite /inv_mulz; case: (egcdzP a n) => /= u v  <- _ /eqP <-.
    by exists u; rewrite mulrC -modzDmr modzMl addr0.
    Qed.

    Lemma aux3 (a b : int): 
        a != 0 -> (`|a| < `|b|)%R  -> (b %| a) = false.
    Proof.
    move=> a_neq0.
    apply contraTF => /dvdzP [/= q Hq].
    rewrite Hq -leNgt Num.normrM.
    apply: Num.Theory.ler_peMl => //.
    apply: archimedean.Num.Theory.norm_intr_ge1 => //.
    case: (q =P 0) => // q_eq0.
    by rewrite Hq q_eq0 mul0r in a_neq0.
    Qed.

    Lemma absz_div_mul (a n : int):
        ((a %/ n)%Z * n)%R = ((a %/ `|n|)%Z * `|n|)%R.
    Proof.
    case: n => n.
        by [].
    rewrite NegzE divzN -mulrzz mulNrNz mulrzz.
    rewrite [X in _ = ((_ %/ X)%Z * X)%R]ltz0_abs; last by [].
    by rewrite -mulrN1z mulNrNz mulrzz mulr1.
    Qed. 

    Lemma absz_le_mul (a n : int):
        (((a %/ n)%Z * n)%R <= `|a|%R)%R.
    Proof.
    rewrite absz_div_mul.
    case: a => a.
    (* caso: a = |a| *)
        rewrite -[X in (_ <= X)%R]abszE absz_nat divz_nat.
        apply div.leq_trunc_div.
    (* caso: a = -|a| *)
    rewrite NegzE.
    rewrite [X in (_ <= X)%R]ltz0_abs; last by [].
    rewrite -mulrN1z -[X in (_ <= X)%R]mulrN1z.
    rewrite mulrN1z mulNrNz mulrzz mulr1.
    case Hn : `|n| => [|k]. 
        rewrite -[X in ((_ %/ X)%Z * X <= _)%R]abszE Hn //=.
    rewrite divNz_nat; last by rewrite Hn //=.
    rewrite mulrC -mulrzz mulrNz Hn -abszE Hn mulrzz. 
    case H : (k.+1 * (div.divn a k.+1).+1) => [|x].
        move: H => /eqP H. rewrite -eqz_nat //= in H.
    move: H => /eqP H. rewrite -eqz_nat //= in H.
    Qed.

    Lemma absz_mod (a n : int):
        (n != 0)%Z -> (a %% n)%Z = `|(a %% n)%Z|.
    Proof.
    rewrite /modz absz_div_mul.
    case: a => a.
    (* caso a seja um número positivo: *)
        rewrite abszE divz_nat subzn; 
            last by rewrite div.leq_trunc_div.
        by rewrite -abszE absz_nat. 
    (* caso a seja um negativo: *)
    rewrite NegzE => nD0.
    rewrite divNz_nat. 
    rewrite -[X in (_ + X)%R = _]mulrN1z.
    rewrite abszE.
    rewrite -[X in _ = `|(_ - X)|%R]mulrN1z.
    rewrite mulNrNz mulrzz mulr1.
    rewrite -[X in _ = `|_ + X|%R]mulrN1z.
    rewrite mulNrNz mulrzz mulr1 -mulrz_nat mulrzz mulr1 addrC -abszE distnEl.
        rewrite subzn. by rewrite -natz.
        rewrite mulnC div.ltn_ceil //=.
        by rewrite absz_gt0.
        rewrite mulnC div.ltn_ceil //=.
        by rewrite absz_gt0.
        by rewrite absz_gt0.
    Qed.

    Lemma mulz_mod (a b c n : int):
        (a == b %[mod n]) -> ((a * c)%R == (b * c)%R %[mod n]).
    Proof.
        rewrite !eqz_mod_dvd.
        move=> Hn. rewrite -!mulrzz -mulrzBl mulrzz.
        by apply dvdz_mulr.
    Qed.

    (*  
        Documentar o uso de "Set Printing Coercions." no TCC (no Capítulo
        sobre a implementação).
    *)
    
    (*  Lema 7 do TCC (Parte 01: o número k existe):  *)
    Lemma invz_modp (p a : int):
        (primez.primez p) -> (0 < a < p)%R -> 
            exists (k : int), (0 < k < p)%R && ((a * k)%R == 1 %[mod p]).
    Proof.
    case: p => // p.
    move=> pP Ha.
    have : (0 < `|a| < p)%R.
        move: Ha. move=> /andP [Ha aLp].
        apply gtz0_abs in Ha as Habs.
        rewrite -abszE Habs. apply/andP.
        by split.
    move=> Habs.
    move: (primez.primez_coprime pP Habs) => Hc.
    rewrite /coprimez -cond_inv in Hc.
    case: Hc => [b Hb].
    rewrite /inv_mulz -modzMmr in Hb.
    exists (b %% p). apply/andP. split; last by [].
    rewrite absz_mod; last by apply (primez.primez_neq0 pP).
    case Hn: `|(b %% p)%Z|%N => [|n].
        rewrite eqz_mod_dvd absz_mod in Hb; last by apply (primez.primez_neq0 pP).
        rewrite Hn mulr0 dvdzE //= subn0 in Hb.
        rewrite -(absz_nat p) -(absz_nat 1) -dvdzE in Hb.
        by move: (primez.Euclidz_dvd1 pP); rewrite Hb.
    rewrite (primez.primez_abs pP) -Hn -absz_mod;
    last by apply (primez.primez_neq0 pP).
    rewrite ltz_mod; last by apply (primez.primez_neq0 pP). 
    rewrite absz_mod; last by apply (primez.primez_neq0 pP). 
    by rewrite Hn.
    Qed.

    (*  Lema 7 do TCC (Parte 02: o número k é único):  *)
    Lemma invz_modp_uniq (a k1 k2 p : int):
        (primez.primez p) -> (0 < a < p)%R -> (0 < k1 < p)%R && ((a * k1)%R == 1 %[mod p])
        -> (0 < k2 < p)%R && ((a * k2)%R == 1 %[mod p]) -> k1 == k2.
    Proof.
    rewrite !eqz_mod_dvd => pP Ha.
    case: k1 => // k1.
    case: k2 => // k2.
    move=> /andP [k1L Hk1] /andP [k2L Hk2].
    move: (dvdz_sub Hk1 Hk2). rewrite -addrA. 
    rewrite [X in p %| (_ + X)%R -> _]addrC. 
    rewrite -mulrN1z mulrzBl intz. 
    rewrite -[X in _ %| (_ + (_ + X + _))%R -> _]mulrN1z.
    rewrite mulNrNz intz mulrN1z -addrA subrr addr0 -mulrN1z mulrzz -mulrA mulrC.
    rewrite [X in _ %| (_ + X)%R -> _]mulrC. 
    rewrite -GRing.mulrDl -mulrzz mulrN1z mulrC (primez.Euclidz_dvdM _ _ pP).
    move: (primez.primez_Ndvd pP Ha) => pDa Hor.
    rewrite (negbTE pDa) //= -eqz_mod_dvd in Hor.
    rewrite !modz_small in Hor. move=>//.
        apply /andP. split.
            by [].
            by move: k2L => /andP [_ pLk2].
        apply /andP. split.
            by [].
            by move: k1L => /andP [_ pLk1].
    Qed.
    
    (* Lema 8 do TCC: *)
    Lemma invz_modp_mul (a p : int):
        (primez.primez p) -> (0 < a < p)%R -> ~ (exists x, x^2 == a %[mod p]) -> (forall h, (0 < h < p)%R -> exists k, (0 < k < p)%R && ((h != k) && ((h * k)%R == a %[mod p]))).
    Proof.
    move=> pP aL Hx h hL. move: (invz_modp pP hL) => [k Hh].
    move: Hh => /andP [kL Hk].
    have Hka : k * a == k * a %[mod p].
        by [].
    move: (mulz_mod h Hka) => {}Hka.
    rewrite mulrC mulrA in Hka.
    move: Hk => /eqP Hk. rewrite -{1}modzMml in Hka.
    rewrite {1}Hk in Hka. rewrite (primez.primez_1modp pP) mul1r in Hka.
    rewrite -mulrA -modzMmr in Hka.
    exists ((k * a) %% p). apply/andP. split.
        apply/andP. split.
        rewrite absz_mod.
        case Hn : `|((k * a) %% p)| => [|n].
            exfalso. apply Hx. exists 0.
            move: Hn. move=> /eqP Hn. rewrite absz_eq0 in Hn.
            move: Hn => /eqP Hn.
            rewrite Hn mulr0 in Hka.
            move: Hka => /eqP[<-] //=.
        by [].
        by rewrite (primez.primez_neq0 pP).
        rewrite (primez.primez_abs pP).
        apply ltz_pmod. 
        rewrite -(primez.primez_abs pP).
        apply (primez.primez_gt0 pP).
    apply/andP. split.
        apply/eqP. move=> H.
        rewrite -H in Hka.
        apply Hx. exists h. rewrite exprSz expr1z.
        apply/eqP. symmetry. by apply/eqP.
        apply/eqP. symmetry. by apply/eqP.
    Qed.

    (* Lema 9 do TCC: *)
    Lemma invz_modp_mul_uniq (a h k1 k2 p : int):
        primez.primez p ->
        (0 < a < p)%R -> (0 < h < p)%R -> (0 < k1 < p)%R -> (0 < k2 < p)%R
        -> (k1 * h)%R == a %[mod p] -> (k2 * h)%R == a %[mod p] -> k1 == k2.
    Proof.
    case: p => // p. case: a => // a. case: h => // h. case: k1 => // k1.
    case: k2 => // k2.
    move=> pP aL hL k1L k2L /eqP Hk1 /eqP Hk2. apply /eqP.
    rewrite -Hk2 in Hk1. move: Hk1 => /eqP. rewrite eqz_mod_dvd.
    rewrite [X in _ %| (X - _)%R-> _]mulrC.
    rewrite [X in _ %| (_ - X)%R-> _]mulrC.
    rewrite -!mulrzz -mulrNz !mulrzz -mulrDr. rewrite (primez.Euclidz_dvdM  _ _ pP).
    move: hL => /andP [hL0 pLh].
        rewrite dvdzE div.gtnNdvd //=.
        rewrite -eqz_mod_dvd !modz_small.
        by move=> /eqP.
    apply /andP. split.
        move: k2L => /andP [H _]. rewrite Num.Theory.le0r H orbC //=.
        move: k2L => /andP [_ H]. by rewrite H.
    apply /andP. split.
        move: k1L => /andP [H _]. rewrite Num.Theory.le0r H orbC //=.
        move: k1L => /andP [_ H]. by rewrite H.
    Qed.

    Lemma primez_prod_sqr (p a : int):
        (primez.primez p) -> (coprimez a p) -> 
        ((`|p| - 1)`!)%:Z ^ 2 == a ^ (p - 1) %[mod p].
    Proof.
    case: p => // p.
    move=> pP aCp.
    rewrite absz_nat (primez.fermatz_little_pred pP); last by apply /negP;
    rewrite dvdzE -prime_coprime; last by [];
    rewrite coprime_sym -coprimezE //=.
    have : (Posz (p - 1)`!) == - 1 %[mod p].
        rewrite eqz_mod_dvd -mulrN1z mulNrNz intz.
        rewrite -PoszD dvdzE //= addn1 subn1 -Wilson //=.
    move: pP; rewrite /primez.primez //=; apply prime_gt1.
    move=> /eqP fatE. 
    rewrite -!exprnP addn1 expr2 -modzMml -modzMmr fatE modzMml modzMmr //=.
    Qed.

    Close Scope int_scope.

    (*  O lema a seguir foi obtido em:
        https://github.com/thery/mathcomp-extra/blob/master/euler.v *)
    Lemma modn_prodm I r (P : pred I) F d :
        \prod_(i <- r | P i) (F i %% d) = \prod_(i <- r | P i) F i %[mod d].
    Proof.
    apply/eqP; elim/big_rec2: _ => // i m n _ /eqP nEm.
    by rewrite modnMml -modnMmr nEm modnMmr.
    Qed.

    (*  A definição a seguir foi obtid em:
        https://github.com/thery/mathcomp-extra/blob/master/euler.v *)
    Definition res_quad p a := has (fun i => i * i == a %[mod p]) (iota 0 p).


    (*  O lema a seguir foi obtido em:
        https://github.com/thery/mathcomp-extra/blob/master/euler.v *)
    Lemma res_quadP a p : 
    reflect (exists i : 'I_p, i * i = a %[mod p]) (res_quad p a).
    Proof. 
    apply: (iffP hasP) => [[x /[!mem_iota] [/andP[_ xLp] /eqP xxE]]|[x xxE]].
    by exists (Ordinal xLp).
    by exists (val x); [rewrite mem_iota /= | apply/eqP].
    Qed.

    (*  O lema a seguir foi obtido em:
        https://github.com/thery/mathcomp-extra/blob/master/euler.v *)
    Lemma res_quadPn a p : 
    reflect (forall i : 'I_p, i * i != a %[mod p]) (~~ (res_quad p a)).
    Proof.
    apply: (iffP hasPn) => [xxE i| xxE i /[!mem_iota] /= iI].
    by apply: xxE; rewrite mem_iota /=.
    by apply: (xxE (Ordinal iI)).
    Qed.

    (*  O lema a seguir foi obtido em:
        https://github.com/thery/mathcomp-extra/blob/master/euler.v *)
    Lemma fact_sqr_exp a p :
        prime p -> ~~ (p %| a) -> ~~ res_quad p a ->  (p.-1`!) = a ^ p.-1./2 %[mod p].
    Proof.
    move=> pP pNDa aR.
    have -> : p.-1`! = \prod_(i in 'F_p | i != 0%R) i.
    apply: etrans (_ : \prod_(i in 'F_p | i != 0 :> nat) i = _); last first.
        by apply: eq_bigl => i.
    rewrite /= Fp_cast //.
    rewrite fact_prod big_add1 /= big_mkord.
    case: p {pNDa aR}pP => //= p pP.
    by rewrite [RHS]big_mkcond /= big_ord_recl /= mul1n.
    pose a' : 'F_p := inZp a.
    have a'E : a' = a %% p :> nat by rewrite /= Fp_cast.
    have a'_neq0 : a' != 0%R.
    apply/eqP/val_eqP; rewrite [val a']a'E /=.
    by have /negPf := pNDa; rewrite /dvdn => ->.
    rewrite -modnXm -a'E.
    pose f (i : 'F_p) : 'F_p := (a' / i)%R.
    have f_eq0 : f 0%R = 0%R by rewrite /f GRing.invr0 GRing.mulr0.
    have fM (i : 'F_p) : i != ord0 -> (f i * i = a')%R.
    by move=> i_neq0; rewrite /f GRing.divfK.
    have fI (i : 'F_p) : f (f i) = i.
    by rewrite /f GRing.invf_div GRing.mulrC GRing.divfK.
    have fI_neq0 (i : 'F_p) : i != 0%R -> f i != i.
    move=> i_neq0; apply/eqP => fiE.
    have iL : i < p by rewrite -[X in _ < X]Fp_cast.
    have /res_quadPn/(_ (Ordinal iL)) /= := aR.
    have /val_eqP := fM _ i_neq0; rewrite fiE /=.
    rewrite ![X in _ %% X]Fp_cast //= => /eqP->.
    by rewrite Fp_cast // eqxx.
    have fB : {on [pred i |  i != ord0],  bijective f}.
    by exists f => j _; apply: fI.
    pose can (i : 'F_p) :=  if i < (f i) then i else f i.
    have -> : \prod_(i in 'F_p | i != 0%R) i =
    \prod_(j in 'F_p | (j < f j))
        \prod_(i in 'F_p | (i != 0%R) && (can i == j)) i.
    apply: partition_big => i /andP[iF i_neq0].
    rewrite andTb /can; case: (leqP (S i) _) => //.
    rewrite fI ltnS leq_eqVlt.
    by have /eqP/val_eqP/negPf/=-> := fI_neq0 _ i_neq0.
    apply: etrans (_ : \prod_(j in 'F_p | j < f j) (j * f j) = _ %[mod p]).
    congr (_ %% _); apply: eq_bigr => j /andP[jF jLfj].
    rewrite (bigD1 j); last first.
        rewrite jF /can jLfj eqxx andTb andbT.
        by apply/eqP=> j_eq0; rewrite j_eq0 f_eq0 ltnn in jLfj.
    rewrite (bigD1 (f j)); last first.
        rewrite inE /can ifN.
        rewrite fI eqxx.
        case: eqP => [fj_eq0|].
            by rewrite fj_eq0 -[j]fI fj_eq0 f_eq0 ltnn in jLfj.
        by case: eqP => [fj_eqj|//]; rewrite fj_eqj ltnn in jLfj.
        by rewrite fI -leqNgt ltnW.
    rewrite big1 /= ?muln1 // => i.
    rewrite /can; case: leqP; last by case: (i =P j); rewrite andbF.
    case: (f i =P j); rewrite ?andbF // => <-.
    by rewrite fI eqxx andbF.
    apply: etrans (_ : \prod_(j in 'F_p | j < f j) a' = _ %[mod p]).
    rewrite -modn_prodm; congr (_ %% _); apply: eq_bigr => i /andP[_ iLfi].
    have i_neq0 : i != 0%R.
        by apply/eqP=> i_eq0; rewrite i_eq0 f_eq0 ltnn in iLfi.
    rewrite -(fM i i_neq0) mulnC.
    by congr (_ %% _); rewrite Fp_cast.
    congr (_ %% _).
    rewrite prod_nat_const.
    congr (_ ^  _).
    rewrite -[p in RHS](card_Fp pP).
    rewrite [in RHS](cardD1 0%R) inE add1n -pred_Sn.
    set A := [predD1 'F_p & 0%R].
    pose B := [pred i |  (i : 'F_p) < f i].
    rewrite -(cardID B A).
    have <- : #|image f [predI A & B]| = #|[predD A & B]|.
    apply: eq_card => i; rewrite !inE.
    rewrite -[in LHS](fI i) mem_map; last first.
        by move=> i1 j1 fiEfj; rewrite -[i1]fI fiEfj fI.
    have -> : (f i  \in enum [predI A & B])  = ([predI A & B] (f i)).
        have F (U : finType) (p1 : pred U) (x : U) : x \in enum p1 = p1 x.
        by rewrite mem_enum .
        by rewrite F.
    rewrite [LHS]/= !inE fI.
    case: (i =P 0%R) => [->|]; first by rewrite f_eq0.
    case: (f i =P 0%R) => [fi0|/eqP fi_neq0 /eqP i_neq0].
        by case; rewrite -(fI i) fi0 f_eq0.
    case: ltngtP => // /eqP/val_eqP fiEi.
    by have := fI_neq0 i i_neq0; rewrite fiEi eqxx.
    rewrite card_image; last by move=> i j fiEfj; rewrite -[i]fI fiEfj fI.
    rewrite addnn (half_bit_double _ false).
    apply: eq_card => i; rewrite !inE.
    by case: eqP => // ->; rewrite f_eq0 ltnn.
    Qed.

    Lemma euler_criterion a p : 
        prime p -> ~~ (p %| a) -> 
        a ^ p.-1./2 = (if res_quad p a then 1 else p.-1) %[mod p].
    Proof.
    move=> pP pNDa.
    have p_gt0 : 0 < p by apply: prime_gt0.
    have [/res_quadP[i Hi]|Hrn] := boolP (res_quad p a); last first.
    rewrite -fact_sqr_exp //.
    apply/eqP; rewrite -(eqn_modDr 1) !addn1 prednK //.
    have /dvdnP[k->] : (p %| (p.-1)`!.+1) by rewrite -Wilson // prime_gt1.
    by rewrite modnn modnMl.
    rewrite -modnXm -Hi modnXm mulnn -expnM mul2n.
    have [pO|/(prime_oddPn pP) pE2]:= boolP (odd p); last first.
    by rewrite [in X in _ ^ X]pE2 /= expn0.
    have i_gt0 : 0 < i.
    case: i Hi pNDa => [] [] //= _.
    by rewrite /dvdn => <- /[!mod0n].
    rewrite even_halfK; last by case: (p) pP pO.
    apply/eqP; rewrite eqn_mod_dvd //; last by rewrite expn_gt0 i_gt0.
    rewrite -(Gauss_dvdr _ (_ : coprime _ i)); last first.
    rewrite prime_coprime //; apply/negP => /dvdnP [k iE].
    rewrite iE mulnA modnMl in Hi.
    by case/negP: pNDa; rewrite /dvdn -Hi.
    rewrite mulnBr muln1 -expnS prednK //.
    rewrite -eqn_mod_dvd //; first by apply/eqP/fermat_little.
    by apply: leq_pexp2l (_ : 1 <= p).
    Qed.

    Delimit Scope int_scope with Z.
    Open Scope int_scope.

    (* Lema 10 do TCC: *)
    Lemma primez_fat_exp_modp (a p : int):
        (primez.primez p) -> ~(p %| a) -> ~ (exists x, x^2 == a %[mod p]) ->
        ((`|p| - 1)`!)%:Z == (a ^ ((p - 1) %/ 2 )%Z) %[mod p].
    Proof.
    case: p => // p.
    rewrite absz_nat => pP aCp nEx.
    have pN0: (p != 0 :> int)%R.
        apply/eqP => H; rewrite H //= in pP.
    Set Printing Coercions.
    rewrite subzn; 
    last by rewrite lt0n; apply/eqP => H; rewrite H //= in pP.
    apply/eqP.
    rewrite divz_nat -exprnP addn1 //= !modz_nat -modzXm (absz_mod a pN0).
    rewrite -rmorphXn //= !modz_nat natrXE; f_equal.
    pose b := (`|(a %% Posz p)%Z|). rewrite -/b.
    rewrite subn1 divn2.
    apply fact_sqr_exp.
        move: pP => /andP [_ pP] //=.
        rewrite -(subn0 b) -eqn_mod_dvd; last by [].
        apply/eqP => bN0.
        apply aCp.
        rewrite -(subr0 a) -eqz_mod_dvd -(modz_mod a) (absz_mod a).
        rewrite -/b !modz_nat bN0 //=.
    apply/eqP => pE0; rewrite pE0 //= in pP.
    apply/res_quadPn => [i].
    case: i => i Hi //=.
    apply/eqP => Hi2.
    apply nEx. exists (Posz i).
    rewrite -(modz_mod a) (absz_mod a pN0) -/b.
    rewrite -/b -exprnP -rmorphXn //= addn1 natrXE -mulnn.
    rewrite !modz_nat Hi2 //=.
    Qed.

    Close Scope int_scope.
    
End inversezmodp.

Module Legendre.

    Definition legendre_symb {p : int} (pL2 : (2 < p)%R) (pP : primez.primez p) (a : int) :=
        if (p %| a)%Z then 0%Z
        else if [exists i : 'I_`|p|, ((i * i)%:Z  == a %[mod p])%Z]
        then 1%Z
        else (-1)%Z.
    
    Theorem eulerz_criterion {p : int} (pL2 : (2 < p)%R) (pP : primez.primez p) (a : int) :
        (a ^ ((p - 1) %/ 2)%Z = (legendre_symb pL2 pP a) %[mod p])%Z.
    Proof.
    move: pL2 pP.
        case: p => // p pL2 pP.
        rewrite /legendre_symb.
        rewrite subzn; last by rewrite prime_gt0.
        rewrite divz_nat -modzXm addn1.
        case pDa : (p %| a)%Z.
        move: pDa => /dvdz_mod0P ->.
        rewrite -rmorphXn //= natrXE exp0n //=.
            rewrite subn1 divn2 half_gt0 ltn_predRL -ltz_nat //=.
        rewrite (missing.absz_mod a); last by apply/eqP; move=> p0; rewrite p0 //= in pP.
        case Ex : ([exists i,  (((nat_of_ord i * nat_of_ord i)%:Z %% p) == `|a %% p|%:Z)])%Z.
        move: Ex => /existsP.
        rewrite absz_nat => Ex.
        case: Ex => x.
        pose m := `|(a %% p)%Z|%N. rewrite (missing.absz_mod a) -/m.
        rewrite absz_nat modz_nat. case: x => k kLp //=.
        move=> /eqP Hk. rewrite -Hk.
        rewrite -modz_nat modzXm mulnn -natrXE rmorphXn //= -rmorphXn //=.
        rewrite mulnn natrXE -expnM mul2n divn2 subn1 even_halfK.
        rewrite rmorphXn //= exprnP.
        rewrite -subn1 -subzn. rewrite (primez.fermatz_little_pred pP).
        rewrite //=.
        rewrite -(subr0 (Posz k)) -eqz_mod_dvd modz_nat mod0z.
        move=> /eqP pDk.
        move: Hk. injection pDk => {}pDk.
        rewrite -modnMml pDk mul0n mod0n => m0.
        have: (Posz p %| a)%Z.
            rewrite -(subr0 a) -eqz_mod_dvd mod0z missing.absz_mod -/m.
            rewrite -m0 //=.
        apply/eqP => p0. rewrite p0 //= in pP.
        move=> pDDa. rewrite pDDa //= in pDa.
        rewrite prime_gt0 //=.
        rewrite -oddS prednK; last by rewrite prime_gt0 //=.
        move: pL2.
        case: (@even_prime p) => //= -> //=.
        apply/eqP => p0. rewrite p0 //= in pP.
        move: Ex.
        rewrite -{1}missing.absz_mod.
        rewrite -{1}modz_mod {1}(missing.absz_mod a).
        pose m := `|(a %% p)%Z|%N.
        rewrite -/m => xE.
        rewrite -rmorphXn //= -(modz_mod (-1)) modNz_nat.
        rewrite mod0n subr0 subzn.
        rewrite !modz_nat. f_equal.
        have resq: (inversezmodp.res_quad p m) = false.
            apply/eqP. rewrite eqbF_neg.
            apply/negP. rewrite /inversezmodp.res_quad.
            move=> resq. move: resq => /inversezmodp.res_quadP [i Hi]. rewrite -Bool.negb_true_iff in xE.
            move: xE => /negP xE.
            apply xE. apply /existsP.
            exists i.
            rewrite modz_nat Hi -modz_nat eqxx //=.
        have pDm : ~~ (p %| m)%N.
            rewrite -(absz_nat p) -(absz_nat m) -dvdzE.
            rewrite -(subr0 (Posz m)) -eqz_mod_dvd /m -missing.absz_mod.
            rewrite modz_mod.
            apply/negP. rewrite /not eqz_mod_dvd subr0 pDa //=.
        apply/eqP => p0. rewrite p0 //= in pP.
        rewrite natrXE.
        have {}pP : prime p.
            rewrite //=.
        move: (inversezmodp.euler_criterion pP pDm).
        rewrite resq subn1 divn2 //=.
        rewrite prime_gt0 //. 
        rewrite prime_gt0 //. 
        apply/eqP => p0. rewrite p0 //= in pP.
        apply/eqP => p0. rewrite p0 //= in pP.
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
    rewrite /legendre_symb. rewrite amodb.
    have -> : (p %| a)%Z = (p %| b)%Z.
        rewrite -(subr0 a) -(subr0 b) -!eqz_mod_dvd amodb //=.
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
    have: [exists i : 'I_p,  (Posz (nat_of_ord i * nat_of_ord i)  == a * a  %[mod p])]%Z.
        apply/existsP.
        have H: (`|a %% Posz p|%Z < p)%N.
            rewrite -ltz_nat -missing.absz_mod.
            rewrite ltz_pmod //=.
            rewrite ltz_nat prime_gt0 //.
            apply /eqP => p0. rewrite p0 //= in pL2.
        pose x := Ordinal H.
        exists x.
        rewrite /x //= PoszM -missing.absz_mod. 
        rewrite modzMml modzMmr eqxx //.
        apply/eqP => p0. rewrite p0 //= in pL2.
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
    rewrite divz_nat addn1 (intEsg (-1)) //= mulr1 subn1 divn2 /exprz sgz_odd; last by [].
    case podd: (odd p.-1./2).
        rewrite //= expr1. move=> /eqP.
        rewrite eqz_mod_dvd /sgz //=.
        have -> : ((-1) - 1%Z)%R = (-2)%Z by [].
        rewrite dvdzE //=.
        rewrite -(subn0 2) -eqn_mod_dvd //=.
        rewrite modn_small //= mod0n //=.
        rewrite //= expr0.
    move=> _. rewrite eqz_mod_dvd subzn; last by rewrite prime_gt0. rewrite dvdzE //= !add1n. apply/dvdnP.
    exists (p.-1./2./2).
    have -> : 4 = (2 * 2) by [].
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
        have -> : 4 = 2 * 2 by [].
        rewrite mulnA !muln2.
        move: (half_bit_double k.*2 false).
        rewrite //= add0n => ->.
        rewrite -{1}(@ltr0_sgz _ (-1)%Z); last by [].
        rewrite /exprz sgz_odd; last by [].
        rewrite odd_double //= expr0.
    rewrite /legendre_symb dvdzE //= Euclid_dvd1; last by [].
    case: ([exists i,  (nat_of_ord i * nat_of_ord i)%N  == -1  %[mod p]])%Z.
        rewrite //=.
    move=> /eqP. rewrite eqz_mod_dvd.
    have -> : (1 - (-1)%Z)%R = 2 by [].
    rewrite dvdzE //= -(subn0 2) -eqn_mod_dvd //=.
    rewrite modn_small //= mod0n //=.
    Qed.

    Lemma legendre_symb_or (p a : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
        ((legendre_symb pL2 pP a) == 1)%Z || ((legendre_symb pL2 pP a) == -1)%Z || ((legendre_symb pL2 pP a) == 0)%Z.
    Proof.
    rewrite /legendre_symb.
    case pDa : (p %| a)%Z => //=.
    case: [exists i,  ((nat_of_ord i * nat_of_ord i)%N  == a  %[mod p])%Z] => //=.
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

    Lemma res_quad_eq_leg (p a : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
        legendre_symb pL2 pP a = (if (p %| a)%Z then 0%Z else if 
        inversezmodp.res_quad `|p| (`|a %% p|%Z) then 1%Z else (-1)%Z).
    Proof.
    move: pL2 pP.
    case: p => // p pL2 pP.
    rewrite absz_nat /legendre_symb /inversezmodp.res_quad.
    case pDa : (p %| a)%Z => //.
    case Hi: (has (fun i : nat => i * i  == `|(a %% p)%Z|  %[mod p]) (iota 0 p))%N.
    Search (has) (reflect). 
    move: Hi => /hasP [x Hi].
    rewrite mem_iota add0n in Hi => Hx.
    have -> : [exists i : 'I_p,  ((nat_of_ord i * nat_of_ord i)%N  == a  %[mod p])%Z].
        rewrite -(modz_mod a) (missing.absz_mod a).
        move: Hi => /andP [_ Hi].
        apply/existsP.
        exists (Ordinal Hi).
        rewrite //= !modz_nat. apply/eqP. f_equal.
        apply/eqP. apply Hx.
    apply/eqP. move=> p0. rewrite p0 // in pL2.
    by [].
    have: ~~ [exists i : 'I_p,  ((nat_of_ord i * nat_of_ord i)%N  == a  %[mod p])%Z].
        rewrite -(modz_mod a) (missing.absz_mod a).
        apply/negP => /existsP [x H].
        rewrite !modz_nat in H.
        move: Hi => /eqP Hi.
        rewrite eqbF_neg in Hi.
        move: Hi => /negP Hi.
        apply Hi.
        apply/hasP.
        move: H. case: x => x Hx //= /eqP xE.
        injection xE => /eqP {}xE.
        exists x.
        rewrite mem_iota add0n Hx //.
        apply xE.
    apply/eqP. move=> p0. rewrite p0 // in pL2.
    rewrite -eqbF_neg => /eqP -> //.
    Qed.

    Lemma legendre_symb_mul (p a b : int) (pL2 : (2 < p)%R) (pP : primez.primez p):
        (legendre_symb pL2 pP (a * b)%R) = ((legendre_symb pL2 pP a) * (legendre_symb pL2 pP b))%R.
    Proof.
    move: pL2 pP.
    case: p => // p pL2 pP.
    have pDp2 : (p %| p.-2) = false.
        rewrite -subn2 dvdn_subr.
        rewrite gtnNdvd //. by rewrite prime_gt1. 
        by rewrite dvdnn.
    rewrite !res_quad_eq_leg primez.Euclidz_dvdM; last by [].
    case pDa: (p %| a)%Z => //=.
        by rewrite mul0r.
    case pDb: (p %| b)%Z => //=.
        by rewrite mulr0.
    rewrite -modzMml -modzMmr.
    pose m := `|(a %% p)%Z|.
    pose n := `|(b %% p)%Z|.
    rewrite (missing.absz_mod a).
    rewrite (missing.absz_mod b).
    rewrite -/m -/n -PoszM modz_nat !absz_nat /inversezmodp.res_quad modn_mod.
    have pDm : ~~ (p %| m).
        rewrite /m -{1}(absz_nat p) -dvdzE.
        apply/negP. rewrite -(subr0 (a %% p)%Z) -eqz_mod_dvd.
        rewrite modz_mod eqz_mod_dvd subr0 pDa //=. 
    have pDn : ~~ (p %| n).
        rewrite /m -{1}(absz_nat p) -dvdzE.
        apply/negP. rewrite -(subr0 (b %% p)%Z) -eqz_mod_dvd.
        rewrite modz_mod eqz_mod_dvd subr0 pDb //=.
    have pDmn: ~~ (p %| m * n).
        rewrite Euclid_dvdM; last by [].
        rewrite -eqbF_neg in pDm.
        rewrite -eqbF_neg in pDn.
        move: pDm pDn => /eqP -> /eqP -> //=.
    clear pDa pDb.
    move: pP => /andP [_ //= pP].
    rewrite ltz_nat addn1 in pL2.
    move: (inversezmodp.euler_criterion pP pDm) => Em.
    move: (inversezmodp.euler_criterion pP pDn) => En.
    move: (inversezmodp.euler_criterion pP pDmn) => Emn.
    case Hm: (has (fun i : nat => i * i  == m  %[mod p]) (iota 0 p)).
    case Hn: (has (fun i : nat => i * i  == n  %[mod p]) (iota 0 p)).
    move: Hm Hn => /hasP [x] xLp /eqP Hx /hasP [y] yLp /eqP Hy.
    move: xLp yLp. rewrite !mem_iota add0n => xLp yLp.
    have -> : (has (fun i : nat => i * i  == m * n  %[mod p]) (iota 0 p)).
        apply/hasP. exists ((x * y) %% p).
        rewrite mem_iota add0n ltn_pmod //.
        rewrite prime_gt0 //.
    rewrite modnMml modnMmr -mulnA (mulnC y) -mulnA mulnA -modnMml -modnMmr Hx Hy modnMml modnMmr eqxx //.
    rewrite //=.
    rewrite mul1r.
    have -> : (has (fun i : nat => i * i  == m * n  %[mod p]) (iota 0 p)) = false.
        rewrite /inversezmodp.res_quad Hm in Em.
        rewrite /inversezmodp.res_quad Hn in En.
        rewrite -(muln1 (n ^ p.-1./2)) -modnMmr -Em modnMmr -expnMn mulnC in En.
        rewrite /inversezmodp.res_quad En in Emn.
        apply/eqP. rewrite eqbF_neg. apply/negP => Hmn.
        rewrite Hmn in Emn. move: Emn => /eqP.
        rewrite eqn_mod_dvd. rewrite subn1 pDp2 //.
        rewrite ltn_predRL prime_gt1 //. rewrite //.
    case Hn: (has (fun i : nat => i * i  == n  %[mod p]) (iota 0 p)).
        rewrite mulr1.
        rewrite /inversezmodp.res_quad Hm in Em.
        rewrite /inversezmodp.res_quad Hn in En.
        rewrite -(muln1 (m ^ _) ) -modnMmr -En modnMmr in Em.
        rewrite -expnMn in Em.
        rewrite Em /inversezmodp.res_quad in Emn.
        move: Emn => /eqP.
        case Hmn: (has (fun i : nat => i * i  == m * n  %[mod p]) (iota 0 p)).
        rewrite eqn_mod_dvd.
        rewrite subn1 pDp2 //=.
        rewrite ltn_predRL prime_gt1 //.
    rewrite //=.
    have -> : ((-1)%Z * (-1)%Z)%R = 1%Z by [].
    rewrite expnMn in Emn.
    rewrite /inversezmodp.res_quad Hm in Em.    
    rewrite /inversezmodp.res_quad Hn in En.
    rewrite -modnMml -modnMmr Em En modnMml modnMmr in Emn.
    case Hmn: (has (fun i : nat => i * i  == m * n  %[mod p]) (iota 0 p)) => //.
    move: Emn => /eqP.
    rewrite /inversezmodp.res_quad Hmn eqn_mod_dvd -{3}(muln1 p.-1).
    rewrite -mulnBr subn1 (Euclid_dvdM _ _ pP) pDp2 orbC /=.
    rewrite -subn1 dvdn_subr.
    rewrite Euclid_dvd1 //=.
    rewrite prime_gt0 //=.
    rewrite dvdnn //=.
    rewrite muln1 mulnn -{1}(expn1 p.-1) leq_pexp2l //=.
    rewrite -ltnS prednK.
    rewrite prime_gt1 //.
    rewrite prime_gt0 //.
    apply/eqP => p0. rewrite p0 // in pL2.
    apply/eqP => p0. rewrite p0 // in pL2.
    Qed.

End Legendre.