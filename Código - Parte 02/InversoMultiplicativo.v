From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssreflect eqtype all_algebra
ssrbool bigop ssrnat ssrint ssralg intdiv seq prime order.
Import Order.Theory.
From Coq Require Import Logic.Decidable.

Import GRing.Theory.

Set Implicit Arguments.     
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*  Algumas provas neste arquivo foram obtidas de https://github.com/thery/mathcomp-extra/ *)

(*  Módulo específico para primos inteiros: *)
Module primesz.
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
    have a_pos' :  (0 < `|a|) %nat.
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

    Lemma primez_lt0 (p : int):
        (primez p) -> (0 < p)%R.
    Proof.
    rewrite /primez => /andP [p0 pP].
    rewrite Num.Internals.le0r in p0.
    move: p0 => /orP [p0 | pL0].
        move: p0 => /eqP p0.
        rewrite p0 //= in pP.
    move=> //=.
    Qed.
        
    Lemma primez_lt1 (p : int):
        (primez p) -> (1 < p)%R.
    Proof.
    move=> pP. move: (primez_abs pP) => Hp.
    rewrite Hp. move: (primez_lt0 pP) => pL0.
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
    move=> pP. move: (primez_lt1 pP) => pL1.
    apply primez_abs in pP. rewrite pP. rewrite pP in pL1.
    rewrite lez_nat. rewrite ltz_nat in pL1.
    rewrite ltn_neqAle. by rewrite ltn_neqAle in pL1.
    Qed.

    Lemma primez_ndiv1 (p : int):
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
    move=> pP. move: (primez_lt1 pP) (primez_abs pP) => pL1 pabs.
    rewrite pabs modz_small. by [].
    apply /andP. split.
        by [].
        by rewrite -pabs.
    Qed.

    (*  A prova do seguinte lema se baseou na prova do lema "prime_modn_expSn" 
        disponível em: https://github.com/thery/mathcomp-extra/blob/640bc1a2634a609b8fd8a7c2023654ac3d9bc0a8/rsa.v  *)

    Lemma primez_modn_expSn (p n : int) : (0 <= n)%R -> primesz.primez p -> ((n + 1) ^ p)%R = ((n ^ p) + 1)%R %[mod p].
    Proof.
    case: n => // n nL0.
    case: p => // p pP.
    rewrite -[((_ ^ _) + 1)%R]addr0.
    (* Set Printing Coercions. *)
    rewrite -PoszD /exprz -!rmorphXn //= natrXE -PoszD !modz_nat addnC.
    apply f_equal.
    move: p pP => [// | p pP].
    rewrite (expnDn 1) big_ord_recr big_ord_recl /= subnn binn exp1n !mul1n
    addnAC -modnDmr natrXE.
    congr ((_ + _) %% _)%N; last by
    apply/eqP/dvdn_sum => -[i ?] _; exact/dvdn_mulr/prime_dvd_bin. 
    by rewrite addnC.
    Qed.

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

    (*  A prova do seguinte lema se baseou na prova do lema "fermat_little" 
        disponível em: https://github.com/thery/mathcomp-extra/blob/640bc1a2634a609b8fd8a7c2023654ac3d9bc0a8/rsa.v  *)
    
    Lemma fermatz_little a p : primez p -> a ^ p = a %[mod p].
    Proof.
    case: p => // p.
    move=> /andP[pL0 pP].
    clear pL0.
    rewrite absz_nat in pP.
    rewrite /exprz -modzXm -{2}(modz_mod a) (absz_mod a);
        last by apply/eqP; move=> p0; injection p0 => {}p0;
        rewrite p0 //= in pP.
    Set Printing Coercions.
    rewrite /exprz -rmorphXn //= natrXE !modz_nat. 
    apply f_equal.
    elim: (`|(a %% Posz p)%Z|) => [|x IH]; first by rewrite exp0n // prime_gt0.
    by rewrite prime_modn_expSn // -addn1 -modnDml IH modnDml addn1.
    Qed.

End primesz.

(*  Implementações relacionados a função fatorial *)

Module factorial.
    (* Delimit Scope int_scope with Z.
    Open Scope int_scope.

    Local Notation "+%Z" := intZmod.addz (at level 0, only parsing).
    Notation "\sum_ ( i <- r | P ) F" :=
    (\big[+%Z/0%Z]_(i <- r | P%B) F%Z) : int_scope.
    

    Lemma prod_factorial (n : int): 
        \prod_((1 <= i < n + 1)%R) i = n.
    Proof.

    Close Scope int_scope. *)

    Delimit Scope nat_scope with N.
    Open Scope nat_scope.
        
    Lemma aux4 (p h : nat): 
        (0 < h < p) -> ((p - 1)`!) = (\prod_(i <- (rem h (index_iota 1 p))) i) * h. 
    Proof.
        elim: p.
        {   
            move=> /andP [_ kL0]. by []. 
        }
        move=> n H /andP[hL0 hLn]. 
        rewrite -addn1 -addnBA; last by [].
        rewrite subnn addn0.
        move: hLn.
        rewrite ltnS leq_eqVlt => /orP[hEn | hLn]. 
        move: hEn => /eqP hEn.
        rewrite hEn.
        Search (rem _). 
    Admitted.

    Close Scope nat_scope.
End factorial.

(*  Implementação de Inverso Multiplicativo em Coq *)

Module inversez.
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

    Compute (iota 1 11).

    Check (forall (a : int), (1 <= a)%R).

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

    Compute ((- 3) %% (- 2))%Z.
    Compute ((- 3) %% (0))%Z.
    Compute (div.modn 14 7).

    Compute (modz (- 2) 8).
    Compute (((- 2) %/ 8)).

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
        (primesz.primez p) -> (0 < a < p)%R -> 
            exists (k : int), (0 < k < p)%R && ((a * k)%R == 1 %[mod p]).
    Proof.
        move=> pP Ha.
        have : (0 < `|a| < p)%R.
            move: Ha. move=> /andP [Ha aLp].
            apply gtz0_abs in Ha as Habs.
            rewrite -abszE Habs. apply/andP.
            by split.
        move=> Habs.
        move: (primesz.primez_coprime pP Habs) => Hc.
        rewrite /coprimez -cond_inv in Hc.
        case: Hc => [b Hb].
        rewrite /inv_mulz -modzMmr in Hb.
        exists (b %% p). apply/andP. split; last by [].
            rewrite absz_mod; last by apply (primesz.primez_neq0 pP).
            case Hn: `|(b %% p)%Z|%N => [|n].
                rewrite eqz_mod_dvd absz_mod in Hb; last by apply (primesz.primez_neq0 pP).
                rewrite Hn mulr0 dvdzE //= subn0 in Hb.
                have H1 : 1%N = `|1|.
                    by [].
                rewrite H1 -dvdzE in Hb.
                by move: (primesz.primez_ndiv1 pP); rewrite Hb.
                rewrite (primesz.primez_abs pP) -Hn -absz_mod;
                last by apply (primesz.primez_neq0 pP).
                rewrite ltz_mod; last by apply (primesz.primez_neq0 pP). 
                rewrite absz_mod; last by apply (primesz.primez_neq0 pP). 
                by rewrite Hn.
    Qed.

    (*  Lema 7 do TCC (Parte 02: o número k é único):  *)
    Lemma invz_modp_uniq (a k1 k2 p : int):
        (primesz.primez p) -> (0 < a < p)%R -> (0 < k1 < p)%R && ((a * k1)%R == 1 %[mod p])
        -> (0 < k2 < p)%R && ((a * k2)%R == 1 %[mod p]) -> k1 == k2.
    Proof.
        rewrite !eqz_mod_dvd => pP Ha /andP [k1L Hk1] /andP [k2L Hk2].
        move: (dvdz_sub Hk1 Hk2). rewrite -addrA. 
        rewrite [X in p %| (_ + X)%R -> _]addrC. 
        rewrite -mulrN1z mulrzBl. rewrite intz. 
        rewrite -[X in _ %| (_ + (_ + X + _))%R -> _]mulrN1z.
        rewrite mulNrNz intz mulrN1z -addrA subrr addr0.
        rewrite -mulrN1z mulrzz -mulrA mulrC.
        rewrite [X in _ %| (_ + X)%R -> _]mulrC. 
        rewrite -GRing.mulrDl -mulrzz mulrN1z mulrC.
        rewrite (primesz.Euclidz_dvdM _ _ pP).
        move: (primesz.primez_Ndvd pP Ha) => pDa Hor.
        rewrite (negbTE pDa) //= -eqz_mod_dvd in Hor.
        have: k1 = `|k1|.
            move: k1L => /andP [k1L0 pLk1]. symmetry.
            apply (gtz0_abs k1L0).
        have: k2 = `|k2|.
            move: k2L => /andP [k2L0 pLk2]. symmetry.
            apply (gtz0_abs k2L0).
        move=> k2abs k1abs.
        rewrite !modz_small in Hor. move=>//.
            apply /andP. split.
                by rewrite k2abs.
                by move: k2L => /andP [_ pLk2].
            apply /andP. split.
                by rewrite k1abs.
                by move: k1L => /andP [_ pLk1].
    Qed.
    
    (* Lema 8 do TCC: *)
    Lemma invz_modp_mul (a p : int):
        (primesz.primez p) -> (2 < p)%R -> (0 < a < p)%R -> ~ (exists x, x^2 == a %[mod p]) -> (forall h, (0 < h < p)%R -> exists k, (0 < k < p)%R && ((h != k) && ((h * k)%R == a %[mod p]))).
    Proof.
        move=> pP pL2 aL Hx h hL. move: (invz_modp pP hL) => [k Hh].
        move: Hh => /andP [kL Hk].
        have Hka : k * a == k * a %[mod p].
            by [].
        move: (mulz_mod h Hka) => {}Hka.
        rewrite mulrC mulrA in Hka.
        move: Hk => /eqP Hk. rewrite -{1}modzMml in Hka.
        rewrite {1}Hk in Hka. rewrite (primesz.primez_1modp pP) mul1r in Hka.
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
            by rewrite (primesz.primez_neq0 pP).
            rewrite (primesz.primez_abs pP).
            apply ltz_pmod. 
            rewrite -(primesz.primez_abs pP).
            apply (primesz.primez_lt0 pP).
        apply/andP. split.
            apply/eqP. move=> H.
            rewrite -H in Hka.
            apply Hx. exists h. rewrite exprSz expr1z.
            apply/eqP. symmetry. by apply/eqP.
            apply/eqP. symmetry. by apply/eqP.
    Qed.

    (* Lema 9 do TCC: *)
    Lemma invz_modp_mul_uniq (a h k1 k2 p : int):
        primesz.primez p ->
        (0 < a < p)%R -> (0 < h < p)%R -> (0 < k1 < p)%R -> (0 < k2 < p)%R
        -> (k1 * h)%R == a %[mod p] -> (k2 * h)%R == a %[mod p] -> k1 == k2.
    Proof.
        move=> pP aL hL k1L k2L /eqP Hk1 /eqP Hk2. apply /eqP.
        rewrite -Hk2 in Hk1. move: Hk1 => /eqP. rewrite eqz_mod_dvd.
        rewrite [X in _ %| (X - _)%R-> _]mulrC.
        rewrite [X in _ %| (_ - X)%R-> _]mulrC.
        rewrite -!mulrzz -mulrNz !mulrzz -mulrDr. rewrite (primesz.Euclidz_dvdM  _ _ pP).
        move: hL => /andP [hL0 pLh].
        have habs: h = `|h|.
            symmetry. by rewrite (gtz0_abs hL0).
            rewrite dvdzE div.gtnNdvd //=.
            rewrite -eqz_mod_dvd !modz_small.
            by move=> /eqP.
        apply /andP. split.
            move: k2L => /andP [H _]. rewrite Num.Theory.le0r H orbC //=.
            move: k2L => /andP [_ H]. by rewrite H.
        apply /andP. split.
            move: k1L => /andP [H _]. rewrite Num.Theory.le0r H orbC //=.
            move: k1L => /andP [_ H]. by rewrite H.
        rewrite habs in hL0. by [].
        rewrite habs (primesz.primez_abs pP) in pLh. by [].
    Qed.
    
    (* Definindo fatorial para inteiros: *)
    (* Definition factorialz (n : int) := (`|n|`!)%:Z.
    Notation "n `!" := (factorialz n) (at level 2, format "n `!") : int_scope. *)

    Compute (\prod_(i <- (rem 1 (rem 2 (index_iota 1 7)))) i)%N.
    Compute (index_iota 1 7).

    Check (forall (a b : int), (a * b)%R = 0).
    

    Lemma primez_pred_exp_half (a p : int):
        (2 < p)%R -> ()


    Lemma prod_rem2 (a : int) (n : nat):
        (0 < a < n.+1)%R ->
        (\prod_(i <- (index_iota 1 n.+1)) i)%:Z == 
        ((\prod_(i <- (rem `|a|%N (index_iota 1 n.+1))) i)%:Z * a)%R.
    Proof.
        move=> /andP [aL0 aLn]. move: (gtz0_abs aL0) => aEabs.
        remember (index_iota 1 n.+1) as l.
        move: Heql. elim: l => [|h t IH].
            {
                rewrite //=.
            }
            

    (* Lemma primez_fat_even_exp_modp (a p : int):
        (primesz.primez p) -> (2 < p)%R -> (0 < a < p)%R -> ~ (exists x, x^2 == a %[mod p]) -> (forall h, (0 < h < p)%R -> 
        exists k, ((h != k) && (\prod_(i <- (index_iota 1)) (h * k)%R == a %[mod p]))). *)

    (* Lemma primez_fat_even_exp_modp (a p : int) n (l : seq nat):
        (n = size l) -> (~~ odd n) 
        -> (forall i, i \in l -> exists j, (j \in l) && ((i * j) == a %[mod p])) ->
        (\prod_(i <- l) i)%:Z == (a ^ (n %/ 2 )%Z) %[mod p].
    Proof.
        move: l.
        elim/ltn_ind: n => [n IH].
        move=> [|h t].
        {
            rewrite //=. move=> -> //= _ Hi.
            rewrite div0z expr0z.
            rewrite -foldrE //=.
        }
        move=> nsize oddn Hi.
         *)


        
    (* Lema 10 do TCC: *)
    Lemma primez_fat_exp_modp (a p : int):
        (primesz.primez p) -> (2 < p)%R -> (coprimez a p) -> ~ (exists x, x^2 == a %[mod p]) ->
        ((`|p| - 1)`!)%:Z == (a ^ ((p - 1) %/ 2 )%Z) %[mod p].
    Proof.
        move=> pP pL2 aCp Hx.
        rewrite fact_prod.
        rewrite -[X in (\prod_(1 <= i < X)  i)%N  == _  %[mod p] ]addn1 subnK;
        last by rewrite -ltz_nat -(primesz.primez_abs pP) (primesz.primez_lt0 pP).
        rewrite {3}(primesz.primez_abs pP).
        remember (index_iota )



        have: `|(p - 1)%R|.+1 = `|p|.
            move: (primesz.primez_abs pP) => pabs. rewrite {1}pabs.
            rewrite distnEl. rewrite -addn1 subnK. by [].
            move: (primesz.primez_lt0 pP). rewrite -ltz_nat {1}pabs //=.
            move: (primesz.primez_lt0 pP). rewrite -ltz_nat {1}pabs //=.
        move=> ->. apply/eqP.
        (* 
            k * h == a (mod p)

            (p - 1)! = ((p - 1) * h) * (\prod i in [1, p-1] - {p - 1, h})
                

            (p - 1)! = a^((p-1)/2) (mod p)
            (p - 1)! = a^((p-1)/2) (mod p)



            2 * (sum 1 ... n - 1) = n * (n - 1)
            (sum 1 ... n - 1 | i) + (sum 1 ... n - 1 | F i) = n * (n - 1)

        *)
        (* ... *)
    Abort.

    Close Scope int_scope.
End inversez.