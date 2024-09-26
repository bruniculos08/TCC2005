From HB Require Import structures.
From mathcomp Require Import ssreflect eqtype all_algebra ssrbool
                             ssrnat ssrint ssralg intdiv seq prime order.
Import Order.Theory.
From Coq Require Import Logic.Decidable.

Import GRing.Theory.

Set Implicit Arguments.     
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Algumas provas neste arquivo foram obtidas de https://github.com/thery/mathcomp-extra/ *)

(* Módulo específico para primos inteiros *)

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
          
    Close Scope int_scope.
End primesz.

(* Implementação de Inverso Multiplicativo em Coq *)

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

    Lemma modz_mul (a b c d n : int):
        (a == b %[mod n]) -> (c == d %[mod n]) -> (a * c == b * d %[mod n]).
    Proof.
        move=> /eqP aMb /eqP cMd. apply/eqP.
    Abort.

    Lemma mulz_inv (a b c n : int):
        (a ^ -1 == b %[mod n]) && ((a * b)%R == c %[mod n]) -> (a == (c * a)%R %[mod n]).
    Proof.
        move=> /andP [Hinv Hmod].
         rewrite /inv_mulz in Hinv.
        Search (modz).
    Abort.

    Lemma ltz_mod0 (a b : int):
        (b != 0) && (a != 0) -> (0 <= (a %% b)%Z)%R.
    Proof.
        move=> /andP [Hb Ha]. rewrite -modz_abs.
        move: Ha. case: a.
            move=> n nN0.
            rewrite modz_nat. Search (div.modn).
    Abort.
    (*  Documentar o uso de "Set Printing Coercions." no TCC (no Capítulo
        sobre a implementação.  )*)
    
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
(* 
    Lemma dvdzN_mul (n a b : int):
        ~~(n %| a) -> ~~(n %| b) -> ~~(n %| (a * b)%R).
    Proof.
        rewrite !dvdzE abszM.   *)

    Lemma dvdz_mul_or (n a b : int):
        n %| (a * b)%R = (n %| a) || (n %| b).
    Proof.
        rewrite !dvdzE abszM.
        elim/ltn_ind : `|a| => [k Hk].
            move: Hk.
            case: k => {}k.
            {   by rewrite mul0n div.dvdn0. }
            {   move=> Hk. rewrite -addn1 mulnDl mul1n.
                case Hnb : (div.dvdn `|n| `|b|).
                    rewrite Hnb in Hk. rewrite orbC //=.
                    rewrite div.dvdn_addl.
                    specialize (Hk k). rewrite orbC //= in Hk. apply Hk.
                    by [].
                    by [].
                rewrite orbC //=.    
                rewrite Hnb in Hk.
                case HnSk: (div.dvdn `|n| (k + 1)).
                    {   rewrite -[X in div.dvdn _ (_ + X) = _]mul1n -mulnDl.
                        by apply div.dvdn_mulr. }
                    {   specialize (Hk k). rewrite orbC //= in Hk.
                        apply negbTE. apply negbT in Hnb.
                        move: Hnb. apply contra.
                        move=> HSkb.
                        rewrite -[X in div.dvdn _ (_ + X)]mul1n -mulnDl in HSkb.
                        apply negbT in HnSk.     }



                rewrite div.dvdn_addr. }





            by rewrite div.dvdn0.
            rewrite -addn1 mulnDl mul1n.
            case Hc : (div.dvdn `|n| `|b|).
                rewrite orbC //=. 
                rewrite -[X in div.dvdn _ (_ + X)]mul1n. 
                rewrite -mulnDl.
                by apply div.dvdn_mull.
            rewrite orbC //=.
            rewrite -[X in div.dvdn _ (_ + X)]mul1n. 
            rewrite -mulnDl.
            rewrite Hc orbC //= in Hk.
            rewrite div.dvdn_mulr. symmetry.

            move: (div.dvdn_add_eq HSk) => H.
            

        case H : (div.dvdn `|n| (`|a| * `|b|)).
            move: H => /div.dvdnP [q Hq].
            
            
        

    (*  Lema 7 do TCC (Parte 02: o número k é único):  *)
    Lemma invz_modp_uniq (a k1 k2 p : int):
        (primesz.primez p) -> (0 < k1 < p)%R && ((a * k1)%R == 1 %[mod p])
        -> (0 < k2 < p)%R && ((a * k2)%R == 1 %[mod p]) -> k1 == k2.
    Proof.
        rewrite !eqz_mod_dvd => pP /andP [k1L Hk1] /andP [k2L Hk2].
        move: (dvdz_sub Hk1 Hk2). rewrite -addrA. 
        rewrite [X in p %| (_ + X)%R -> _]addrC. rewrite -mulrN1z mulrzBl.
        rewrite intz. rewrite -[X in _ %| (_ + (_ + X + _))%R -> _]mulrN1z.
        rewrite mulNrNz intz mulrN1z -addrA subrr addr0.
        rewrite -mulrN1z mulrzz -mulrA mulrC [X in _ %| (_ + X)%R -> _]mulrC. rewrite -GRing.mulrDl -mulrzz mulrN1z mulrC.
        Set Printing Coercions.
        



    Close Scope int_scope.
End inversez.