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
        move=> /dvdzP[q1 ->] /dvdzP[q2 ->].
        by rewrite -GRing.mulrDl dvdz_mull.
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

    Search (_ %% _).

    Compute abszN.

    (* Lemma auxn (n : nat):
        `|(Negz n)|%R = `|(- (n.+1)%:Z)%R|.
    Proof.
        by [].
    Qed. *)

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

    Lemma absz_le_mod (a n : int):
        (((a %/ n)%Z * n)%R <= `|a|%R)%R.
    Proof.

        case: a => a.
        (* caso: a = |a| *)
        {
            elim/ltn_ind: a => x IH. 
        }


        (* 
            Ideia:

            - Indução forte em |a|:
            forall m < |a| -> (a /  * m) <=  


        *)


        move: n.
        elim/ltn_ind: (`|a|) => [k] Hk. 
        

    Lemma absz_mod (a n : int):
        (n != 0)%Z -> (a %% n)%Z = `|(a %% n)%Z|.
    Proof.
        move=> nD0. remember (`|a|%N) as x.
        rewrite /modz.
        (* 
            Ideia: 
                a %% n = |a %% n|
            por inducao em |a|:
                se |a| >= |n| então visto que (a %% n < |a|) temos
                pela hipótese.
                se |a| < |n| então (a/n * n)     
        *)

        move=> n0. rewrite -{1}modz_abs.
        move: (modz_absm a n) => H.
        rewrite -modz_abs in H.
        rewrite -[X in _ = X]modz_abs in H.
        rewrite -[X in _ * X = _ %[mod _]]modz_abs in H.
        move: H n0. case: a => a Ha.
            {
                rewrite ltz_nat //= in Ha.
                rewrite exprnP expr0z mul1r in Ha.
                rewrite -[X in _ -> _ = Posz `|X|]modz_abs.
                by rewrite modz_nat absz_nat.
            }
            {
                rewrite //= in Ha. rewrite NegzE.
                rewrite NegzE in Ha. rewrite exprnP expr1z in Ha.
                Search (_ < _). 
                
            }

        rewrite  in H.
        Search (modz).

        Search (_ %% _).

    Lemma mul_invz (a b c n : int):
        (a ^ -1 == b %[mod n]) && ((a * b) == c %[mod n]) -> (a == c * b %[mod n]).
    Proof.
        move=> /andP [Hinv Hmod]. rewrite /inv_mulz in Hinv.
        Search (modz).
    Abort.

    Lemma ltz_mod0 (a b : int):
        (b != 0) && (a != 0) -> (0 <= (a %% b)%Z)%R.
    Proof.
        move=> /andP [Hb Ha]. rewrite -modz_abs.
        move: Ha. case: a.
            move=> n nN0.
            rewrite modz_nat. Search (div.modn).
            Search (_ || _).
    Abort.

    (* Lema 7 do TCC: *)
    Lemma inv_modp (p a : int):
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
        rewrite /inv_mulz in Hb.
        rewrite -modzMmr in Hb.
        exists (b %% p). apply/andP. split; last by [].
        Search (coprimez).
        Search (_ %% _).

        have: (0 <= (b %% p)%Z)%R.
            Search ((_ %% _)%Z).

        exists (b %% p). apply/andP. split.
            {
                have {}Hb: (exists k : int, (b %% p)%Z ^ -1 == k %[mod p]).
                    by exists a; rewrite /inv_mulz mulrC.
                rewrite cond_inv in Hb.
                    
            }
    Abort.

    Close Scope int_scope.
End inversez.