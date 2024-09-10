From HB Require Import structures.
From mathcomp Require Import ssreflect eqtype all_algebra ssrbool ssrint ssralg intdiv seq prime order.
Import Order.Theory.
From Coq Require Import Logic.Decidable.


Set Implicit Arguments.     
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Implementação de Inverso Multiplicativo em Coq *)

(* Algumas provas neste arquivo foram obtidas de https://github.com/thery/mathcomp-extra/ *)

Module inverse.
    Delimit Scope int_scope with Z.
    Open Scope int_scope.

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

    Lemma reflect_modz (a b n : int) :
        reflect (a = b %[mod n]) (a == b %[mod n]).
    Proof.
        apply eqP.
    Qed.

    Lemma aux1 (a b n : int) :
        a * b = 1  %[mod n] -> exists uv, ((fst uv) * b + (snd uv) * n)%R = 1%R.
    Proof.
        move=> /eqP. rewrite eqz_mod_dvd. move=> Hmod.
        apply divzK in Hmod. remember ((a * b - 1) %/ n)%Z as q.
        exists (a, (-q)%R). rewrite /fst /snd.
        rewrite -Heqq in Hmod. 
        rewrite -!mulrzz mulNrz.
        rewrite -!mulrzz in Hmod. rewrite Hmod.
        rewrite GRing.opprB GRing.addrC.
        rewrite -[X in (1 - _ + X)%R = 1%R]GRing.addr0.
        by rewrite GRing.subrKA GRing.addr0.
    Qed.

    Lemma dvdz_add (a b n : int) :
        (n %| a) -> (n %| b) -> (n %| (a + b)%R).
    Proof.
        move=> /dvdzP Ha /dvdzP Hb. case: Ha => q1 Ha.
        case: Hb => q2 Hb. rewrite Ha Hb. rewrite GRing.mulrC.
        rewrite [X in _ %| (_ * _ + X)%R]GRing.mulrC.
        rewrite -GRing.mulrDr. rewrite dvdz_mulr //.
    Qed.

    Lemma aux2 (a b c : int) :
        (exists (x y : int), (a * x + b * y)%R == c%R) <-> (gcdz a b %| c).
    Proof.
        split.
            {
                move=> Heq. case: Heq => [x Heq].
                case: Heq => [y Heq]. move: Heq.
                move=> /eqP Heq.
                have Ha : gcdz a b %| (a * x)%R.
                    rewrite dvdz_mulr // dvdz_gcdl //.
                have Hb : gcdz a b %| (b * y)%R.
                    rewrite dvdz_mulr // dvdz_gcdr //.
                rewrite -Heq.
                rewrite dvdz_add //. 
            }
        move=> /dvdzP H. case : H => [q Hq].
        pose proof (Bezoutz a b).
        case: H => u H. case: H => v Huv.
        rewrite Hq. exists (q * u)%R. exists (q * v)%R.
        rewrite GRing.mulrC.
        rewrite -[X in (_ + X)%R == _]GRing.mulrC.
        rewrite -!GRing.mulrA -GRing.mulrDr Huv //=.
    Qed.
        
        (* Lema 6 do TCC: *)
    Lemma cond_inv (a n : int) :
        (exists b : int, a ^ -1 == b %[mod n]) <-> ((gcdz a n)%R == 1%R).
    Proof.
        split.
        {
            rewrite /inv_mulz /eqP. move=> Hab.
            case : Hab => b Hab. rewrite GRing.mulrC in Hab.
            move: Hab. move=> /reflect_modz Hab. 
            apply aux1 in Hab. case: Hab => w. case: w => x y.
            rewrite //=. move=> Hbn.
            have : exists x y : int, (a * x + n * y)%R == 1.
                exists x. exists y. rewrite GRing.mulrC.
                rewrite (GRing.mulrC n). apply/eqP. move=> //.
            move=> H. clear Hbn.
            apply aux2 in H. rewrite dvdz1 in H.
            move=> //.
        }
        move=> /eqP gcdE1. move: (Bezoutz a n) => Bz.
        case: Bz => x Bz. case: Bz => y Bz. rewrite /inv_mulz.
        exists x. rewrite eqz_mod_dvd. apply/dvdzP.
        exists (-y)%R. rewrite -gcdE1. rewrite -Bz.
        rewrite GRing.mulrC.
        rewrite -{1}(GRing.addr0 (x * a)%R).
        rewrite [X in (X - _)%R = _]GRing.addrC.
        rewrite GRing.addrKA GRing.add0r.
        rewrite -!mulrzz -mulNrz //.
    Qed.

    Compute (iota 1 11).

    Lemma prime_gcdz1 (a p : int):
        (prime `|p|) -> ~~ (div.dvdn `|p| `|a|) -> gcdz p a == 1.
    Proof.
        move=> Hp. apply (prime_coprime `|a|) in Hp as Hpa.
        move=> Ha. rewrite -Hpa in Ha. rewrite /gcdz.
        rewrite /div.coprime in Ha. move=>//.
    Qed. 

    Check (forall (a : int), (1 <= a)%R).

    Lemma aux3 (a b : int):
        a != 0 -> (`|a| < `|b|)%R  -> (b %| a) = false.
    Proof.
        move=> Ha0.
        apply contraTF.
        move=> /dvdzP [q Hab].
        have {}Hab: (`|a|)%R = `|(q * b)%R|.
            rewrite Hab //.
        case Hq : `|q| => [|k].
            rewrite abszM in Hab.
            rewrite Hq in Hab.
            rewrite ssrnat.mul0n in Hab.
            move: Hab. move=> /eqP Hab.
            rewrite -absz_eq0 absz_id absz_eq0 in Hab.
            move: Hab. move=> /eqP Hab. rewrite Hab // in Ha0.
        move: Hab. 
        move=> Hab. rewrite -abszE in Hab.
        rewrite [X in ~~ (X < _)%R]Hab.
        rewrite -abszE. rewrite ltz_nat.
        rewrite abszM Hq.
        rewrite ssrnat.mulSn -ssrnat.addSn.
        rewrite -ssrnat.ltnNge ssrnat.leq_addr //.
    Qed.
            
    Lemma aux4 p (a : int):
        prime p -> (0 < a)%R && (a <= p%:Z - 1)%R -> coprimez a p.
    Proof.
        move=> Hprime /andP Hap.
        case: Hap => Ha0 Hap.
        have Had0 : a != 0.
            rewrite neq_lt Ha0 orbC //=.
        have {}Habs : (`|a| < `|p%:Z|)%R.
            have : ((p%:Z - 1) < p%:Z)%R.
                rewrite -lezD1. 
                rewrite -[X in (_ + X <= _)%R]GRing.addr0 GRing.subrKA.
                rewrite GRing.addr0. rewrite lez_nat ssrnat.leqnn //.
            move=> Hp. apply gtz0_abs in Ha0. rewrite -Ha0 in Hap.
            move: (absz_nat p) => Hpp.
            rewrite -Hpp in Hp.
            rewrite -ltzD1 in Hap.
            rewrite -[X in (_ < _ + X)%R]GRing.addr0 in Hap.
            rewrite GRing.subrKA GRing.addr0 in Hap.
            move=>//.
        move: (aux3 Had0 Habs) => Hpda.
        rewrite dvdzE in Hpda.
        (* Search (prime).
        Search (div.coprime _ _ = div.coprime _ _). *)
        rewrite coprimezE div.coprime_sym prime_coprime.
        rewrite Hpda //=.
        move=>//. 
    Qed.

    Print GRing.sqrrN.

    HB.about int.
    HB.about nat.
    HB.about eqType.
    HB.about GRing.Ring.
    HB.about GRing.SemiRing.
    HB.about GRing.Zmodule.
    HB.about GRing.addNr.

    (* Lema 7 do TCC: *)
    Lemma inv_modp p (a : int):
        (prime p) -> (0 < a)%R && (a <= p%:Z - 1)%R -> 
            exists (k : int), (0 < k <= (p%:Z - 1))%R && ((a * k)%R == 1 %[mod p]).
    Proof.
        move=> Hprime Hap. move: (aux4 Hprime Hap) => Hcp.
    Admitted.

        

    Close Scope int_scope.
End inverse.