From HB Require Import structures.
From mathcomp Require Import ssreflect eqtype all_algebra ssrbool ssrint ssralg intdiv.
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
            (n %| a)%Z -> (n %| b)%Z -> (n %| (a + b)%R).
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
        
        Lemma cond_inv (a n : int) :
            (exists b : int, a ^ -1 == b %[mod n]) -> ((gcdz a n)%R == 1%R).
        Proof.
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
        Qed.

    Close Scope int_scope.
End inverse.