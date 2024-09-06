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
        Notation "a ^ -1 = m %[mod n ]" := (@inv_mulz m a n) (at level 30) : int_scope.

        Lemma reflect_modz (a b n : int) :
            reflect (a = b %[mod n]) (a == b %[mod n]).
        Proof.
            apply eqP.
        Qed.

        Lemma eq_modz (a b n : int) : 
            (a = b %[mod n]) <-> (a == b %[mod n]).
        Proof.
            by apply: Bool.reflect_iff ; apply: reflect_modz.
        Qed.

        Lemma aux1 (a b n : int) :
            a * b = 1  %[mod n] -> exists uv, ((fst uv) * b + (snd uv) *  n)%R = 1%R.
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

        Lemma cond_inv (a n : int) :
            (exists b, @inv_mulz b a n) -> ((gcdz a n) == 1).
        Proof.
                move=> [b] H. rewrite /inv_mulz in H.
                move: H. move=> /eqP H.
                apply aux1 in H.
                case: H => w.
                case: w => [x y]. rewrite /fst /snd.
                move=> Heq. 
                move: (Bezoutz a n) => [x1 H].
                case: H => x2 H.
                apply/eqP. 
                have He1: 1 = 1%R.
                    by [].
                rewrite He1. rewrite -Heq.
                symmetry.
                rewrite -Heq.

                move=> [y] Hbz. rewrite eqz_mod_dvd in H.
                (* Search (_ %| _).  *)
                apply divzK in H.
                pose q := ((a * b - 1) %/ n)%Z.

    Close Scope int_scope.
End inverse.