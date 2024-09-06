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
        Definition inv_mulz_b (m a : int) {n} : bool := a * m == 1 %[mod n].
        Compute (@inv_mulz_b 8 15 7).
        Compute (@inv_mulz_b 8 2 7).

        (* Definição de inverso multiplicativo como proposição: *)
        Definition inv_mulz (m a : int) {n} : Prop := a * m = 1 %[mod n].
        Compute (@inv_mulz 8 15 7).
        Compute (@inv_mulz 8 2 7).

        (* Notação para inverso multiplicativo: *)
        (* Notation "a ^ -1 = m %[mod n ]" := (@inv_mulz m a n) (at level 30) : int_scope. *)

        Lemma reflect_modz (a b n : int) :
            reflect (a = b %[mod n]) (a == b %[mod n]).
        Proof.
            (* 
                Tem-se uma igualdade, o que é justamente o provado pelo lema
                eqP: 
            *)
            apply eqP.
            (* 
                unfold modz.
                pose proof @eqP.
                unfold Equality.axiom in X.
                specialize (X _ ((a - (a %/ n)%Z * n)%R) ((b - (b %/ n)%Z * n)%R)).
                apply X. 
            *)
        Qed.

        Lemma eq_modz (a b n : int) : 
            (a = b %[mod n]) <-> (a == b %[mod n]).
        Proof.
            by apply: Bool.reflect_iff ; apply: reflect_modz.
        Qed.

        (* Lemma aux1 (a n : int) :
            exists uv, ((fst uv) * a + (snd uv) * (- n))%R = 1%R.
             *)

        Lemma cond_inv (a n : int) :
            (exists b, @inv_mulz b a n) -> ((gcdz a n) = 1).
        Proof.
            {
                intros. destruct H as [b].
                unfold inv_mulz in H.
                pose proof (Bezoutz (a%Z) (n%Z)).
                destruct H0 as [x]. destruct s as [y].
                apply eq_modz in H.
                rewrite eqz_mod_dvd in H.
                pose proof (@dvdzP n (a * b - 1)).
                apply Bool.reflect_iff in H0.
                apply H0 in H.
                destruct H as [q].
                clear H0.
                rewrite -e.
                pose proof (coprimezP a n).
                assert (exists uv, ((fst uv) * a + (snd uv) * (- n))%R = 1%R).
                {
                    exists (b,(q)). simpl.
                    rewrite <- mulrzz.
                    rewrite <- mulrzz.
                    rewrite mulrNz.
                    rewrite <- mulrzz in H.
                    rewrite <- mulrzz in H.
                    rewrite <- H.
                    rewrite mulrzz.
                    rewrite mulrzz.
                    rewrite <- intRing.mulzC.
                    rewrite <- intRing.mulzC.
                    rewrite <- (@intRing.mulzC b _).
                    
                    
                    (* unfold "- _". *)
                    (* pose proof (intRing.mulzN q n). *)

                    unfold minus. unfold mulz.
                }


                (* unfold inv_mulz.
                apply contraPeq.
                intros. unfold not.
                intros. destruct H0 as [m].
                pose proof (@eqP int).
                unfold Equality.axiom in X.
                specialize (X (gcdz a (n + 1)) 1).
                Search (reflect _ _ -> _).
                apply negPP in X as X1.
                apply Bool.reflect_iff in X1.
                apply X1 in H as H1.
                unfold not in H1. apply H1.
                apply Bool.reflect_iff in X as X2.
                apply X2. rewrite <- gcdz_modl. *)
                (* apply <- X2. *)
                (* rewrite eqz_mod_dvd in H. 
                pose proof (@dvdzP (n + 1) (a * b - 1)). *)
                (* unfold "%|" in H0. simpl in H0.
                unfold dvdz in H0.
                unfold div.dvdn in H0.
                unfold div.modn in H0. *)
            }

    Close Scope int_scope.
End inverse.