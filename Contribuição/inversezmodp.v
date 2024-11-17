From mathcomp Require Import all_ssreflect all_algebra.
From contributions Require Import primez.
From Coq Require Import Logic.Decidable.
Import Order.Theory.
Import GRing.Theory.


Set Implicit Arguments.     
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*  Algumas provas neste arquivo foram obtidas de https://github.com/thery/mathcomp-extra/ *)

(*  Implementação de Inverso Multiplicativo em Coq *)
Module inversezmodp.
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

    Definition legendre_symb {p : int} (H : primez.primez p) (a : int) :=
        if (a ^ ((p - 1) %/ 2)%Z == 1 %[mod p]) then 1%Z
        else if (p %| a)%Z then 0%Z
        else 1%Z.   

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
