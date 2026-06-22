From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




Definition onext n (x : 'I_n) : 'I_n.
Proof.
refine (

  Sub

(if val x == n.-1 then 0 else x.+1)


_

).
case: x => [m /=].
case: n => [ | n] /=.
  by [].
case: ifP.
  move/eqP=> misn.
  move=> _.
  by [].
move=> test_false.
rewrite ltnS.
move=> mlen.
rewrite ltnS.
have neq := negbT test_false.
rewrite ltn_neqAle.
rewrite neq.
rewrite mlen.
by [].

Defined.


Eval compute in val (onext (Ordinal (isT : 2 < 4))).
Eval compute in val (onext (Ordinal (isT : 3 < 4))).





Module MyInj.

Check injective.

Definition injectiveb (aT : finType) (rT : eqType) (f : aT -> rT) : bool :=
 [forall x : aT, forall y : aT, (f x == f y) ==> (x == y)].

Lemma injectiveP (aT : finType) (rT : eqType) (f : aT -> rT) :
  reflect (injective f) (injectiveb f).
Proof.
apply: (iffP forallP).
  move=> Ibf.
  move=> x.
  move=> y.
  move=> Efxy.
  have {Ibf}:= Ibf x.
  move=>/forallP Ibf'.
  have {Ibf'} := Ibf' y.
  move=>/implyP.
  rewrite Efxy.
  rewrite eqxx.
  move=>Ibf''.
  have{Ibf''} := Ibf'' isT.
  move/eqP.
  by [].
move=> If x.
apply/forallP=> y.
apply/implyP=> /eqP Efxfy.
apply/eqP.
apply: If.
by [].
Qed.

End MyInj.


Lemma neg_offset_ord_proof n (i : 'I_n) (p : nat) : i - p < n.
Proof.
have : i < n.
  apply: ltn_ord.
apply: leq_ltn_trans.
by apply: leq_subr.
Qed.

Definition neg_offset_ord n (i : 'I_n) p := Ordinal (neg_offset_ord_proof i p).

Eval compute in (val (neg_offset_ord (Ordinal (isT : 7 < 9)) 4)).





Lemma gauss_ex_p1 : forall n, (\sum_(i < n) i).*2 = n * n.-1.
Proof.
elim=> [|n IH].
  rewrite big_ord0.
  by [].
rewrite big_ord_recr /=.
rewrite doubleD.
rewrite {}IH.
case: n => [| n /=].
  by [].
rewrite -muln2.
rewrite -mulnDr.
rewrite addn2.
rewrite mulnC.
by [].
Qed.

Lemma gauss_ex_p2 : forall n, (\sum_(i < n) i).*2 = n * n.-1.
Proof.
case=> [|n/=].
  by rewrite big_ord0.
rewrite -addnn.
have Hf i : n - i < n.+1.
  rewrite ltnS.
  by apply: leq_subr.
pose f (i : 'I_n.+1) := neg_offset_ord (@ord_max n) i.
have f_inj : injective f.
  move=> x y.
  rewrite /f /=.
  move=>/val_eqP/eqP /= Efxfy.
  apply/val_eqP => /=.
  have -> : \val x = n - (n - x).
    rewrite subKn.
      by [].
    rewrite -ltnS.
    by [].
  rewrite Efxfy.
  rewrite subKn.
  rewrite eqxx.
  by [].
rewrite -ltnS.
by [].
rewrite {1}(reindex_inj f_inj) /=.
rewrite -big_split /=.
have ext_eq : forall i : 'I_n.+1, true -> n - i + i = n.
  move=> i _.
  rewrite subnK.
    by [].
  rewrite -ltnS.
  by [].
rewrite (eq_bigr (fun _ => n) ext_eq).
rewrite sum_nat_const.
rewrite card_ord.
by[].
Qed.

Lemma gauss_ex_p3 : forall n, (\sum_(i < n) i).*2 = n * n.-1.
Proof.
case=> [|n/=]; first by rewrite big_ord0.
rewrite -addnn {1}(reindex_inj rev_ord_inj) -big_split /=.
rewrite -[X in _ = X * _]card_ord -sum_nat_const.
by apply: eq_bigr => i _; rewrite subSS subnK // -ltnS.
Qed.







Definition parking n := 'I_n -> 'I_n -> bool.



Definition sumL n (p : parking n) i := \sum_(j < n) p i j.



Definition sumC n (p : parking n) j := \sum_(i < n) p i j.





Lemma leq_sumL n (p : parking n) i : sumL p i < n.+1.
Proof.

have {2}<-: \sum_(i < n) 1 = n by rewrite -[X in _ = X]card_ord sum1_card.
by apply: leq_sum => k; case: (p _ _).
Qed.

Lemma leq_sumC n (p : parking n) j : sumC p j < n.+1.
Proof.
have {2}<-: \sum_(i < n) 1 = n by rewrite -[X in _ = X]card_ord sum1_card.
by apply: leq_sum => k; case: (p _ _).
Qed.

Lemma inl_inj {A B} : injective (@inl A B). Proof. by move=> x y []. Qed.
Lemma inr_inj {A B} : injective (@inr A B). Proof. by move=> x y []. Qed.

Lemma result n (p : parking n) : 0 < n ->
  exists i, exists j,
   [\/  (i != j) /\ (sumL p i = sumL p j),
        (i != j) /\ (sumC p i = sumC p j) | sumL p i = sumC p j].
Proof.
case: n p => [//|[|n]] p _ /=.
  exists ord0, ord0; apply: Or33.
  by rewrite /sumL /sumC !big_ord_recl !big_ord0.
pose sLC (i : 'I_n.+2 + 'I_n.+2) :=
  match i with
  | inl i => Ordinal (leq_sumL p i)
  | inr i => Ordinal (leq_sumC p i) end.
have [sC_inj | /injectivePn /=] := altP (injectiveP sLC).
  have := max_card (mem (codom sLC)); rewrite card_codom // card_sum !card_ord.
  by rewrite !addnS !addSn !ltnS -ltn_subRL subnn ltn0.
move=> [[i|i] [[j|j] //=]]; [| |move: i j => j i|];
rewrite ?(inj_eq inj_inl, inj_eq inj_inr) => neq_ij [];
by exists i, j; do ?[exact: Or31|exact: Or32|exact: Or33].
Qed.




Lemma sum_odd1 : forall n, \sum_(i < n) (2 * i + 1) = n ^ 2.
Proof.
case=> [|n/=]; first by rewrite big_ord0.
rewrite big_split -big_distrr /= mul2n gauss_ex_p3 sum_nat_const.
by rewrite card_ord -mulnDr addn1 mulnn.
Qed.



Lemma sum_exp : forall x n, x ^ n.+1 - 1 = (x - 1) * \sum_(i < n.+1) x ^ i.
Proof.
move=> x n.
rewrite mulnBl big_distrr mul1n /=.
rewrite big_ord_recr [X in _ = _ - X]big_ord_recl /=.
rewrite [X in _ = _ - (_ + X)](eq_bigr (fun i : 'I_n =>  x * x ^ i))
      => [|i _]; last by rewrite -expnS.
rewrite [X in _ = X - _]addnC [X in _ = _ - X]addnC subnDA addnK.
by rewrite expnS expn0.
Qed.





Lemma bound_square : forall n, \sum_(i < n) i ^ 2 <= n ^ 3.
Proof.
move=> n.
rewrite expnS -[X in _ <= X * _]card_ord -sum_nat_const /=.
elim/big_ind2: _ => // [* |i]; first exact: leq_add.
by rewrite leq_exp2r // ltnW.
Qed.


About big_cat_nat.
Lemma sum_prefix_0 (f : nat -> nat) n m : n <= m ->
  (forall k, k < n -> f k = 0) ->
  \sum_(0 <= i < m) f i = \sum_(n <= i < m) f i.
Proof.
pose H := big_cat_nat.
move => nm f0; rewrite (big_cat_nat (leq0n n) nm) /=.
rewrite big_nat_cond big_mkcondl big1 ?add0n //.
move => i _; case cnd : (0 <= i < n) => //.
apply: f0.
by move/andP: cnd => [_ it].
Qed.





Section cex.

Variable op2 : nat -> nat -> nat.

Hypothesis op2n0 : right_id 0 op2.

Hypothesis op20n : left_id 0 op2.

Hypothesis op2A : associative op2.

Hypothesis op2add : forall x y, op2 x y = x + y.

HB.instance Definition _ := Monoid.isLaw.Build nat 0 op2 op2A op20n op2n0.

Lemma ex_op2 : \big[op2/0]_(i < 3) i = 3.
Proof.
by rewrite !big_ord_recr big_ord0 /= !op2add.
Qed.

End cex.
