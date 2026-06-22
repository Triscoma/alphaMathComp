From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg poly ssrnum ssrint rat intdiv.
From Coq Require Import Lia.
From mathcomp.zify Require Import zify.
From mathcomp.algebra_tactics Require Import ring.

Search _ "ring".
Locate "_ring".
About ring.

Locate Library mathcomp.zify.zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Definition delta (n : nat) := (n.+1 * n)./2.

Lemma deltaS (n : nat) : delta n.+1 = delta n + n.+1.
Proof.
rewrite /delta; lia.
Qed.

Lemma leq_delta (m n : nat) : m <= n -> delta m <= delta n.
Proof.
move=> lemn; apply: half_leq; nia.
Qed.



Lemma delta_square (n : nat) : (8 * delta n).+1 = n.*2.+1 ^ 2.
Proof.
elim: n => // n IHn; rewrite deltaS mulnDr -addSn IHn; lia.
Qed.

Lemma gauss_ex_nat1 (n : nat) : (\sum_(i < n) i).*2 = n * n.-1.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0.
by rewrite big_ord_recr /= doubleD {}IH; nia.
Qed.

Lemma gauss_ex_nat2 (n : nat) : \sum_(i < n) i = (n * n.-1)./2.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0.
rewrite big_ord_recr /= {}IH; nia.
Qed.

Lemma gauss_ex_int1 (n : nat) (m : int) :
  ((\sum_(i < n) (m + i%:R)) * 2 = (m * 2 + n%:R - 1) * n%:R)%R.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0 mulr0.
rewrite big_ord_recr /= mulrDl {}IH -natr1; lia.
Qed.

Lemma sum_squares_p1 (n : nat) :
  (\sum_(i < n) i ^ 2) * 6 = n.-1 * n * (n * 2).-1.
Proof.
elim: n => [|n IHn]; first by rewrite big_ord0.
by rewrite mulSn add2n /= big_ord_recr /= mulnDl {}IHn; nia.
Qed.

Lemma sum_squares_p2 (n : nat) :
  \sum_(i < n) i ^ 2 = (n.-1 * n * (n * 2).-1) %/ 6.
Proof.
elim: n => [|n IHn]; first by rewrite big_ord0.
rewrite mulSn add2n /= big_ord_recr /= {}IHn; nia.
Qed.

Lemma sum_cubes_p1 (n : nat) : (\sum_(i < n) i ^ 3) * 4 = (n * n.-1) ^ 2.
Proof.
elim: n => [|n IHn]; first by rewrite big_ord0.
rewrite big_ord_recr /= mulnDl {}IHn; nia.
Qed.

Lemma sum_cubes_p2 (n : nat) : \sum_(i < n) i ^ 3 = ((n * n.-1) %/ 2) ^ 2.
Proof.
elim: n => [|n IHn]; first by rewrite big_ord0.
rewrite big_ord_recr /= {}IHn; case: n => //= n.
rewrite [in RHS]mulnC -[in RHS]add2n mulnDr divnMDl // sqrnD.
rewrite -addnA addnCA mulnCA [2 * _]mulnC divnK; first lia.
rewrite dvdn2 oddM; lia.
Qed.

Lemma polyeq_p1 (R : comRingType) :
  (4 *: 'X^3 - 3 *: 'X + 1)%R = (('X + 1) * (2 *: 'X - 1) ^+ 2)%R :> {poly R}.
Proof.
rewrite -!mul_polyC; ring.
Qed.
