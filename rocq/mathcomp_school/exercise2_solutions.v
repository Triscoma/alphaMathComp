From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Definition elements {A} (f : _ -> A) n :=
  let l := iota 0 n.+1 in zip l (map f l).


Definition delta n := (n.+1 * n)./2.

Lemma deltaE n : delta n =  (n.+1 * n)./2.
Proof. by []. Qed.

Lemma delta1 : delta 1 = 1.
Proof. by []. Qed.


Compute elements delta 10.


Lemma deltaS n : delta n.+1 = delta n + n.+1.
Proof.
rewrite !deltaE -addn2 mulnDl mulnC halfD.
rewrite !oddM andbF add0n mul2n.
suff -> : ((n.+1).*2)./2 = n.+1 by [].
by rewrite -[RHS](half_bit_double n.+1 false).
Qed.



Lemma leq_delta m n : m <= n -> delta m <= delta n.
Proof.
by move=> H; apply: half_leq; apply: leq_mul.
Qed.


Lemma delta_square n : (8 * delta n).+1 = n.*2.+1 ^ 2.
Proof.
elim: n => // n IH.
rewrite deltaS mulnDr -addSn IH.
rewrite doubleS -addn1 -addnS -addSn addn1.
rewrite sqrnD -addnA /=.
congr (_ + _).
rewrite mulnS.
rewrite [_ * 2]mulSn mulnDr addnA.
congr (_ + _).
by rewrite mulnCA -muln2 -!mulnA mulnC.
Qed.


Definition troot n := 
 let l := iota 0 n.+2 in
 (find (fun x => n < delta x) l).-1.

Lemma trootE n :
  troot n = (find (fun x => n < delta x) (iota 0 n.+2)).-1.
Proof. by []. Qed.

Compute elements troot 10.

Lemma troot_gt0 n : 0 < n -> 0 < troot n.
Proof.
by case: n.
Qed.


Lemma leq_delta_root m : delta (troot m) <= m.
Proof.
rewrite trootE leqNgt.
set l := iota _ _; set f := (fun _ => _).
case E : (find f l).-1 => [|n] //.
have  /(before_find 0) : 
   (find f l).-1 < find f l by rewrite prednK // E.
rewrite E  nth_iota // /f => [->//|].
rewrite -[m.+2](size_iota 0) -E prednK; first by apply: find_size.
by case: find E.
Qed.


Lemma ltn_delta_root m : m < delta (troot m).+1.
Proof.
rewrite /troot leqNgt.
set l := iota _ _; set f := (fun _ => _).
have Hfl : has f l.
  apply/hasP; exists m.+1; first by rewrite mem_iota leq0n leqnn.
  rewrite /f /delta -{1}[m.+1](half_bit_double _ false).
  by apply/half_leq; rewrite add0n -mul2n leq_mul2r orbT.
have := nth_find 0 Hfl; rewrite {1}/f.
case E : _.-1 => [|n] //.
  case: find E => // [] [|n] //.
  by rewrite nth_iota //=; case: (m).
rewrite nth_iota.
  by rewrite -E prednK // ltnNge ltnS.
by rewrite -(size_iota 0 m.+2) -has_find.
Qed.

Lemma leq_root_delta m n : (n <= troot m) = (delta n <= m).
Proof.
case: leqP => [/leq_delta/leq_trans->//|dmLn].
  apply: leq_delta_root.
apply/sym_equal/idP/negP.
rewrite -ltnNge.
by apply: leq_trans (ltn_delta_root _) (leq_delta dmLn).
Qed.

Lemma leq_troot m n : m <= n -> troot m <= troot n.
Proof.
by move=> mLn; rewrite leq_root_delta (leq_trans (leq_delta_root _)).
Qed.

Lemma troot_delta m n : (troot m == n) = (delta n <= m < delta n.+1).
Proof.
by rewrite ltnNge -!leq_root_delta -ltnNge ltnS -eqn_leq eq_sym.
Qed.

Lemma troot_deltaK n : troot (delta n) = n.
Proof.
by apply/eqP; rewrite troot_delta leqnn deltaS -addn1 leq_add2l.
Qed.


Definition tmod n := n - delta (troot n).

Lemma tmodE n : tmod n = n - delta (troot n).
Proof. by []. Qed.

Lemma tmod_delta n : tmod (delta n) = 0.
Proof.
by rewrite tmodE troot_deltaK subnn.
Qed.

Lemma delta_tmod n : n = delta (troot n) + tmod n.
Proof.
by rewrite addnC (subnK (leq_delta_root _)).
Qed.

Lemma leq_tmod_troot n : tmod n <= troot n.
Proof.
by rewrite leq_subLR -ltnS -addnS -deltaS ltn_delta_root.
Qed.

Lemma ltn_troot m n : troot m < troot n -> m < n.
Proof.
rewrite leq_root_delta deltaS => /(leq_trans _) -> //.
by rewrite [X in X < _]delta_tmod ltn_add2l ltnS leq_tmod_troot.
Qed.

Lemma leq_tmod m n : troot m = troot n -> (tmod m <= tmod n) = (m <= n).
Proof.
move=> tmEtn.
rewrite [X in _ = (X <= _)]delta_tmod.
rewrite [X in _ = (_ <= X)]delta_tmod.
by rewrite tmEtn leq_add2l.
Qed.

Lemma leq_troot_mod m n : 
   m <= n = 
   ((troot m < troot n) || ((troot m == troot n) && (tmod m <= tmod n))).
Proof.
case: leqP => [|dmGdn] /= ; last first.
  apply/idP.
  apply: (leq_trans (_ : _ <= delta (troot m).+1)).
    by rewrite ltnW // ltn_delta_root.
  apply: (leq_trans (_ : _ <= delta (troot n))).
    by apply: leq_delta.
  by apply: leq_delta_root.
rewrite leq_eqVlt => /orP[/eqP dnEdm|dmLdn].
  rewrite dnEdm eqxx /=.
  rewrite [X in (X <= _) = _]delta_tmod [X in _ <= X = _]delta_tmod.
       by rewrite dnEdm leq_add2l.
rewrite (gtn_eqF dmLdn) /=.
apply/idP/negP.
rewrite -ltnNge.
apply: (leq_trans (ltn_delta_root _)).
apply: (leq_trans _ (leq_delta_root _)).
by apply: leq_delta.
Qed.



Definition fermat n := (2 ^ (2 ^ n)).+1.

Lemma fermatE n : fermat n = (2 ^ (2 ^ n)).+1.
Proof. by []. Qed.

Compute elements (prime \o fermat) 4.


Lemma dvd_exp_odd a k : 
  0 < a -> odd k -> a.+1 %| (a ^ k).+1.
Proof.
move=> aP kO.
rewrite -[k]odd_double_half {}kO add1n.
elim: {k}_./2 => [|k IH]; first by apply/dvdnn. 
rewrite doubleS.
rewrite (_ : (a ^ k.*2.+3).+1 = 
             (a ^ 2 * (a ^ k.*2.+1).+1) - (a ^ 2 - 1)); last first.
  rewrite mulnSr -expnD !addSn subnBA ?expn_gt0 ?aP //.
  by rewrite addnAC addnK addn1.
rewrite dvdn_sub ?dvdn_mull //.
by rewrite -[X in _ %| _ - X](exp1n 2) subn_sqr addn1 dvdn_mull.
Qed.


Lemma odd_log_eq0 n : 0 < n -> logn 2 n = 0 -> odd n.
Proof.
case: n => // n _ HL.
have : 2 \notin primes n.+1.
  rewrite -logn_gt0.
  by case: (logn 2 n.+1) HL.
by rewrite mem_primes /= dvdn2 negbK.
Qed.


Lemma odd_div_log n : 0 < n -> odd (n %/ 2 ^ logn 2 n).
Proof.
move=> nP.
apply: odd_log_eq0.
  rewrite divn_gt0 ?expn_gt0 //.
  apply: dvdn_leq => //.
  apply: pfactor_dvdnn.
rewrite logn_div.
  by rewrite pfactorK // subnn.
by apply: pfactor_dvdnn.
Qed.


Lemma prime_2expS m : 
  0 < m -> prime (2 ^ m).+1 -> m = 2 ^ logn 2 m.
Proof.
move=> mP Hp.
pose a := 2 ^ logn 2 m.
pose b := m %/ a.
have : (2 ^ a).+1 %| (2 ^ m).+1. 
  rewrite -(divnK (pfactor_dvdnn 2 m)).
  rewrite mulnC expnM.
apply: dvd_exp_odd; first by apply: expn_gt0.
  by apply: odd_div_log.
have F : (2 ^ a).+1 != 1.
  by rewrite eq_sym neq_ltn ltnS expn_gt0.
move=> /(prime_nt_dvdP Hp).
move=> /(_ F) [] /eqP.
by rewrite eqn_exp2l // => /eqP{1}<-.
Qed.


Lemma odd_fermat n : odd (fermat n).
Proof.
by rewrite /= oddX negb_or eq_sym neq_ltn expn_gt0.
Qed.


Lemma dvdn_exp2m1 a k : a.+1 %| (a ^ (2 ^ k.+1)).-1.
Proof.
elim: k => /= [|k IH].
  rewrite expn1 -subn1 -[X in _ %| _ - X](exp1n 2).
  by rewrite subn_sqr addn1 dvdn_mull //.
rewrite -subn1 -{2}[1](exp1n 2) expnS mulnC expnM subn_sqr.
by rewrite dvdn_mulr // subn1.
Qed.


Lemma dvdn_fermat m n : m < n -> fermat m %| (fermat n).-2.
Proof.
move=> mLn.
rewrite fermatE /= -(subnK mLn) -addSnnS addnC.
by rewrite expnD expnM dvdn_exp2m1.
Qed.

Lemma fermat_gt1 n : 1 < fermat n.
Proof.
by rewrite ltnS expn_gt0.
Qed.


Lemma coprime_fermat m n : m < n -> coprime (fermat m) (fermat n).
Proof.
move=> mLn.
rewrite /coprime -(subnK (fermat_gt1 n)) subn2.
case/dvdnP: (dvdn_fermat mLn) => k ->.
by rewrite gcdnMDl [_ == _]coprimen2 odd_fermat.
Qed.




