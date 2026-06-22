
From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

  

Section Algebraic_part.

Open Scope ring_scope.
Import GRing.Theory Num.Theory.



Variable n : nat.
Variables na nb: nat.
Hypothesis nbne0: nb != 0%N.

Definition a:rat := (Posz na)%:~R.
Definition b:rat := 
(Posz nb)%:~R.

Definition pi := 
a / b.


Definition f :{poly rat} := 
  (n`!)%:R^-1 *: ('X^n * (a%:P -  b*:'X)^+n).

Definition F :{poly rat} := \sum_(i < n.+1) (-1)^i *: f^`(2*i).




Lemma bne0: b != 0.
Proof. by rewrite intr_eq0. Qed.

Lemma P1_size: size (a%:P -  b*:'X) = 2%N.
Proof.
have hs:  size (- (b *: 'X)) = 2%N.
  by rewrite size_opp size_scale ?bne0 // size_polyX.
by rewrite  addrC size_addl hs ?size_polyC //;  case:(a!= 0).
Qed.


Lemma P1_lead_coef: lead_coef (a%:P -  b*:'X) = -b.
Proof.
rewrite addrC lead_coefDl.
  by rewrite lead_coefN lead_coefZ lead_coefX mulr1.
by rewrite size_opp size_scale ?bne0 // size_polyX size_polyC; case:(a!= 0).
Qed.


Lemma P_size : size ((a%:P -  b*:'X)^+n)  = n.+1.
elim:n=>[| n0 Hn0]; first by rewrite expr0 size_polyC.
rewrite exprS size_proper_mul.
  by rewrite P1_size /= Hn0.
by rewrite lead_coef_exp P1_lead_coef -exprS expf_neq0 // oppr_eq0 bne0.
Qed.


Lemma int_Qint (z:int) : z%:~R \is a (@Num.int rat).
Proof. by apply/intr_int; exists z. Qed.

Lemma nat_Qint (m:nat) : m%:R \is a (@Num.nat rat).
Proof. by apply/natr_nat; exists m. Qed.


Lemma comp_poly_exprn: 
   forall (p q:{poly rat}) i, p^+i \Po q = (p \Po q) ^+i.
move=> p q; elim=>[| i Hi].
  by rewrite !expr0 comp_polyC.
by rewrite !exprS comp_polyM Hi.
Qed.




Lemma f_small_coef0 i: (i < n)%N -> f`_i = 0.
Proof.
move=> iltn;rewrite /f coefZ.
apply/eqP; rewrite mulf_eq0 invr_eq0 pnatr_eq0 eqn0Ngt (fact_gt0 n) /=.
by rewrite coefXnM iltn.
Qed.



Lemma f_int i: (n`!)%:R * f`_i \is a (@Num.int rat).
Proof.
rewrite /f coefZ mulrA mulfV; last by rewrite pnatr_eq0 -lt0n (fact_gt0 n).
rewrite mul1r; apply/polyOverP.
rewrite rpredM ?rpredX ?polyOverX //.
by rewrite rpredB ?polyOverC ?polyOverZ ?polyOverX // int_Qint.
Qed.


Lemma derive_f_0_int: forall i, f^`(i).[0] \is a (@Num.int rat).
Proof.
move=> i.
rewrite horner_coef0 coef_derivn addn0 binomial.ffactnn.
case:(boolP (i <n)%N).
  move/f_small_coef0 ->.
  by rewrite mul0rn // int_Qint.
rewrite -leqNgt.
move/binomial.bin_fact <-.
rewrite /f coefZ -mulrnAl -mulr_natr mulrC mulnC !natrM !mulrA mulfVK.
rewrite !rpredM // ; try exact: intr_nat.
  apply/polyOverP.
  rewrite rpredM // ?rpredX ?polyOverX //.
  by rewrite ?rpredB ?polyOverC ?polyOverZ ?polyOverX // int_Qint.

by rewrite pnatr_eq0 eqn0Ngt (fact_gt0 n).
Qed.



Lemma F0_int : F.[0] \is a (@Num.int rat).
Proof.
rewrite /F horner_sum rpred_sum // =>  i _ ; rewrite !hornerE rpredM //.
  by rewrite -exprnP rpredX.
by rewrite derive_f_0_int.
Qed.


Lemma pf_sym:  f \Po (pi%:P -'X) = f.
Proof.
rewrite /f comp_polyZ;congr (_ *:_).
rewrite comp_polyM   !comp_poly_exprn.
rewrite comp_polyB comp_polyC !comp_polyZ !comp_polyX scalerBr /pi.
have h1:    b%:P * (a / b)%:P = a%:P.
  by rewrite polyCM mulrC -mulrA -polyCM mulVf ?bne0 // mulr1.
suff->: (a%:P - (b *: (a / b)%:P - b *: 'X)) = b%:P * 'X.
  rewrite exprMn mulrA - exprMn [X in _ = X]mulrC.
  congr (_ *_); congr (_^+_).
  rewrite mulrC mulrBr; congr (_ -_)=>//.
  by rewrite mul_polyC.
by rewrite -!mul_polyC h1 opprB addrA addrC addrA addNr add0r.
Qed.



Lemma  derivn_fpix i :
      (f^`(i)\Po(pi%:P -'X))= (-1)^+i *: f^`(i).
Proof.
elim:i ; first by rewrite /= expr0 scale1r pf_sym.
move => i Hi.
set fx := _ \Po _.
rewrite derivnS exprS -scalerA -derivZ -Hi deriv_comp !derivE.
by rewrite mulrBr mulr0 add0r mulr1 -derivnS /fx scaleN1r opprK.
Qed.


Lemma FPi_int : F.[pi] \is a (@Num.int rat).
Proof.
rewrite /F horner_sum rpred_sum //.
move=> i _ ; rewrite !hornerE rpredM //.
  by rewrite -exprnP rpredX.
move:(derivn_fpix (2*i)).
rewrite  mulnC exprM sqrr_sign scale1r => <-.
by rewrite horner_comp !hornerE subrr derive_f_0_int.
Qed.




Lemma D2FDF : F^`(2) + F = f.
Proof.
rewrite /F linear_sum /=.
rewrite (eq_bigr (fun i:'I_n.+1 => (((-1)^i *: f^`(2 * i.+1)%N)))); last first.
  move=> i _ ;rewrite !derivZ; congr (_ *:_).
  rewrite -!derivnS;congr (_^`(_)).
  by rewrite mulnS addnC addn2.
rewrite [X in _ + X]big_ord_recl muln0 derivn0.
rewrite -exprnP expr0 scale1r (addrC f) addrA -[X in _ = X]add0r.
congr (_ + _).
rewrite big_ord_recr addrC addrA -big_split big1=>[| i _].
  rewrite add0r /=; apply/eqP; rewrite scaler_eq0 -derivnS derivn_poly0.
    by rewrite eqxx orbT.
  suff ->: (size f) = (n + n.+1)%N by rewrite -plus_n_O leqnSn.
  rewrite /f size_scale; last first.
    by rewrite invr_neq0 // pnatr_eq0 -lt0n (fact_gt0 n).
  rewrite size_monicM ?monicXn //; last by rewrite -size_poly_eq0 P_size.
  by rewrite  size_polyXn P_size.
rewrite /bump /= -scalerDl.
apply/eqP;rewrite scaler_eq0 /bump -exprnP add1n exprSr.
by rewrite mulrN1 addrC subr_eq0 eqxx orTb.
Qed.

End Algebraic_part.

