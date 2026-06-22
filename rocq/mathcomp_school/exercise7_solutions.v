From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Scope ring_scope.

Section CPGE.

Lemma pinvmx_on_key : unit. Proof. exact: tt. Qed.
Definition pinvmx_on (F : fieldType) (m n : nat) (S : 'M_m)
   (A : 'M[F]_(m, n)) : 'M_(n, m) :=
 locked_with pinvmx_on_key (pinvmx A *m proj_mx S (kermx A)).

Lemma pinvmx_on_sub (F : fieldType) (m n : nat) (S : 'M_(m))
   (A : 'M[F]_(m, n)) : (pinvmx_on S A <= S)%MS.
Proof.
rewrite [pinvmx_on _ _]unlock.
by rewrite (submx_trans (proj_mx_sub _ _ _)) ?genmxE.
Qed.

Lemma mulmxKpV_on (F : fieldType) (m1 m2 n : nat) (S : 'M_(m2))
  (A : 'M[F]_(m1, n)) (B : 'M_(m2, n)) :
  (S :&: kermx B)%MS = 0 ->
  (S + kermx B == 1%:M)%MS ->
  (A <= B)%MS -> A *m pinvmx_on S B *m B = A.
Proof.
move=> SIkB0 SDkB1 subAB; rewrite [pinvmx_on _ _]unlock.
rewrite -[RHS](mulmxKpV subAB).
symmetry.
apply: subr0_eq.
rewrite -mulmxBl -mulmxBr.
apply/sub_kermxP.
apply: mulmx_sub.
rewrite proj_mx_compl_sub.
reflexivity.
by rewrite (eqmxP SDkB1) submx1.
Qed.




Section ex_6_12.

Variables (F : fieldType) (n' : nat).
Let n := n'.+1.

Section Q1.

Variable (u : 'M[F]_n) (S : 'M[F]_n).
Hypothesis eq_keru_imu : (kermx u :=: u)%MS.
Hypothesis S_u_direct : (S :&: u)%MS = 0.
Hypothesis S_u_eq1 : (S + u == 1)%MS.

Fact S_ku_direct : (S :&: kermx u)%MS = 0.
Proof.
apply/eqmx0P; rewrite !(cap_eqmx (eqmx_refl _) eq_keru_imu).
by rewrite !S_u_direct submx_refl.
Qed.
Hint Resolve S_ku_direct.

Fact S_ku_eq1 : (S + kermx u == 1)%MS.
Proof. by rewrite !(adds_eqmx (eqmx_refl _) eq_keru_imu) S_u_eq1. Qed.
Hint Resolve S_ku_eq1.

Implicit Types (x y z : 'rV[F]_n).



Definition w := locked (proj_mx S u).
Definition v := locked (proj_mx u S * pinvmx_on S u).



Lemma wS x : (x *m w <= S)%MS.
Proof.
unlock w.
by rewrite proj_mx_sub.
Qed.

Lemma vS x : (x *m v <= S)%MS.
Proof.
unlock v.
 by rewrite mulmxA mulmx_sub ?pinvmx_on_sub.
Qed.

Lemma w_id x : (x <= S)%MS -> x *m w = x.
Proof.
unlock w => xS.
by rewrite proj_mx_id ?S_u_direct.
Qed.

Lemma Su_rect x : x = x *m w + (x *m v) *m u.
Proof.
unlock v w.
rewrite [x *m (_ *_)]mulmxA mulmxKpV_on ?proj_mx_sub//.
by rewrite add_proj_mx // (eqmxP S_u_eq1) submx1.
Qed.




Lemma Su_dec_eq0 y z : (y <= S)%MS -> (z <= S)%MS ->
  (y + z *m u == 0) = (y == 0) && (z == 0).
Proof.
move=> yS zS; apply/idP/idP; last first.
  by move=> /andP[/eqP -> /eqP ->]; rewrite add0r mul0mx.
rewrite addr_eq0 -mulNmx => /eqP eq_y_Nzu.
have : (y <= S :&: u)%MS by rewrite sub_capmx yS eq_y_Nzu submxMl.
rewrite S_u_direct // submx0 => /eqP y_eq0.
move/eqP: eq_y_Nzu; rewrite y_eq0 eq_sym mulNmx oppr_eq0 eqxx /= => /eqP.
move=> /sub_kermxP; rewrite eq_keru_imu => z_keru.
have : (z <= S :&: u)%MS by rewrite sub_capmx zS.
by rewrite S_u_direct // submx0.
Qed.

Lemma Su_dec_uniq y y' z z' : (y <= S)%MS -> (z <= S)%MS ->
                              (y' <= S)%MS -> (z' <= S)%MS ->
  (y + z *m u == y' + z' *m u) = (y == y') && (z == z').
Proof.
move=> yS zS y'S z'S; rewrite -subr_eq0 opprD addrACA -mulmxBl.
by rewrite Su_dec_eq0 ?addmx_sub ?eqmx_opp // !subr_eq0.
Qed.



Lemma u2_eq0 : u *m u = 0.
Proof. by apply/sub_kermxP; rewrite eq_keru_imu. Qed.

Lemma u2K m (a : 'M_(m,n)) : a *m u *m u = 0.
Proof. by rewrite -mulmxA u2_eq0 mulmx0. Qed.

Lemma uv x : (x <= S)%MS -> (x *m u) *m v = x.
Proof.
move=> xS; have /eqP := Su_rect (x *m u).
rewrite -[X in X == _]add0r Su_dec_uniq ?sub0mx ?vS ?wS //.
by move=> /andP [_ /eqP <-].
Qed.

Lemma uw x : (x <= S)%MS -> (x *m u) *m w = 0.
Proof.
move=> xS; have /eqP := Su_rect (x *m u).
rewrite -[X in X == _]add0r Su_dec_uniq ?sub0mx ?vS ?wS //.
by move=> /andP [/eqP <-].
Qed.



Lemma add_uv_vu : v *m u + u *m v = 1.
Proof.
apply/row_matrixP => i; rewrite !rowE; set x := delta_mx _ _.
rewrite mulmx1 mulmxDr !mulmxA {2}[x]Su_rect mulmxDl u2K addr0.
by rewrite uv ?wS // addrC -Su_rect.
Qed.

Lemma add_wu_uw : w *m u + u *m w = u.
Proof.
apply/row_matrixP => i; rewrite !rowE; set x := delta_mx _ _.
rewrite mulmxDr !mulmxA {2}[x]Su_rect mulmxDl u2K addr0 uw ?wS // addr0.
by have /(canLR (addrK _)) <- := Su_rect x; rewrite mulmxBl u2K subr0.
Qed.

End Q1.




Section Q2.

Variable (u : 'M[F]_n).

Lemma u20_eq_u_kermx v : u ^+ 2 = 0 -> v *m u + u *m v = 1 -> (u == kermx u)%MS.
Proof.
move=> u20 vuDuv_eq1; apply/andP; split; first by apply/sub_kermxP.
apply/rV_subP => x /sub_kermxP xu_eq0.
have /(congr1 (fun w => x *m w)) := vuDuv_eq1; rewrite mulmx1 => <-.
by rewrite mulmxDr !mulmxA xu_eq0 mul0mx addr0 mulmx_sub.
Qed.

End Q2.

Section Q3.

Hypothesis charF_neq2 : [char F]^'.-nat 2%N.

Let u : 'M[F]_3 :=
\matrix_(i, j) ((i == 2%N :> nat) && (j == 1%N :> nat))%:R.
Let w : 'M[F]_3 :=
2%:R^-1 *: 1.

Lemma u_neq0 : u != 0.
by apply/negP => /eqP /matrixP /(_ 2%:R 1) /eqP; rewrite !mxE !eqxx oner_eq0.
Qed.

Lemma wuDuw_eq_u : w *m u + u *m w = u.
Proof.
rewrite -scalemxAl -scalemxAr mul1mx mulmx1 -scalerDl.
rewrite -mulr2n.
rewrite -(mulr_natr (2^-1) 2).
rewrite mulrC.
by rewrite divff ?scale1r ?natf_neq0_pchar.
Qed.

Lemma neq_u_kermxu : (u != kermx u)%MS.
Proof.
suff: \rank u != \rank (kermx u) by apply: contraNneq=> <-.
by rewrite mxrank_ker; have := rank_leq_row u; case: (\rank _) => [|[|[]]].
Qed.

End Q3.
End ex_6_12.
End CPGE.
