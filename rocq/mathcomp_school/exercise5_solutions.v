From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory UnityRootTheory.
Open Scope ring_scope.

Section PreliminaryLemmas.


Search "Cnat".
About Aint_Cnat.
Check Num.nat.
About Num.nat.
Lemma Cnat_add_eq1 : {in @Num.nat algC &, forall x y,
   (x + y == 1) = ((x == 1) && (y == 0))
               || ((x == 0) && (y == 1))}.
Proof.
Search (reflect _ (_ \in Num.nat)).
move=> x y /natrP [n ->] /natrP [m ->]; rewrite -natrD !pnatr_eq1 ?pnatr_eq0.
by move: n m => [|[|?]] [|[|?]].
Qed.

Lemma ReM (x y : algC) :
  'Re (x * y) = 'Re x * 'Re y - 'Im x * 'Im y.
Proof.
rewrite {1}[x]algCrect {1}[y]algCrect mulC_rect Re_rect //;
by rewrite rpredD ?rpredN // rpredM // ?Creal_Re ?Creal_Im.
Qed.

Lemma ImM (x y : algC) :
  'Im (x * y) = 'Re x * 'Im y + 'Re y * 'Im x.
Proof.
rewrite {1}[x]algCrect {1}[y]algCrect mulC_rect Im_rect //;
by rewrite rpredD ?rpredN // rpredM // ?Creal_Re ?Creal_Im.
Qed.

End PreliminaryLemmas.



Section GaussianIntegers.

Definition gaussInteger :=
  [pred x : algC | ('Re x \in Num.int) && ('Im x \in Num.int)].

Lemma Cint_GI (x : algC) : x \in Num.int -> x \in gaussInteger.
Proof.
move=> x_int; rewrite inE (Creal_ReP _ _) ?(Creal_ImP _ _) ?Creal_Cint //.
by rewrite x_int rpred0 .
all: apply Rreal_int; assumption.
Qed.



Lemma GI_subring : subring_closed gaussInteger.
Proof.
split => [|x y /andP[??] /andP[??]|x y /andP[??] /andP[??]].
- by rewrite Cint_GI.
- by rewrite inE !raddfB /= ?rpredB.
by rewrite inE ReM ImM rpredB ?rpredD // rpredM.
Qed.

HB.instance Definition _ :=  GRing.isSubringClosed.Build _ _ GI_subring.

Record GI := GIof { algGI : algC; algGIP : algGI \in gaussInteger }.
Hint Resolve algGIP.

HB.instance Definition _ := [isSub for algGI].
HB.instance Definition _ := [Choice of GI by <:].
HB.instance Definition _ := [SubChoice_isSubComRing of GI by <:].

Lemma GIRe (x : GI) : 'Re (val x) \in Num.int.
Proof. by have /andP [] := algGIP x. Qed.
Lemma GIIm (x : GI) : 'Im (val x) \in Num.int.
Proof. by have /andP [] := algGIP x. Qed.
Hint Resolve GIRe GIIm.

Canonical ReGI x := GIof (Cint_GI (GIRe x)).
Canonical ImGI x := GIof (Cint_GI (GIIm x)).

Definition invGI (x : GI) := insubd x (val x)^-1.
Definition unitGI := [pred x : GI | (x != 0)
          && ((val x)^-1 \in gaussInteger)].



Fact mulGIr : {in unitGI, left_inverse 1 invGI *%R}.
Proof.
move=> x /andP [x_neq0 xVGI]; rewrite /invGI.
by apply: val_inj; rewrite /= insubdK // mulVr ?unitfE.
Qed.

Fact unitGIP (x y : GI) : y * x = 1 -> unitGI x.
Proof.
rewrite /unitGI => /(congr1 val) /=.
have [-> /eqP|x_neq0] := altP (x =P 0); first by rewrite mulr0 eq_sym oner_eq0.
by move=> /(canRL (mulfK x_neq0)); rewrite mul1r => <- /=.
Qed.

Fact unitGI_out : {in [predC unitGI], invGI =1 id}.
Proof.
move=> x.
rewrite 2!inE /= /unitGI.
rewrite negb_and negbK => /predU1P [->|/negPf xGIF];
by apply: val_inj; rewrite /invGI ?val_insubd /= ?xGIF // invr0 if_same.
Qed.

HB.instance Definition _ :=
  GRing.ComRing_hasMulInverse.Build GI mulGIr unitGIP unitGI_out.



Lemma conjGIE (x : algC) : (x^* \in gaussInteger) = (x \in gaussInteger).
Proof.
by rewrite ![_ \in gaussInteger]inE Re_conj Im_conj/= rpredN.
Qed.

Fact conjGI_subproof (x : GI) : (val x)^* \in gaussInteger.
Proof. by rewrite conjGIE. Qed.

Canonical conjGI x := GIof (conjGI_subproof x).

Definition gaussNorm (x : algC) := x * x^*.
Lemma gaussNorm_val (x : GI) : gaussNorm (val x) = val (x * conjGI x).
Proof. by []. Qed.



Lemma gaussNormE x : gaussNorm x = `|x| ^+ 2.
Proof. by rewrite normCK. Qed.

Lemma gaussNormCnat (x : GI) : gaussNorm (val x) \in Num.nat. Search (_ ^+ 2 \in Num.nat). Search Num.int Num.nat.
Proof. by rewrite /gaussNorm -normCK normC2_Re_Im rpredD // natr_exp_even. Qed.
Hint Resolve gaussNormCnat.

Lemma gaussNorm1 : gaussNorm 1 = 1.
Proof. by rewrite /gaussNorm rmorph1 mulr1. Qed.

Lemma gaussNormM : {morph gaussNorm : x y / x * y}.
Proof. by move=> x y; rewrite /gaussNorm rmorphM mulrACA. Qed.



Lemma rev_unitrPr (R : comUnitRingType) (x y : R) :
   x * y = 1 -> x \in GRing.unit.
Proof. by move=> ?; apply/unitrPr; exists y. Qed.

Lemma eq_algC a b :
  (a == b :> algC) = ('Re a == 'Re b) && ('Im a == 'Im b).
Proof.
rewrite -subr_eq0 [a - b]algCrect -normr_eq0 -sqrf_eq0.
rewrite normC2_rect ?paddr_eq0 ?sqr_ge0 -?realEsqr ?Creal_Re ?Creal_Im //.
by rewrite !sqrf_eq0 !raddfB ?subr_eq0.
Qed.

Lemma primitive_root_i : 4.-primitive_root ('i : algC).
Proof.
have : 'i ^+ 4 = 1 :> algC by rewrite [_ ^+ (2 * 2)]exprM sqrCi -signr_odd expr0.
move=> /prim_order_exists [] // [//|[|[|[//|[//|//]]]]] /prim_expr_order.
  rewrite expr1 => /(congr1 (fun x => 'Im x)) /eqP.
  by rewrite Im_i (Creal_ImP _ _) ?oner_eq0 ?rpred1.
by move/eqP; rewrite sqrCi eq_sym -addr_eq0 paddr_eq0 ?ler01 ?oner_eq0.
Qed.

Lemma primitive_rootX_unity (C: fieldType) n (x : C) :
  n.-primitive_root x ->
  n.-unity_root =i [seq x ^+ (val k) | k <- enum 'I_n].
Proof.
move=> x_p y; rewrite -topredE /= unity_rootE; apply/idP/idP; last first.
  by move=> /mapP [k _ ->]; rewrite exprAC [x ^+ _]prim_expr_order // expr1n.
by move=> /eqP/(prim_rootP x_p)[k ->]; apply/mapP; exists k; rewrite ?mem_enum.
Qed.

Lemma unitGI_norm1 (a : GI) :
  (a \in GRing.unit) = (val a \in 4.-unity_root).
Proof. 
transitivity (gaussNorm (val a) == 1).
  apply/idP/idP; last first.
  Check natr_mul_eq1.
    by rewrite gaussNorm_val (val_eqE _ (1 : GI)) => /eqP /rev_unitrPr.
  move=> /unitrPr [b /(congr1 (gaussNorm \o val)) /=] /eqP.
 by rewrite gaussNormM gaussNorm1 natr_mul_eq1 // => /andP [].
rewrite (primitive_rootX_unity primitive_root_i).
rewrite (map_comp (GRing.exp 'i) val) val_enum_ord /=.
rewrite /= expr0 expr1 sqrCi exprSr sqrCi mulN1r.
rewrite !in_cons in_nil ?orbF orbA orbAC !orbA orbAC -!orbA.
rewrite [val a in LHS]algCrect gaussNormE normC2_rect ?Creal_Re ?Creal_Im //.
rewrite Cnat_add_eq1 ?natr_exp_even // !sqrf_eq0 !sqrf_eq1.
rewrite andb_orr andb_orl -!orbA.
rewrite ?[val _ == _]eq_algC !raddfN /=.
by rewrite Re_i Im_i ?(Creal_ReP 1 _) ?(Creal_ImP 1 _) ?oppr0.
Qed.

End GaussianIntegers.
