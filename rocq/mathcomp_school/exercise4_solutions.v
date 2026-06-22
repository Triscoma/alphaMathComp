From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_boot.
From mathcomp Require Import all_order.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




Lemma cat_take_drop T n (s : seq T) : take n s ++ drop n s = s.
Proof.
by elim: s n => [|x s IHs] [|n] //=; rewrite IHs.
Qed.


Lemma size_take T n (s : seq T) :
  size (take n s) = if n < size s then n else size s.
Proof.
have [le_sn | lt_ns] := leqP (size s) n; first by rewrite take_oversize.
by rewrite size_takel // ltnW.
Qed.


Lemma takel_cat T n (s1 s2 : seq T) :
  n <= size s1 -> take n (s1 ++ s2) = take n s1.
Proof.
move=> Hn; rewrite take_cat ltn_neqAle Hn andbT.
by case: eqP => //= ->; rewrite subnn take0 cats0 take_size.
Qed.


Lemma size_rot T n (s : seq T) : size (rot n s) = size s.
Proof.
by rewrite -[s in RHS](cat_take_drop n) /rot !size_cat addnC.
Qed.


Lemma has_filter (T : eqType) a (s : seq T)  : has a s = (filter a s != [::]).
Proof.
by rewrite -size_eq0 size_filter has_count lt0n.
Qed.


Lemma filter_all T a (s : seq T) : all a (filter a s).
Proof. 
by elim: s => //= x s IHs; case: ifP => //= ->. 
Qed.


Lemma all_filterP T a (s : seq T) :
  reflect (filter a s = s) (all a s).
Proof.
apply: (iffP idP) => [| <-]; last exact: filter_all.
by elim: s => //= x s IHs /andP[-> Hs]; rewrite IHs.
Qed.


Lemma allP (T : eqType) (a : pred T) (s : seq T) :
  reflect (forall x, x \in s -> a x) (all a s).
Proof.
elim: s => [|x s IHs] /=; first by exact: ReflectT.
rewrite andbC; case: IHs => IHs /=.
  apply: (iffP idP) => [Hx y|].
    by rewrite inE => /orP[ /eqP-> // | /IHs ].
  by move=> /(_ x); apply; rewrite inE eqxx.
by apply: ReflectF=> H; apply: IHs => y Hy; apply H; rewrite inE orbC Hy.
Qed.


Lemma maxn_idPl m n : reflect (maxn m n = m) (m >= n).
Proof. by rewrite -subn_eq0 -(eqn_add2l m) addn0 -maxnE; apply: eqP. Qed.


