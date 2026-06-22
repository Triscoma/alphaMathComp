From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.


Lemma orbC p q : p || q = q || p.

Proof. by case: p; case: q. Qed.


Lemma Peirce p q : ((p ==> q) ==> p) ==> p.

Proof. by case: p; case: q. Qed.

Lemma bool_gimmics1 a : a != a.-1 -> a != 0.

Proof.
apply: contra.
move => /eqP Ha.
by rewrite Ha.
Qed.


Lemma find_me p q :  ~~ p = q -> p (+) q.

Proof.
move=> Hq.
by rewrite -Hq addbN negb_add eqxx.
Qed.


Lemma view_gimmics1 p a b : p -> (p ==> (a == b.*2)) -> a./2 = b.
Proof.
move=> Hp.
rewrite Hp.
move=> /eqP Hq.
by rewrite Hq doubleK.
Qed.



Lemma bool_gimmics2 p q r : ~~ p && (r == q) -> q ==> (p || r).

Proof.
move=> /andP[Hp Hr].
move: Hp.
move=> /negbTE Hp.
rewrite Hp.
move: Hr.
move=> /eqP Hq.
rewrite Hq.
exact: implybb.
Qed.


Lemma ltn_neqAle m n : (m < n) = (m != n) && (m <= n).
Proof. by rewrite ltnNge leq_eqVlt negb_or -leqNgt eq_sym. Qed.


Lemma mem_cat (T : eqType) (x : T) s1 s2 :
  (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
Proof.

elim: s1 => [//|y s1 IHs /=].
by rewrite !inE /= -orbA -IHs.
Qed.

