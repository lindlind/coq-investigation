From mathcomp Require Import ssreflect ssrnat ssrbool eqtype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Locate "_ = _".

Inductive my_eq (A : Type) (x : A) : A -> Prop
  := my_eq_refl : my_eq x x.

Notation "x === y" := (my_eq x y) (at level 70).

Lemma my_eq_sym A (x y: A) : x === y -> y === x.
case.
done.
Qed.

Lemma my_eq_Leibniz A (x y: A) (P: A -> Prop) : x === y -> P x <-> P y.
case.
done.
Qed.

Lemma disaster' : ~ 1 === 2.
move => feq.
pose D x := if x is 1 then False else True.
have: D 2 => //.
case: feq.
move => /=.
done.
Qed.

Lemma disaster : ~ 2 = 1.
done.
Qed.


Section Rewriting.

Definition double {A} (f : A -> A) (x : A) 
              := f (f x).
Fixpoint nat_iter (n : nat) {A} (f : A -> A) (x : A) : A 
              := if n is S n' then f (nat_iter n' f x) else x.

Theorem double2 A (x : A) f t
              : t = double f x -> double f t = nat_iter 4 f x.
Proof.
move => P.
rewrite P.
rewrite / double / nat_iter.
done.
Restart.
move => ->.
rewrite / double.
done.
Qed.

Definition f x y := x + y.
Goal forall x y, x + y + (y + x) = f y x + f y x.
move => x y.
rewrite /f.
(* use eq_Leibniz *)
congr (_ + _).
Print ssrfun.commutative.
Print addnC.
rewrite addnC.
Undo.
(* r-pattern, regex pattern *)
rewrite [x + _] addnC.
Undo.
rewrite [y + _] addnC.
done.
Qed.

Lemma addnCA: forall m n p, m + (n + p) = n + (m + p).
move => m n.
elim: m => [ | m H] p.
(* ! means as many as possible, at least once
   ? means as many as possible, maybe zero times *)
rewrite ! add0n.
done.
rewrite ! addSnnS.
Check addnS.
(* nothing (or ->) means rewriting from left side of = to right
         - (or <-) means rewriting from right side of = to left *)
rewrite - addnS.
done.
Restart.
by move => m n; elim: m => [ |  m H] p; rewrite ?add0n ?addSnnS -?addnS.
Qed.

Lemma addnC: forall m n, m + n = n + m.
Proof.
move => m n.
(* [x] specify which var equality applies to
   {1} specify which occurence of var [x] equality applies to *) 
rewrite - {1} [n] addn0.
rewrite addnCA.
rewrite addn0.
done.
Qed.

Lemma huh n m: ~ (m <= n /\ m > n).
Proof.
case.
elim: m n.
done.
move => x H y.
elim y.
done.
move => z _.
exact: H z.
Restart.
case.
elim: m n => [|x H y] //.
elim: y => [|z _] //.
apply H.
Restart.
case.
elim: m n => [| x H] [|z] //.
apply H.
Qed.

Definition maxn m n := if m < n then n else m.
Lemma max_is_max m n: n <= maxn m n /\ m <= maxn m n.
Proof.
case H: (m < n); rewrite /maxn H.
Check ltnW.
apply ltnW in H => //.
case H1: (n <= m) => //.
rewrite ltnNge @ H1 in H => //.
Qed.

(* Defining custom rewriting rule *)
Inductive leq_xor_gtn m n : bool -> bool -> Set :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n true false
  | GtnNotLeq of n <  m : leq_xor_gtn m n false true.
Print leq_xor_gtn.

Lemma leqP m n : leq_xor_gtn m n (m <= n) (n < m).
Proof.
Print "~~".
Check ltnNge.
rewrite ltnNge.
case H: (m <= n).
constructor.
done.
constructor.
rewrite ltnNge H.
done.
Qed.

Lemma huh' n m: ~ (m <= n /\ m > n).
Proof.
move /andP.
case leqP => H.
done. done.
Restart.
case leqP => H.
case. done.
case. done.
Qed.

Lemma max_is_max' m n: n <= maxn m n /\ m <= maxn m n.
Proof.
rewrite /maxn.
case leqP => H.
done.
rewrite [m <= _] ltnW => //.
Undo.
apply ltnW in H => //.
Qed.


Lemma max_l m n: n <= m -> maxn m n = m.
Proof.
rewrite /maxn.
case leqP => H.
done.
done.
Qed.

Lemma succ_max_distr n m : (maxn n m).+1 = maxn (n.+1) (m.+1).
Proof.
rewrite /maxn.
case: (leqP m n) => H1; case: (leqP m.+1 n.+1) => H2.
Undo.
case: (leqP m n) (leqP m.+1 n.+1) => [H1 | H1] [H2 | H2].
done.
apply: False_ind (huh (conj H1 H2)).
apply: False_ind (huh (conj H1 H2)).
done.
Qed.

Lemma plus_max_distr_l m n p: maxn (p + n) (p + m) = p + maxn n m.
Proof.
have add_leq: forall a b c, a <= b -> c + a <= c + b.
by move => a b c; rewrite (leq_add2l c a b).
have add_lt: forall a b c, a < b -> c + a < c + b.
by move => a b c; rewrite - addnS; apply add_leq.
rewrite /maxn.
case (leqP m n) => H1; case (leqP (p + m) (p + n)) => H2.
done.
apply (add_leq m n p) in H1; apply: False_ind (huh (conj H1 H2)).
apply (add_lt n m p) in H1; apply: False_ind (huh (conj H1 H2)).
done.
Qed.


Inductive nat_rels m n : bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n : nat_rels m n true false false
  | CompareNatEq of m = n : nat_rels m n false true false
  | CompareNatGt of m > n : nat_rels m n false false true.

Lemma leq_lt_eq : forall m n, m <= n -> m < n \/ m = n.
Proof.
move => n m.
elim: m n => [| x H] [| z];
  (try by left); 
  (try by right).
move /ltnSE.
move /H.
case => H2.
left => //.
right; rewrite H2 => //.
Qed.

Lemma leq_leq_eq : forall m n, m <= n -> n <= m -> m = n.
Proof.
move => m n.
move / leq_lt_eq.
case => //.
move => H1 H2.
apply: False_ind (huh (conj H2 H1)).
Qed.

Lemma lt_not_lt: forall m n, m < n -> ~ n < m.
move => m n.
move / ltnW.
move => H1 H2.
apply: huh (conj H1 H2).
Qed.

Lemma natrelP m n : nat_rels m n (m < n) (m == n) (m > n).
Proof.
rewrite eqn_leq.
case (leqP m n) => H1; case (leqP n m) => H2; 
  try constructor; 
  try apply H1; 
  try apply H2.
apply: leq_leq_eq => //.
apply: False_rec (lt_not_lt H2 H1).
Qed.

Definition minn m n := if m < n then m else n.

Lemma addn_min_max m n : minn m n + maxn m n = m + n.
rewrite /maxn /minn.
case leqP => H //.
apply addnC.
Qed.

End Rewriting.