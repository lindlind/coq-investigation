(* SSReflect proof language requires these libraries to be loaded and options to be set. *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import Nat Arith Lia.

(* https://stackoverflow.com/questions/77527395 *)

Module MyProofs.

Lemma L1: forall A B C, A -> (A -> B /\ C) -> C.
Proof.
move => A B C H1 H2.
apply H2 in H1. 
destruct H1 as [H3 Goal].
done.
Qed.

Lemma L2: forall A Q, (forall x, (exists y, x + y = y + x) -> A) -> Q -> A.
Proof.
move => A _ T _.
assert (H: exists y, 2 + y = y + 2) by (exists 0; lia).
apply (T 2) in H.
done.
Qed.

Lemma divides_by_2_by_3_means_by_6 : 
        forall z p q, z = 2 * p -> z = 3 * q -> exists n, z = 6 * n. 
Proof.
move => a b c P Q.
assert (odd_or_even: forall n, (exists k, n = 2 * k) \/ (exists k, n = 2 * k + 1)). {
  induction n.
  - left. exists 0. lia.
  - destruct IHn as [[x H] | [x H]].
    + right; exists x; lia.
    + left; exists (x + 1); lia.
}
move : (odd_or_even c) => H.
destruct H as [[x H] | [x H]].
- exists x; lia.
- lia.
Qed.

End MyProofs.

Module FixedProofs.

Lemma L1: forall A B C, A -> (A -> B /\ C) -> C.
Proof.
(* "/[swap]" to swap the top two elements of the goal;
   "/[apply]" to apply the top element of the goal to the next;
   "-" usually do nothing,
   but here "-" forces next "[]" to be a destruction pattern instead of branching one.
 *)
by move=> A B C /[swap] /[apply] - [].
Qed.

Lemma L2: forall A Q, (forall x, (exists y, x + y = y + x) -> A) -> Q -> A.
Proof.
(* "/(_ 2)" here equals "move => T; move :(T 2)";
   "apply" without arguments takes as argument the top element of the goal.
 *)
by move=> A _ + _ => /(_ 2); apply; exists 0; lia.
Qed.

Lemma divides_by_2_by_3_means_by_6 : 
  forall z p q, z = 2 * p -> z = 3 * q -> exists n, z = 6 * n. 
Proof.
(* Number of indentations equals number of opened goals. *)
move=> a b c.
have odd_or_even : forall n, (exists k, n = 2 * k) \/ (exists k, n = 2 * k + 1).
  elim=> [ | n [[k kP] | [k kP]]]; first by left; exists 0.
    by right; exists k; lia.
  by left; exists (k + 1); lia.
move=> P Q; move: (odd_or_even c)=> [[x H] | [x H]].
  by exists x; lia.
by lia.
Qed.

End FixedProofs.

Module AvoidLiaProofs.

From mathcomp Require Import all_ssreflect.

Lemma divides_by_2_by_3_means_by_6 : 
  forall z p q, z = 2 * p -> z = 3 * q -> exists n, z = 6 * n. 
Proof.
have odd_or_even : forall n, (exists k, n = 2 * k) \/
  (exists k, n = 2 * k + 1).
  elim=> [ | n [[k kP] | [k kP]]]; first by left; exists 0.
    by right; exists k; rewrite kP addn1.
  by left; exists (k + 1); rewrite kP -addnS mulnDr muln1.
move=> a b c + Q; move: (odd_or_even c) => [[x H] | [x H]].
  by exists x; rewrite Q H mulnA; congr (_ * _).
rewrite Q H => /eqP.
have -> : 3 * (2 * x + 1) = 2 * (3 * x + 1) + 1.
  by rewrite 2!mulnDr !mulnA mulnC -addnA; congr (_ + _).
have -> // : forall n m, (2 * n + 1 == 2 * m) = false.
  by move=> n m; rewrite !mul2n addn1 eqn_leq leq_Sdouble ltn_double ltnNge andNb.
Qed.

End AvoidLiaProofs.
