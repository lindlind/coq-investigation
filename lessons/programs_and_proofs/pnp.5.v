From mathcomp Require Import ssreflect ssrnat ssrbool eqtype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From mathcomp Require Import prime.

(* type "true" doesn't make sense *)
(* type "true = true" makes sense *)
(* coercion is_true add "= true" implicitly so type "true" becomes type "true = true" *)

Coercion is_true (b: bool) := b = true.

(* now we can use predicates in types, with meaning meaning p x = true *)
Goal prime 41. Proof. done. Qed.
Goal ~ prime 42. Proof. done. Qed.

Definition prime_spec n m : Prop := m = (if prime n then 1 else 2).

Definition discr_prime n := (if prime n then 0 else 1) + 1.

Lemma discr_prime_spec : forall n, prime_spec n (discr_prime n).
Proof.
move => n.
rewrite /discr_prime /prime_spec.
by case: (prime n).
Qed.

Section Reflects.

Variables do_check1 do_check2 : nat -> bool.
Hypothesis H: forall n, do_check2 n -> prime n.

Lemma check_prime n : (do_check1 n) && (do_check2 n) -> prime n.
(* case doesn't work since bool &&, not Prop /\. *)
try case.
Abort.

Print Bool.reflect.

Lemma trueP: reflect True true.
Proof. constructor. done. Qed.

Lemma falseP: reflect False false.
Proof. constructor. done. Qed.

Lemma andP (b1 b2 : bool): reflect (b1 /\ b2) (b1 && b2). 
Proof.
case: b1; case: b2.
all: constructor.
done.
all: case.
all: done.
Qed.

(* now we can use andP as reflection from /\ to && *)
Lemma check_prime n : (do_check1 n) && (do_check2 n) -> prime n.
Proof.
case: andP.
case => _.
move /H.
done.
move => a b.
done.
Restart.
case: andP => //.
by case => _ /H.
Restart.
by case /andP => _ /H.
Qed.

Print check_prime.
Check elimTF.

Definition andb_orb b1 b2: b1 && b2 -> b1 || b2.
Proof.
case /andP => h1 h2.
apply /orP.
left; done.
Qed.

End Reflects.

Definition XOR (P Q: Prop) := (P \/ Q) /\ ~(P /\ Q).

Definition xorb b := if b then negb else fun x => x.

Lemma xorP_gen (b1 b2 : bool)(P1 P2: Prop):
  reflect P1 b1 -> reflect P2 b2 -> reflect (XOR P1 P2) (xorb b1 b2).
Proof.
rewrite /XOR.
case => p1; case => p2; constructor.
by case => _ /(_ (conj p1 p2)).
by constructor; [left  | case].
by constructor; [right | case].
by case; case.
Qed.

Lemma xorP (b1 b2 : bool): reflect (XOR b1 b2) (xorb b1 b2).
Proof.
apply xorP_gen; case b1; case b2; by constructor.
Qed.


Definition XOR' (P Q: Prop) := (P /\ ~Q) \/ (~P /\ Q).

Lemma XORequiv P Q: XOR P Q <-> XOR' P Q.
Proof.
rewrite /XOR /XOR'.
split.
- case; case => [p | q] f.
  by left;  constructor => // q; apply f.
  by right; constructor => // p; apply f.
- case; case => p q.
  by constructor; [left  | case].
  by constructor; [right | case].
Qed.

Lemma xorP' (b1 b2 : bool): reflect (XOR' b1 b2) (xorb b1 b2).
Proof.
case H: (xorb b1 b2).
all: constructor.
all: apply /XORequiv. 
all: apply /xorP.
all: rewrite H.
all: done.
Qed.


Definition foo (x y : nat) := if x == y then 1 else 0.

Goal forall x y, x = y -> foo x y = 1.
Proof.
rewrite /foo.
move => x y.
move /eqP.
move => ->.
done.
Qed.


Definition uniqueBothArgs (A: Type) (P: A -> A -> Prop) := exists x, unique (fun x => exists y, unique (P x) y) x.
Definition unique1stArg (A: Type) (P: A -> A -> Prop) := exists x, unique (fun x => exists y, P x y) x.
Definition unique2ndArg (A: Type) (P: A -> A -> Prop) := exists x, exists y, unique (P x) y.

Lemma ExistsUniqueMeansExists: forall A (P: A -> Prop), (exists x, unique P x) -> (exists x, P x).
Proof.
move => A P H.
destruct H as [y H].
exists y.
apply H.
Qed.

Theorem ExistsUnique1 : forall (A: Type) (P: A -> A -> Prop), unique1stArg P /\ unique2ndArg P -> uniqueBothArgs P.
Proof.
move => A P.
case => H1 H2.
destruct H1 as [x1 [_ noOtherX1]].
destruct H2 as [x2 [y2 [H noOtherY2]]].

exists x2.
split.
by exists y2.


assert (Hx: exists y : A, P x2 y) by (exists y2; done).
apply (noOtherX1 x2) in Hx.

rewrite -Hx.

move => x H0.
apply ExistsUniqueMeansExists in H0.
auto.
Qed.


From Coq Require Import Nat Arith Lia.

Lemma Counterexample: forall A (P: A -> Prop), (exists (y: A), ~ P y) -> (~ forall (x: A), P x).
Proof.
move => A P [y S] T.
exact (S (T y)).
Qed.

Theorem ExistsUnique2 : ~ (forall (A: Type) (P: A -> A -> Prop), uniqueBothArgs P -> unique1stArg P /\ unique2ndArg P).
Proof.
apply Counterexample.
exists nat.
apply Counterexample.
exists (fun (x y : nat) => (0 = x) <-> (0 = y)).
cut (uniqueBothArgs (fun x y : nat => (0 = x) <-> (0 = y))).
move => H1 H2.
apply H2 in H1; clear H2.
destruct H1 as [A B].
destruct A.
destruct H.
move : (H0 0) => H1.
move : (H0 1) => H2.
assert (T1: exists y : nat, (0 = 0) <-> (0 = y)) by (exists 0; lia).
assert (T2: exists y : nat, (0 = 1) <-> (0 = y)) by (exists 1; lia).
apply H1 in T1.
apply H2 in T2.
lia.

exists 0.
split.
exists 0.
split.
+ done.
+ move => x H.
  rewrite -H.
  done.
move => x [y H].
destruct H.
induction y; induction x; try auto.
+ assert (H2: (0 = x.+1) <-> (0 = x.+1)) by lia.
  lia.
+ assert (H2: (0 = x.+1) <-> (0 = y.+2)) by lia.
  apply (H0 (y.+2)) in H2.
  lia.
Qed.


