(* SSReflect proof language requires these libraries to be loaded and options to be set. *)
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import Nat Arith Lia.

Theorem card_nat : ~ exists x y : nat, forall z : nat, x = z \/ y = z.

(* attempt 1 *)
Proof.
unfold not.
intros (x, (y, H)).
assert (H0 := H 0); revert H0.
assert (H1 := H 1); revert H1.
assert (H2 := H 2); revert H2.
case => A; case => B; case => C.

(* attempt 2, using elim *)
Restart.
unfold not.
intros (x, (y, H)).
elim (H 0); elim (H 1); elim (H 2); intros;
try rewrite H0 in H1; try rewrite H0 in H2; try rewrite H1 in H2; done.

(* attempt 3, using ssreflect and repeat *)
Restart.
move => [x [y H]].
move: (H 0) (H 1) (H 2).
repeat (case => //; move => ->).
Qed.


Lemma three_consecutive_someone_divides_by_2 : 
        forall x, exists y, x = 2 * y \/ x + 1 = 2 * y \/ x + 2 = 2 * y. 
Proof.
move => z; induction z.
- exists 0. lia.
- destruct IHz.
  move : H; case; [ | case]; move => H.
  + exists (x + 1); lia.
  + exists x; lia.
  + exists x; lia.
Qed.

Lemma three_consecutive_someone_divides_by_3 : 
        forall x, exists y, x = 3 * y \/ x + 1 = 3 * y \/ x + 2 = 3 * y. 
Proof.
move => z; induction z.
- exists 0. lia.
- destruct IHz.
  move : H; case; [ | case]; move => H.
  + exists (x + 1); lia.
  + exists x; lia.
  + exists x; lia.
Qed.

Lemma divides_by_2_by_3_means_by_6 : 
        forall z p q, z = 2 * p -> z = 3 * q -> exists n, z = 6 * n. 
Proof.
move => a b c P Q.
Search "odd_even".

assert (either_odd_or_even: forall n, (exists k, n = 2 * k) \/ (exists k, n = 2 * k + 1)). 
{
induction n.
constructor. exists 0. lia.
case : IHn => H; destruct H. 
constructor 2. exists x. lia.
constructor 1. exists (x + 1). lia.
}

case : (either_odd_or_even c) => H.
destruct H.
exists x.
lia.

destruct H.
rewrite H in Q.
rewrite Q in P.
move : (Mult.odd_even_lem_stt (3* x + 2) b); move => T.
lia.
Qed.

Theorem three_consecutive_mult_divides_by_6 : forall x, exists y, x * (x + 1) * (x + 2) = 6 * y.
Proof.
move => x.
move : (three_consecutive_someone_divides_by_2 x) (three_consecutive_someone_divides_by_3 x).
move => [a Ha] [b Hb].

move : Ha; case; [ | case]; move => Ha.
all: move : Hb; case; [ | case]; move => Hb.
all: try rewrite Ha Hb; try rewrite Hb Ha.

all: cycle 1.
exists (a * b * (2 * a + 2)); lia.
exists (a * b * (2 * a + 1)); lia.
exists (a * b * (3 * b + 2)); lia.
all: cycle 1.
exists (a * b * x); lia.
exists (a * b * (3 * b + 1)); lia.
exists (a * b * x); lia.
all: cycle 1.

all: destruct (divides_by_2_by_3_means_by_6 Ha Hb).
all: rewrite H; rename x0 into w.


exists (w * (6 * w + 1) * (6 * w + 2)); lia.
exists (w * x * (x + 2)); lia.
exists (w * x * (x + 1)); lia.
Qed.
