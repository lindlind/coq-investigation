(* SSReflect proof language requires these libraries to be loaded and options to be set. *)
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma card_nat : ~ exists x y : nat, forall z : nat, x = z \/ y = z.

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

