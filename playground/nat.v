From Coq Require Import ssreflect ssrfun ssrbool.

Lemma card_nat : ~ exists x y : nat, forall z : nat, x = z \/ y = z.
Proof.
unfold not.
intros (x, (y, H)).

assert (H0 := H 0); revert H0.
assert (H1 := H 1); revert H1.
assert (H2 := H 2); revert H2.
case => A; case => B; case => C.
Undo. Undo. Undo. Undo.
elim (H 0); elim (H 1); elim (H 2); intros.

Undo.
elim (H 0); elim (H 1); elim (H 2); intros;
try rewrite H0 in H1; try rewrite H0 in H2; try rewrite H1 in H2; done.
Qed.

