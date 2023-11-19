From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PropLogic.

Print True.

Theorem true_is_true : True.
exact: I.
Qed.

Definition true_is_true' : True := I.

(* just know, that it is inhabited, no need evaluations again *)
Eval compute in true_is_true.

(* evaluates again, uses its body *)
Eval compute in true_is_true'.

Print False.

Check True_ind.

Check False_ind.

Inductive empty : Set := .

Check unit_ind.

Check empty_ind.

Theorem one_eq_two_from_empty: empty -> 1 = 2.
Proof.
exact: empty_ind.
Qed.

Theorem one_eq_two: False -> 1 = 2.
Proof.
exact: False_ind (1 = 2).
Undo.
apply False_ind.
Undo.
case.
Qed.

Theorem imp_trans: forall P Q R: Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
move => P Q R.
move => f1.
move => f2.
move => x.
exact: f2 (f1 x).
Undo.
apply f2.
apply f1.
apply x.
Qed.

Theorem forall_distributivity A (P Q : A -> Prop): 
  (forall x : A, P x -> Q x) -> (forall y : A, P y) -> (forall z : A, Q z).
Proof.
move => X.
move => Y.
move => z.
apply X.
apply Y.
Qed.

Print imp_trans.

Theorem imp_trans' (P Q R : Prop) : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
move => f1 f2.
move: (@imp_trans P Q R) => f.
apply f.
apply f1.
apply f2.
Restart.
move: (@imp_trans P Q R)=> H H1 H2.
apply: H; done.
Restart.
move => H1 H2.
apply: (@imp_trans P Q R)=>//.
Qed.

Module Connectives.

Variables P Q R : Prop.

Locate " /\ ".

Print and.

Goal P -> R -> P /\ R.
apply: conj.
Undo.
constructor 1.
Undo.
(* split = constructor 1 *)
split.
done.
done.
Qed.

Goal P /\ Q -> Q.
case.
done.
Qed.

Locate " \/ ".

Print or.

Goal Q -> P \/ Q \/ R.
move => q.
apply: or_intror. Undo. constructor 2. Undo. right.
apply: or_introl. Undo. constructor 1. Undo. left.
Undo. Undo.
(* by: exact sequence of tactics with "done" tactic at the end *)
by right; left.
Qed.

Goal P \/ Q -> Q \/ P.
case => x.
by right.
by left.
Qed.

Locate "~ ".

Print not.

Theorem absurd: P -> ~P -> Q.
Proof.
move => P nP.
move: (nP P).
case.
Qed.

Theorem contraP: (P -> Q) -> ~Q -> ~P.
Proof.
move => f nQ P.
exact: (nQ (f P)).
Restart.
move => f nQ.
(* goal: B -> C, context: A -> B => goal: A -> C *)
move / f.
exact: nQ.
Qed.

Locate "exists".

Print ex.

Theorem ex_imp_ex A (S T : A -> Prop):
  (exists a : A, S a) -> (forall x: A, S x -> T x) -> (exists b : A, T b).
Proof.
case => a sa f.
exists a.
apply f.
exact: sa.
Restart.
case => a sa f.
by exists a; apply f.
Qed.

(* Exercise *)
Inductive my_ex A (S: A -> Prop) : Prop := my_ex_intro x of S x.
Print ex.
Print my_ex.

Goal forall A (S : A -> Prop), @my_ex A S <-> exists y : A, S y.
Locate "<->".
Print iff.
Proof.
split.
(* my_ex S -> exists y : A, S y *)
case => a sa.
exists a.
apply sa.
(* (exists y : A, S y) -> my_ex S *)
case => a sa.
apply: my_ex_intro sa.
Restart.
split.
(* my_ex S -> exists y : A, S y *)
case.
apply ex_intro.
(* (exists y : A, S y) -> my_ex S *)
case.
apply my_ex_intro.
Qed.

End Connectives.

Require Import Classical_Prop.

Check classic.

Definition peirce_law := forall P Q : Prop, ((P -> Q) -> P) -> P.

Check peirce_law.

(* Exercise *)

Definition implies_to_or := forall P Q : Prop, (P -> Q) -> (~P \/ Q).
Definition excluded_middle := forall P : Prop, P \/ ~P.
Definition double_neg := forall P : Prop, ~(~P) -> P.
Definition de_morgan_not_and_not := forall P Q : Prop, ~(~P /\ ~Q) -> P \/ Q.
Definition peirce := forall P Q : Prop, ((P -> Q) -> P) -> P.

Goal implies_to_or -> excluded_middle.
rewrite / implies_to_or / excluded_middle.
move => implies_to_or P.
Search "comm".
apply or_comm.
apply: implies_to_or (fun x : P => x).
Qed.

Goal excluded_middle -> peirce.
rewrite / excluded_middle / peirce.
move => ex_m P Q.
have: P \/ ~P => //.
case; move => x => //.
have: ~P -> P -> Q => //.
move => f g.
by apply g; apply f.
Qed.

Goal peirce -> double_neg.
rewrite / peirce / double_neg / not.
move => peirce P nnP.
apply (peirce P False).
done.
Qed.


Goal excluded_middle -> double_neg.
rewrite / excluded_middle / double_neg.
apply: forall_distributivity => P.
by case; done.
Qed.

Goal double_neg -> de_morgan_not_and_not.
rewrite / double_neg / de_morgan_not_and_not.
move => double_neg.
move => A B not_and.
apply double_neg.
move: not_and.
apply contra_not.
move => not_or.
apply conj.
move: not_or.
apply contra_not.
by left.
move: not_or.
apply contra_not.
by right.
Qed.


Goal de_morgan_not_and_not -> implies_to_or.
rewrite / de_morgan_not_and_not / implies_to_or.
move => de_morgan.
move => A B f.
apply: de_morgan.
rewrite / not.
case.
move => nna nb.
apply nna.
move / f => //.
Qed.


End PropLogic.