(* SSReflect proof language requires these libraries to be loaded and options to be set. *)
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Goal forall A, A -> A.
Proof.
(* "=>" tactic move terms from goal to context (args from left to right) *)
move => A x.
(* ":" tactic move terms from context to goal (args from right to left) *)
move : A x.
move => A.
(* ": .. => .." can be used for renaming *)
move : A => T.
Abort.


(* SSReflect redefines case, elim, and apply for better sinergy with "=>" and ":" *)

Goal forall m, 0 <= m.
Proof.
(* "elim" takes top assumption of the goal and do induction *)
elim.
Abort.

Goal forall A B, A \/ B -> ~A -> B.
Proof.
move => A B.
(* "case" takes top assumption of the goal and 'destruct' it for each constructor*)
case.
Abort.

(* In general
   "tactic : a b c" pushes the context constants a, b, c as goal variables 
                       before performing the tactic;
   "tactic => a b c" pops the top three goal variables as context constants a, b, c
                       after the tactic has been performed.
 *)

Goal forall m n, n <= m -> m - n + n = m.
Proof.
move => m n leq.
(* Note:
   elim : n m leq.
   is same as
   move : n m leq; elim. 
 *)
elim : n m leq => [|n IHn] m.
Abort.


(* "//" same as "try done." *)
(* "/=" same as "simpl." *)
(* "//=" same as "simpl; try done." *)


