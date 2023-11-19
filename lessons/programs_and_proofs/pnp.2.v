From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Check tt.
Print tt.
Check unit.
Print unit.

Check Set.
Check Type.

(*
Print Set.  # Syntax error
*)

Print true.
Print false.
Print bool.

Inductive empty : Set := .
Check empty.
Print empty.

Definition negate b :=
  match b with
  | true => false
  | false => true
end.
Print negate.

Print nat.
Print plus.
Print Nat.add.
Eval compute in Nat.add 2 1.


Print unit.

(* 
Definition of induction:
  for all P : unit -> Type,
    if   (P tt) 
    then (for all u : unit, P u)
"P tt" is base of induction.
Here is no step of induction.
"for all u : unit, P u" is the result of induction.
*)
Print unit_rect.

(*
The same for only Type: Set.
*)
Print unit_rec.

(*
The same for only Type: Prop.
*)
Print unit_ind.

(* example *)
Definition is_tt (x:unit) := unit_rect (fun _ => bool) true x.
Print is_tt.
Eval compute in is_tt tt.


Print nat.

(* 
Definition of induction:

  for all P : nat -> Type,
    if   (P 0)
    and  (for all n : nat, if P n then P (S n))
    then (for all n : nat, P n)
*)
Print nat_rect.

(*
The same for only Type: Set.
*)
Print nat_rec.

(*
The same for only Type: Prop.
*)
Print nat_ind.

(* examples *)
Definition is_zero (x:nat) := nat_rect (fun _ => bool) true (fun _ _ => false) x.
Print is_zero.
Eval compute in is_zero 0.
Eval compute in is_zero 1.
Eval compute in is_zero 2.

Definition add_two (x:nat) := nat_rect (fun _ => nat) 2 (fun _ b => (S b)) x.
Print add_two.
Eval compute in add_two 0.
Eval compute in add_two 1.
Eval compute in add_two 2.


Inductive tree : Set := L : nat -> tree | V : tree -> nat -> tree -> tree.

Definition my_tree := V (L 5) 10 (V (L 1) 2 (L 3)).

Print tree_rect.

Definition tree_size := tree_rect (fun n => 1) (fun _ a n _ b => S (a + b)).
Eval compute in tree_size my_tree.

Definition tree_size_explicitly := @tree_rect (fun _ => nat) (fun n => 1) (fun _ a n _ b => S (a + b)).
Eval compute in tree_size_explicitly my_tree.

Definition tree_sum := tree_rect (fun n => n) (fun _ a n _ b => n + a + b).
Eval compute in tree_sum my_tree.

Print nat.
Check O.
Check S.

Print prod.
(* new notation *)
Inductive my_prod (A B : Type) : Type := my_pair of A & B.
Check pair.
Check my_pair.
Check fst.
Print fst.
Check snd.

Check sum.
Check inl.
Check inr.

Print list.
Check nil.
Check cons.

From mathcomp Require Import seq.
Print seq.
Check list_rect.
(* Exercise 2.1 *)
Fixpoint alternate (A : Type) (a : seq A) (b : seq A) := 
  match a with
  | nil => b
  | ha :: ta => ha :: (
    match b with
    | nil => ta
    | hb :: tb => hb :: alternate ta tb
    end
  )
  end.
Eval compute in alternate [:: 1;2;3] [:: 4].

Search tree.
Search "_ + _".
Locate tree.
Locate "_ + _".