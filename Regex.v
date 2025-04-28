Require Import List Lia.
Import ListNotations.

From Linden Require Import Chars.
From Linden Require Import Groups.
From Warblre Require Import Base.

(* The subset of JavaScript regexes supported by this development. *)
(* The semantics come from JavaScript:
   for instance, the star termination criteria is not the same as in other languages
   and capture groups are reset at each iteration *)

(** * Regex Syntax  *)
Inductive regex : Type :=
| Epsilon 
| Character (cd : char_descr)   (* includes character classes and dot *)
| Disjunction (r1 r2 : regex) 
| Sequence (r1 r2 : regex)
| Quantified (greedy:bool) (min: nat) (plus: non_neg_integer_or_inf) (r1: regex)
| Group (id : group_id) (r : regex).

Definition regex_eq_dec : forall (x y : regex), { x = y } + { x <> y }.
Proof.
  decide equality.
  - apply char_descr_eq_dec.
  - decide equality. apply PeanoNat.Nat.eq_dec.
  - apply PeanoNat.Nat.eq_dec.
  - destruct greedy; destruct greedy0; auto. right. lia.
  - apply PeanoNat.Nat.eq_dec. 
Defined.

(** * Group Manipulation  *)

(* getting all groups defined in a regex for the reset *)
Fixpoint def_groups (r:regex) : list group_id :=
  match r with
  | Epsilon | Character _  => []
  | Sequence r1 r2 | Disjunction r1 r2 => def_groups r1 ++ def_groups r2
  | Quantified _ _ _ r1 => def_groups r1
  | Group id r1 => id::(def_groups r1)  
  end.
