Require Import List Lia.
Import ListNotations.

Require Import Chars.
Require Import Groups.

(** * Regex Syntax  *)
Inductive regex : Type :=
| Epsilon 
| Character (cd : char_descr)   (* includes character classes and dot *)
| Disjunction (r1 r2 : regex) 
| Sequence (r1 r2 : regex)
| Star (r1: regex)
| Group (id : group_id) (r : regex).

Definition regex_eq_dec : forall (x y : regex), { x = y } + { x <> y }.
Proof.
  decide equality. apply char_descr_eq_dec. apply PeanoNat.Nat.eq_dec. 
Defined.

(** * Group Manipulation  *)

(* getting all groups defined in a regex for the reset *)
Fixpoint def_groups (r:regex) : list group_id :=
  match r with
  | Epsilon | Character _  => []
  | Sequence r1 r2 | Disjunction r1 r2 => def_groups r1 ++ def_groups r2
  | Star r1 => def_groups r1
  | Group id r1 => id::(def_groups r1)  
  end.
