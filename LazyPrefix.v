Require Import List.
Import ListNotations.

Require Import Regex Chars Groups Tree Semantics.


(* Let's assume we have a function that computes the priority tree *)
(* we don't for now, but this should be proved in the future *)
Parameter exec: regex -> input -> option leaf.

(* Axiomatizing that this function is correct *)
Axiom exec_tree:
  forall r i ol,
    exec r i = ol <->
      (exists tree, is_tree r [] i tree /\
                 first_branch tree = ol).

(* Search for a match for a regex, at a given position indicated by the current state of the input (next & pref) *)
(* then search from the next position if no match is found *)
Fixpoint search_from (r:regex) (next:string) (pref:string): option leaf :=
  match (exec r (Input next pref)) with
  | Some leaf => Some leaf
  | None =>
      match next with
      | [] => None
      | char::next' =>
          search_from r next' (char::pref)
      end
  end.

(* the string-quadratic algorithm described in RegExpBuiltinExec *)
Definition BuiltinExec (r:regex) (i:input) : option leaf :=
  match i with
  | Input next pref =>
      search_from r next pref
  end.

(* TODO: for now, this simple algorithm does not set the capture group 0 *)
(* I expect that to support this, we should add the hypothesis that r itself does not contain a capture group 0 *)


(* adding all*? as a prefix to r*)
(* using all instead of dot, since the behavior of dot depends on a flag *)
Definition lazy_prefix (r:regex) : regex :=
  Sequence (Star false (Character all)) r.


Theorem lazy_prefix_correct:
  forall r i,
    BuiltinExec r i = exec (lazy_prefix r) i.
Proof.
Admitted.
