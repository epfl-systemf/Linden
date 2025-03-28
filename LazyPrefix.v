Require Import List.
Import ListNotations.

Require Import Regex Chars Groups Tree Semantics.
Require String.


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

Lemma lazy_prefix_end:
  forall r pref tree_anch,
  is_tree r [] (Input [] pref) tree_anch ->
  is_tree (lazy_prefix r) [] (Input [] pref) (Choice tree_anch (GroupAction (Reset []) Mismatch)).
Proof.
  intros r pref tree_anch Hanch.
  constructor.
  eapply tree_star.
  - simpl. reflexivity.
  - apply tree_char_fail. simpl. reflexivity.
  - apply tree_pop_reg. apply Hanch.
  - simpl. reflexivity.
Qed.

Lemma cons_different {A}: forall (x: A) (l: list A), l <> x::l.
Proof.
  intros x l.
  induction l as [ | y q IHq].
  - discriminate.
  - intro H. inversion H. contradiction.
Qed.

Lemma lazy_prefix_cons:
  forall r pref x next tree_anch tree_lazy_next,
  is_tree r [] (Input (x::next) pref) tree_anch ->
  is_tree (lazy_prefix r) [] (Input next (x::pref)) tree_lazy_next ->
  is_tree (lazy_prefix r) [] (Input (x::next) pref)
    (Choice tree_anch (GroupAction (Reset []) (Read x (CheckPass (x::next) tree_lazy_next)))).
Proof.
  intros r pref x next tree_anch tree_lazy_next Hanch Hnext.
  constructor.
  eapply tree_star.
  - simpl. reflexivity.
  - eapply tree_char.
    + simpl. rewrite all_match. reflexivity.
    + apply tree_pop_check.
      1: {
        simpl. apply cons_different.
      }
      apply tree_pop_reg.
      inversion Hnext. apply CONT.
  - apply tree_pop_reg. apply Hanch.
  - simpl. reflexivity.
Qed.

Theorem lazy_prefix_correct:
  forall r i,
    BuiltinExec r i = exec (lazy_prefix r) i.
Proof.
  intros r i.
  destruct i as [next pref].
  revert pref.
  induction next as [ | x next IHnext].
  - intro pref. simpl.
    symmetry.
    rewrite exec_tree.
    remember (exec r (Input [] pref)) as ol.
    symmetry in Heqol.
    rewrite exec_tree in Heqol.
    destruct Heqol as [tree_anch [Htree Hbranch]].
    eexists; split.
    + apply lazy_prefix_end. apply Htree.
    + replace (match ol with | Some leaf => _ | None => None end) with ol.
      2: {
        destruct ol; reflexivity.
      }
      unfold first_branch in *. simpl.
      rewrite seqop_none. assumption.
  - 
Admitted.
