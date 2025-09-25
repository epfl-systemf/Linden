(** * An example Backtracking Tree  *)
(* Figure 2 of the paper *)

Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics PikeVMSeen.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import FunctionalUtils FunctionalSemantics.

Section TreeExample.
  Context (rer: RegExpRecord).


(* we assume the existence of three characters *)
Parameter a : Character.type.
Parameter b : Character.type.
Parameter c : Character.type.

Example a_char : regex := Regex.Character (CdSingle a).
Example b_char : regex := Regex.Character (CdSingle b).
Example c_char : regex := Regex.Character (CdSingle c).


Lemma charmatch_same:
  forall c, char_match rer c (CdSingle c) = true.
Proof. unfold char_match, char_match'. intros. apply EqDec.reflb. Qed.
(* we assume that these characters are distincts (b does not match c) *)
Axiom charmatch_bc:
  char_match rer b (CdSingle c) = false.

Example fig2_regex: regex :=
  Sequence
    (Disjunction a_char
       (Disjunction
          (Sequence a_char (Group 1 b_char))
          a_char))
    (Sequence b_char c_char).

Example fig2_input: input := Input [a;b;b;c] []. 

Example fig2_tree: tree :=
  Choice
    (Read a (Read b Mismatch))
    (Choice
       (Read a (GroupAction (Open 1) (Read b (GroupAction (Close 1) (Read b (Read c Match))))))
       (Read a (Read b Mismatch))).

Theorem fig2_is_tree:
  is_tree rer [Areg fig2_regex] fig2_input GroupMap.empty forward fig2_tree.
Proof.
  unfold fig2_input.
  repeat (econstructor; simpl; try rewrite charmatch_same).
  2: { rewrite charmatch_bc; auto. }
  rewrite charmatch_bc. auto.
Qed.

End TreeExample.
