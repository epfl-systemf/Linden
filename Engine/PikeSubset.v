Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics.
From Warblre Require Import Numeric Base.

(* The subset of regexes supported by the PikeVM engine *)

Context `{characterClass: Character.class}.


(** * PikeVM supported subset  *)

Inductive pike_regex : regex -> Prop :=
| pike_eps:
  pike_regex Epsilon
| pike_char:
  forall cd, pike_regex (Regex.Character cd)
| pike_disj:
  forall r1 r2,
    pike_regex r1 ->
    pike_regex r2 ->
    pike_regex (Disjunction r1 r2)
| pike_seq:
  forall r1 r2,
    pike_regex r1 ->
    pike_regex r2 ->
    pike_regex (Sequence r1 r2)
| pike_star:
  forall r1 b,
    pike_regex r1 ->
    pike_regex (Quantified b 0 NoI.Inf r1)
| pike_group:
  forall g r1,
    pike_regex r1 ->
    pike_regex (Group g r1).

(* lifting to actions *)
Inductive pike_action: action -> Prop :=
| pike_areg:
  forall r1,
    pike_regex r1 ->
    pike_action (Areg r1)
| pike_aclose: forall g, pike_action (Aclose g)
| pike_acheck: forall s, pike_action (Acheck s).

(* lifting to actions lists *)
Inductive pike_actions: actions -> Prop :=
| pike_nil: pike_actions []
| pike_cons: forall a l,
    pike_action a ->
    pike_actions l ->
    pike_actions (a::l).

(* only a subset of trees can correspond to a pike regex *)
Inductive pike_subtree: tree -> Prop :=
| pike_mismatch: pike_subtree Mismatch
| pike_match: pike_subtree Match
| pike_choice: forall t1 t2,
    pike_subtree t1 -> pike_subtree t2 ->
    pike_subtree (Choice t1 t2)
| pike_read: forall cd t1,
    pike_subtree t1 ->
    pike_subtree (Read cd t1)
| pike_progress: forall t1,
    pike_subtree t1 ->
    pike_subtree (Progress t1)
| pike_groupaction: forall ga t1,
    pike_subtree t1 ->
    pike_subtree (GroupAction ga t1).

(* used for the lists of trees and gm manipulated by the PikeTree algorithm *)
Definition pike_list (l: list (tree * group_map)) : Prop :=
  (forall t gm, In (t, gm) l -> pike_subtree t).


(** * Subset Properties  *)

Lemma pike_list_cons:
  forall t gm l,
    pike_list ((t,gm)::l) <-> pike_subtree t /\ pike_list l.
Proof.
  intros t gm l. unfold pike_list. split; try split; intros. 
  - eapply H; eauto. left. eauto.
  - eapply H; eauto. right. eauto.
  - destruct H. inversion H0; subst.
    + inversion H2. subst. auto.
    + eapply H1. eauto.
Qed.

Lemma pike_list_app:
  forall l1 l2,
    pike_list (l1 ++ l2) <-> pike_list l1 /\ pike_list l2.
Proof.
  intros l1 l2. unfold pike_list. split; try split; intros.
  - eapply H. rewrite in_app_iff. left. eauto.
  - eapply H. rewrite in_app_iff. right. eauto.
  - destruct H. rewrite in_app_iff in H0. destruct H0.
    + eapply H; eauto.
    + eapply H1; eauto.
Qed.

Lemma pike_list_empty:
  pike_list [].
Proof.
  unfold pike_list. intros. inversion H.
Qed.

Lemma pike_list_single:
  forall t gm, pike_subtree t -> pike_list [(t,gm)].
Proof.
  unfold pike_list. intros t gm H t0 gm0 H0. inversion H0; inversion H1; subst; auto.
Qed.

Lemma pike_list_twice:
  forall t1 t2 gm1 gm2, pike_subtree t1 -> pike_subtree t2 -> pike_list [(t1,gm1);(t2,gm2)].
Proof.
  unfold pike_list. intros t1 t2 gm1 gm2 H H0 t gm H1.
  inversion H1; inversion H2; try inversion H3; subst; auto.
Qed.




(* inverting evidence of belonging to the subset *)
Ltac invert_subset := 
  match goal with
  | [ H : pike_list ((_,_)::_) |- _ ] => apply pike_list_cons in H; destruct H
  | [ H : pike_list (?tgm::_) |- _ ] => destruct ?tgm
  | [ H : pike_list (_ ++ _) |- _ ] => apply pike_list_app in H; destruct H
    
  | [ H : pike_subtree (Choice _ _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (Read _ _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (Progress _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (GroupAction _ _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (ReadBackRef _ _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (AnchorPass _ _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (LK _ _ _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (LKFail _ _) |- _ ] => inversion H; clear H                                       

  | [ H : pike_actions (_ :: _) |- _ ] => inversion H; clear H

  | [ H : pike_action (Areg _) |- _ ] => inversion H; clear H
                                                           
  | [ H : pike_regex (Regex.Character _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Disjunction _ _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Sequence _ _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Quantified _ _ _ _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Group _ _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Lookaround _ _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Anchor _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Backreference _) |- _ ] => inversion H; clear H

  | [ |- pike_list (_ ++ _) ] => apply pike_list_app; split
  | [ |- pike_list (_ :: _) ] => apply pike_list_cons; split
  | [ |- pike_list [] ] => apply pike_list_empty
  | [ |- pike_list [(_,_)] ] => apply pike_list_single
  | [ |- pike_list [(_,_);(_,_)] ] => apply pike_list_twice
  | [ |- pike_list [?tgm] ] => destruct ?tgm

  end.

Ltac pike_subset :=
  repeat (invert_subset; subst); repeat (constructor; auto); auto.

Ltac in_subset :=
  match goal with
  | [ H : ~ pike_regex (Epsilon) |- _ ] => try solve[exfalso; apply H; pike_subset]
  | [ H : ~ pike_regex (Regex.Character _) |- _ ] => try solve[exfalso; apply H; pike_subset]
  | [ H : ~ pike_regex (Disjunction _ _) |- _ ] => try solve[exfalso; apply H; pike_subset]
  | [ H : ~ pike_regex (Sequence _ _) |- _ ] => try solve[exfalso; apply H; pike_subset]
  | [ H : ~ pike_regex (Quantified _ _ _ _) |- _ ] => try solve[exfalso; apply H; pike_subset]
  | [ H : ~ pike_regex (Group _ _) |- _ ] => try solve[exfalso; apply H; pike_subset]
  end.

(* prove that one can only construct pike subtrees from pike regexes *)
Lemma pike_actions_pike_tree:
  forall cont inp gm dir t,
    pike_actions cont ->
    is_tree cont inp gm dir t ->
    pike_subtree t.
Proof.
  intros cont inp gm dir t PIKE ISTREE.
  induction ISTREE; try apply IHISTREE; pike_subset; auto.
  - apply IHISTREE1. pike_subset. 
  - apply IHISTREE2. pike_subset.
  - destruct dir; simpl; pike_subset. 
  - destruct greedy.
    + pike_subset. apply IHISTREE1. pike_subset. destruct plus; inversion H3. constructor. auto.
    + pike_subset. apply IHISTREE1. pike_subset. destruct plus; inversion H3. constructor. auto.
  - apply IHISTREE. pike_subset.
Qed.
