(** * Termination of the PikeTree and PïkeVM algorithm *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeTree PikeVM.
From Linden Require Import PikeTreeSeen PikeVMSeen.
From Linden Require Import Correctness.

(** * Productivity of the PikeTree Algorithm  *)
(* we prove that the PikeTree algorithm never gets stuck *)

Theorem piketree_productivity:
  forall pts1, (exists res, pts1 = PTSS_final res) \/ (exists pts2, pike_tree_seen_step pts1 pts2).
Proof.
  intros pts1. destruct pts1; [right|left; eauto].
  destruct active as [|[t gm] active].
  - destruct blocked as [|tgm blocked]; repeat econstructor.
  - destruct (inseen seen t) eqn:SEEN.
    { repeat econstructor; auto. }
    destruct (tree_bfs_step t gm (idx inp)) eqn:STEP;
      try solve[eexists; econstructor; eauto].
Qed.

(** * Termination of the PikeTree Algorithm  *)
(* We define a measure, based on the total sizes of all trees handled by the algorithm. *)
(* This measure strictly decreases at each step, meaning that the algorithm eventually reaches a final state *)

(* The measure cannot just sum the sizes of the trees inside active and blocked.
   Because the nextchar rule might then not strictly decrease the measure.
   Since the rule is only possible when the blocked list is non-empty, we add a bonus of 1 for any state where the blocked list is non-empty, ensuring that the measure decreases for the rule nextchar.
 *)

Definition bonus (l:list (tree * group_map)) :nat :=
  match l with
  | [] => 0
  | _ => 1
  end.

Lemma bonus_add:
  forall l tgm,
    bonus (l ++ [(tgm)]) = 1.
Proof.
  intros l tgm. destruct l; simpl; auto.
Qed.


Fixpoint size (t:tree) : nat :=
  match t with
  | Mismatch | Match => 1
  | Choice t1 t2 | LK _ t1 t2 => 1 + (size t1) + (size t2)
  (* In rule ptss_blocked, a bonus might be added in for the new state if the blocked list was previously empty. To ensure that ptss_blocked still strictly decreases the measure, we give a size of 2 to Read nodes (a Read node gets removed during ptss_blocked). *)
  | Read _ t1 => 2 + (size t1)
  | ReadBackRef _ t1 | Progress t1 | AnchorPass _ t1
  | GroupAction _ t1 | LKFail _ t1 => 1 + (size t1)
  end.

Lemma size_strict_pos:
  forall t, size t > 0.
Proof.
  intros t. induction t; simpl; lia.
Qed.

Definition list_size (l: list (tree * group_map)) : nat :=
  List.fold_right (fun tgm n => n + size (fst tgm)) 0 l.

Lemma list_size_0:
  forall l, list_size l = 0 <-> l = [].
Proof.
  intros l. split; intros H; subst; auto.
  destruct l as [|[t gm] l]. auto.
  unfold list_size in H. simpl in H. assert (size t > 0) by apply size_strict_pos. lia.
Qed.

Lemma list_size_app:
  forall l1 l2, list_size (l1 ++ l2) = list_size l1 + list_size l2.
Proof.
  intros l1 l2. induction l1; auto. simpl. rewrite IHl1. lia.
Qed.

Definition pt_measure (pts:pike_tree_seen_state) : nat :=
  match pts with
  | PTSS_final _ => 0
  | PTSS inp active best blocked seen =>
      1 + list_size active + list_size blocked + bonus blocked
  end.

Lemma pt_measure_0:
  forall pts, pt_measure pts = 0 <-> exists r, pts = PTSS_final r.
Proof.
  intros pts. split; intros.
  - destruct pts; eauto. simpl in H. lia.
  - destruct H as [r H]. subst. auto.
Qed.

Theorem piketree_decreases:
  forall pts1 pts2,
    pike_tree_seen_step pts1 pts2 ->
    pt_measure pts2 < pt_measure pts1.
Proof.
  intros pts1 pts2 H. destruct H; simpl;
    match goal with
    | [|- context[size ?t]] => specialize (size_strict_pos t) as H
    | _ => auto
    end; try lia.
  - rewrite list_size_app. destruct t; inversion STEP; simpl; lia.
  - rewrite bonus_add. rewrite list_size_app.
    destruct t; inversion STEP; simpl; lia.
Qed.

Lemma piketree_finishes:
  forall n pts,
    pt_measure pts <= n ->
    exists res, trc_pike_tree pts (PTSS_final res).
Proof.
  intros n. induction n; intros.
  - apply PeanoNat.Nat.le_0_r in H. apply pt_measure_0 in H as [r H].
    exists r. subst. repeat econstructor.
  - specialize (piketree_productivity pts) as [[r FINAL]|[next STEP]].
    { subst. exists r. repeat econstructor. }
    apply piketree_decreases in STEP as DECR. assert (DEC: pt_measure next <= n) by lia.
    apply IHn in DEC as [r TRC]. exists r. eapply trc_cons; eauto.
Qed.

Theorem piketree_termination:
  forall pts, 
  exists res, trc_pike_tree pts (PTSS_final res).
Proof.
  intros pts. eapply piketree_finishes. eauto.
Qed.





