(** * Termination of the PikeTree and PïkeVM algorithm *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeTree PikeVM PikeSubset.
From Linden Require Import PikeTreeSeen PikeVMSeen.
From Linden Require Import Correctness PikeSeenEquiv.

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

Lemma piketree_can_finish:
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

(* Note that this does not mean that all executions of PikeTree terminate (it is non-deterministic) *)
(* but that a terminating execution can be started from any state *)
Theorem piketree_weak_termination:
  forall pts, 
  exists res, trc_pike_tree pts (PTSS_final res).
Proof.
  intros pts. eapply piketree_can_finish. eauto.
Qed.


(** * Termination of the PikeVM Algorithm  *)

(* This is proved using the fact that the PikeTree measure decreases, and that there is a strictly decreasing measure in the invariant preservation theorem between PikeTree and PikeVM *)
(* We use a lexicographic order between these two measures *)

(* the first nat is the piketree measure, the second one is from the piketree-pikevm invariant *)
Definition measure : Type := (nat * nat).

(* lexicographic order *)
Inductive lt : measure -> measure -> Prop :=
| lt_left: forall n1 n2 m1 m2, n1 < n2 -> lt (n1, m1) (n2, m2)
| lt_right: forall n m1 m2, m1 < m2 -> lt (n, m1) (n, m2).

Require Import Init.Wf.

(* it is well-founded because < is well-founded *)
Lemma wf_lex:
  well_founded lt.
Proof.
  assert (forall x, Acc Peano.lt x -> forall y, Acc Peano.lt y -> Acc lt (x,y)).
  { intros x LEFT. induction LEFT. intros y RIGHT. induction RIGHT.
    constructor; intros. inversion H3; subst; auto.
    apply H0; auto. apply PeanoNat.Nat.lt_wf_0. }
  unfold well_founded. intros [n m]. apply H; auto;
    apply PeanoNat.Nat.lt_wf_0.
Qed.

(* Decreasing lexicographic order on the PikeVM execution *)
Theorem pikevm_decreases:
  forall code rer pts1 pvs1 pvs2 m1,
    stutter_wf rer code -> 
    pike_inv rer code pts1 pvs1 m1 ->
    pike_vm_seen_step rer code pvs1 pvs2 ->
    exists pts2, exists m2,
      (pike_inv rer code pts2 pvs2 m2 /\
         lt (pt_measure pts2,m2) (pt_measure pts1,m1)).
Proof.
  intros code rer pts1 pvs1 pvs2 m1 H H0 H1.
  eapply invariant_preservation in H1; eauto.
  destruct H1 as [[pts2 [m2 [STEP INV]]]|[m2 [INV LESS]]].
  - exists pts2. exists m2. split; auto.
    apply piketree_decreases in STEP. apply lt_left; auto.
  - exists pts1. exists m2. split; auto. apply lt_right; auto.
Qed.

(* a well-founded induction on the lexicographic measure *)
Theorem pikevm_finishes:
  forall code rer pts pvs m,
    stutter_wf rer code ->
    pike_inv rer code pts pvs m ->
    exists res, trc_pike_vm rer code pvs (PVSS_final res).
Proof.
  intros code rer pts pvs m ST INV.
  remember (pt_measure pts,m) as meas. change measure in meas.
  generalize dependent pts. generalize dependent pvs. generalize dependent m.
  induction meas using (well_founded_induction wf_lex); intros.
  destruct pvs.
  (* already at a final state *)
  2: { exists best. econstructor. }
  (* not at a final state: a step is possible *)
  specialize (pikevm_progress rer code inp active best blocked seen) as [pvs2 STEP].
  (* the new pikevm state maintains the invariant, while decreasing the measure *)
  specialize (pikevm_decreases _ _ _ _ _ _ ST INV STEP) as [pts2 [m2 [INV2 LT]]].
  rewrite <- Heqmeas in LT. apply H with (pts:=pts2) (pvs:=pvs2) (m:=m2) in LT as [res TRC]; auto.
  exists res. apply trc_cons with (y:=pvs2); auto.
Qed.

(* for any pike regex and input, the PikeVM, starting from its initial state, reaches a final state *)
Theorem pike_vm_terminates:
  forall rer r inp,
    pike_regex r ->
    exists result, trc_pike_vm rer (compilation r) (pike_vm_seen_initial_state inp) (PVSS_final result).
Proof.
  intros rer r inp H. eapply pikevm_finishes.
  - eapply compilation_stutter_wf; eauto.
  - eapply initial_pike_inv; eauto.
    eapply encode_equal with (gm:=GroupMap.empty); eauto.
    + pike_subset.
    + repeat constructor.
    + eapply FunctionalUtils.compute_tr_is_tree.
Qed.
