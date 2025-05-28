From Linden Require Import Groups Tactics.
From Coq Require Import List DecidableClass Lia PeanoNat.

Lemma group_map_open_find_other:
  forall gm idx gid gid',
    gid <> gid' ->
    GroupMap.find gid' (GroupMap.open idx gid gm) = GroupMap.find gid' gm.
Proof.
  intros gm idx gid gid' Hneq.
  unfold GroupMap.open.
  destruct (GroupMap.find gid' gm) as [r|] eqn:Hfindgm.
  - apply GroupMap.MapS.find_2 in Hfindgm. now apply GroupMap.MapS.find_1, GroupMap.MapS.add_2.
  - unfold GroupMap.find.
    destruct GroupMap.MapS.find as [r|] eqn:Hfindgmadd; try reflexivity.
    apply GroupMap.MapS.find_2, GroupMap.MapS.add_3, GroupMap.MapS.find_1 in Hfindgmadd. 2: assumption.
    unfold GroupMap.find in Hfindgm. congruence.
Qed.

Lemma group_map_open_find:
  forall gm idx gid,
    GroupMap.find gid (GroupMap.open idx gid gm) = Some (GroupMap.Range idx None).
Proof.
  intros gm idx gid. unfold GroupMap.open.
  apply GroupMap.MapS.find_1, GroupMap.MapS.add_1. reflexivity.
Qed.

Lemma group_map_close_find_other:
  forall gm idx gid gid',
    gid <> gid' ->
    GroupMap.find gid' (GroupMap.close idx gid gm) = GroupMap.find gid' gm.
Proof.
  intros gm idx gid gid' Hneq.
  unfold GroupMap.close.
  destruct (GroupMap.find gid gm); simpl. 2: reflexivity.
  destruct r as [startIdx endIdxOpt].
  destruct (GroupMap.find gid' gm) as [r|] eqn:Hfindgm.
  - apply GroupMap.MapS.find_2 in Hfindgm. destruct Nat.leb.
    + apply GroupMap.MapS.find_1, GroupMap.MapS.add_2; assumption.
    + apply GroupMap.MapS.find_1, GroupMap.MapS.add_2; assumption.
  - destruct (GroupMap.find gid' (if Nat.leb _ _ then _ else _)) as [r|] eqn:Hfindgmadd; try reflexivity.
    destruct Nat.leb.
    + apply GroupMap.MapS.find_2, GroupMap.MapS.add_3, GroupMap.MapS.find_1 in Hfindgmadd. 2: assumption. unfold GroupMap.find in Hfindgm. congruence.
    + apply GroupMap.MapS.find_2, GroupMap.MapS.add_3, GroupMap.MapS.find_1 in Hfindgmadd. 2: assumption. unfold GroupMap.find in Hfindgm. congruence.
Qed.

Lemma group_map_close_find_success_le:
  forall gm startIdx origEndOpt endIdx gid,
    GroupMap.find gid gm = Some (GroupMap.Range startIdx origEndOpt) ->
    startIdx <= endIdx ->
    GroupMap.find gid (GroupMap.close endIdx gid gm) = Some (GroupMap.Range startIdx (Some endIdx)).
Proof.
  intros gm startIdx origEndOpt endIdx gid Hfind Hle.
  unfold GroupMap.close. rewrite Hfind. replace (startIdx <=? endIdx) with true.
  2: { symmetry. now apply <- Nat.leb_le. }
  apply GroupMap.MapS.find_1, GroupMap.MapS.add_1. reflexivity.
Qed.

Lemma group_map_close_find_success_gt:
  forall gm startIdx origEndOpt endIdx gid,
    GroupMap.find gid gm = Some (GroupMap.Range startIdx origEndOpt) ->
    startIdx > endIdx ->
    GroupMap.find gid (GroupMap.close endIdx gid gm) = Some (GroupMap.Range endIdx (Some startIdx)).
Proof.
  intros gm startIdx origEndOpt endIdx gid Hfind Hgt.
  assert (Hnle: ~(startIdx <= endIdx)) by lia.
  rewrite <- Nat.leb_le in Hnle. rewrite Bool.not_true_iff_false in Hnle.
  unfold GroupMap.close. rewrite Hfind, Hnle.
  apply GroupMap.MapS.find_1, GroupMap.MapS.add_1. reflexivity.
Qed.

Lemma group_map_close_find_success_exists:
  forall gm startIdx origEndOpt endIdx gid,
    GroupMap.find gid gm = Some (GroupMap.Range startIdx origEndOpt) ->
    exists start' end', GroupMap.find gid (GroupMap.close endIdx gid gm) = Some (GroupMap.Range start' (Some end')).
Proof.
  intros gm startIdx origEndOpt endIdx gid H.
  decide (startIdx <= endIdx) as Hle.
  - rewrite (group_map_close_find_success_le _ _ _ _ _ H) by assumption. eexists. eexists. reflexivity.
  - rewrite (group_map_close_find_success_gt _ _ _ _ _ H) by lia. eexists. eexists. reflexivity.
Qed.

Lemma group_map_close_find_fail:
  forall gm endIdx gid,
    GroupMap.find gid gm = None ->
    GroupMap.find gid (GroupMap.close endIdx gid gm) = None.
Proof.
  intros gm endIdx gid Hfind. unfold GroupMap.close.
  rewrite Hfind. assumption.
Qed.

Inductive is_open_range: option GroupMap.range -> Prop :=
| Is_open_range: forall startIdx, is_open_range (Some (GroupMap.Range startIdx None)).

Lemma group_map_close_find_notopen:
  forall gm endIdx gid,
    ~is_open_range (GroupMap.find gid (GroupMap.close endIdx gid gm)).
Proof.
  intros gm endIdx gid.
  destruct (GroupMap.find gid gm) as [[startIdx origEndOpt]|] eqn:Hfindorig.
  - apply group_map_close_find_success_exists with (endIdx := endIdx) in Hfindorig. destruct Hfindorig as [start' [end' ->]].
    intro Habs. inversion Habs.
  - apply group_map_close_find_fail with (endIdx := endIdx) in Hfindorig. rewrite Hfindorig. intro H. inversion H.
Qed.

Lemma gm_remove_find_other:
  forall gm gid gid',
    gid' <> gid ->
    GroupMap.find gid' (GroupMap.MapS.remove gid gm) = GroupMap.find gid' gm.
Proof.
  intros gm gid gid' Hdiff.
  destruct (GroupMap.find gid' gm) as [r|] eqn:Hfindorig.
  - apply GroupMap.MapS.find_1, GroupMap.MapS.remove_2.
    1: congruence. apply GroupMap.MapS.find_2. exact Hfindorig.
  - destruct (GroupMap.find gid' (GroupMap.MapS.remove _ _)) as [r|] eqn:Hfindremoved; try reflexivity.
    apply GroupMap.MapS.find_2, GroupMap.MapS.remove_3, GroupMap.MapS.find_1 in Hfindremoved. unfold GroupMap.find in Hfindorig. congruence.
Qed.

Lemma gm_remove_find:
  forall gm gid,
    GroupMap.find gid (GroupMap.MapS.remove gid gm) = None.
Proof.
  intros gm gid.
  destruct GroupMap.find as [r|] eqn:Hfind; try reflexivity.
  exfalso. pose proof GroupMap.MapS.remove_1. unfold not in H. apply H with (x := gid) (y := gid) (m := gm) (elt := GroupMap.range).
  1: reflexivity. unfold GroupMap.MapS.In, GroupMap.MapS.Raw.PX.In.
  exists r. apply GroupMap.MapS.find_2. exact Hfind.
Qed.

Lemma gm_reset_find_other:
  forall gidl gm gid,
    ~In gid gidl -> GroupMap.find gid (GroupMap.reset gidl gm) = GroupMap.find gid gm.
Proof.
  intros gidl gm gid Hnotin.
  generalize dependent gm. induction gidl as [|x rtl IH] using rev_ind.
  - simpl. reflexivity.
  - intro gm. unfold GroupMap.reset. rewrite fold_left_app. simpl.
    change (fold_left _ rtl gm) with (GroupMap.reset rtl gm).
    assert (Hgidnotx: gid <> x). {
      rewrite in_app_iff in Hnotin. simpl in *. symmetry. tauto.
    }
    specialize_prove IH. {
      intro Habs. rewrite in_app_iff in Hnotin. tauto.
    }
    specialize (IH gm).
    transitivity (GroupMap.find gid (GroupMap.reset rtl gm)). 2: exact IH.
    now apply gm_remove_find_other.
Qed.

Lemma gm_reset_find:
  forall gidl gm gid,
    In gid gidl -> GroupMap.find gid (GroupMap.reset gidl gm) = None.
Proof.
  intros gidl gm gid Hin.
  induction gidl as [|x rtl IH] using rev_ind.
  - inversion Hin.
  - apply in_app_or in Hin. destruct Hin as [Hinrtl | Heqx].
    + unfold GroupMap.reset. rewrite fold_left_app. simpl. change (fold_left _ rtl gm) with (GroupMap.reset rtl gm).
      decide (gid = x) as Hgidx.
      * subst gid. apply gm_remove_find.
      * rewrite gm_remove_find_other by assumption. auto.
    + simpl in Heqx. destruct Heqx as [Heqx|[]].
      unfold GroupMap.reset. rewrite fold_left_app. simpl. change (fold_left _ rtl gm) with (GroupMap.reset rtl gm).
      subst x. apply gm_remove_find.
Qed.
