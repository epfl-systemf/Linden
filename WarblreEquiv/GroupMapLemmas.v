From Linden Require Import Groups.
From Coq Require Import List DecidableClass Lia.

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
Admitted.

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
Admitted.

Lemma group_map_close_find_success_gt:
  forall gm startIdx origEndOpt endIdx gid,
    GroupMap.find gid gm = Some (GroupMap.Range startIdx origEndOpt) ->
    startIdx > endIdx ->
    GroupMap.find gid (GroupMap.close endIdx gid gm) = Some (GroupMap.Range endIdx (Some startIdx)).
Admitted.

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
Admitted.

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

Lemma gm_reset_find_other:
  forall gidl gm gid,
    ~In gid gidl -> GroupMap.find gid (GroupMap.reset gidl gm) = GroupMap.find gid gm.
Admitted.

Lemma gm_reset_find:
  forall gidl gm gid,
    In gid gidl -> GroupMap.find gid (GroupMap.reset gidl gm) = None.
Admitted.