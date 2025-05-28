From Linden Require Import Groups.
From Coq Require Import List.

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

Lemma gm_reset_find_other:
  forall gidl gm gid,
    ~In gid gidl -> GroupMap.find gid (GroupMap.reset gidl gm) = GroupMap.find gid gm.
Admitted.

Lemma gm_reset_find:
  forall gidl gm gid,
    In gid gidl -> GroupMap.find gid (GroupMap.reset gidl gm) = None.
Admitted.