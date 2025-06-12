From Coq Require Export List.
From Warblre Require Export Base.
From Linden Require Export Regex Chars Groups Tree Semantics FunctionalSemantics FunctionalUtils ComputeIsTree.

Export ListNotations.

Section Setup.
  Context {char: Parameters.Character.class}.

  Definition tree_equiv_tr_dir i gm dir tr1 tr2 :=
    tree_leaves tr1 gm (idx i) dir = tree_leaves tr2 gm (idx i) dir.

  Definition tree_nequiv_tr_dir i gm dir tr1 tr2 :=
    tree_leaves tr1 gm (idx i) dir <> tree_leaves tr2 gm (idx i) dir.

  Section IsTree.
    Definition tree_equiv_dir dir r1 r2 :=
      forall i gm tr1 tr2,
        is_tree [Areg r1] i gm dir tr1 ->
        is_tree [Areg r2] i gm dir tr2 ->
        tree_equiv_tr_dir i gm dir tr1 tr2.

    Definition tree_equiv r1 r2 :=
      forall dir, tree_equiv_dir dir r1 r2.

    Definition tree_nequiv_dir dir r1 r2 :=
      not (tree_equiv_dir dir r1 r2).

    Definition tree_nequiv r1 r2 :=
      not (tree_equiv r1 r2).
  End IsTree.

  Section ComputeTree.
    Definition tree_equiv_compute_dir dir r1 r2 :=
      forall i gm,
        tree_equiv_tr_dir i gm dir
          (compute_tr [Areg r1] i gm dir)
          (compute_tr [Areg r2] i gm dir).

    Definition tree_equiv_compute r1 r2 :=
      forall dir, tree_equiv_compute_dir dir r1 r2.

    Definition tree_nequiv_compute_dir dir r1 r2 :=
      not (tree_equiv_compute_dir dir r1 r2).

    Definition tree_nequiv_compute r1 r2 :=
      not (tree_equiv_compute r1 r2).
  End ComputeTree.

  Lemma tree_equiv_compute_dir_iff {dir r1 r2} :
    tree_equiv_dir dir r1 r2 <-> tree_equiv_compute_dir dir r1 r2.
  Proof.
    unfold tree_equiv_dir, tree_equiv_compute_dir, tree_equiv_tr_dir; split.
    - eauto 6 using compute_tr_is_tree with inp_valid.
    - intros Heq * H1 H2.
      pattern tr1; eapply compute_tr_ind with (3 := H1); eauto with inp_valid.
      pattern tr2; eapply compute_tr_ind with (3 := H2); eauto with inp_valid.
  Qed.

  Lemma tree_equiv_compute_iff {r1 r2} :
    tree_equiv r1 r2 <-> tree_equiv_compute r1 r2.
  Proof.
    unfold tree_equiv, tree_equiv_compute; split; intros;
      apply tree_equiv_compute_dir_iff; eauto.
  Qed.

  Lemma tree_nequiv_compute_dir_iff {dir r1 r2} :
    tree_nequiv_dir dir r1 r2 <-> tree_nequiv_compute_dir dir r1 r2.
  Proof.
    unfold tree_nequiv_dir, tree_nequiv_compute_dir.
    split; intros Hneq Heq%tree_equiv_compute_dir_iff; tauto.
  Qed.

  Lemma tree_nequiv_compute_iff {r1 r2} :
    tree_nequiv r1 r2 <-> tree_nequiv_compute r1 r2.
  Proof.
    unfold tree_nequiv, tree_nequiv_compute.
    split; intros Hneq Heq%tree_equiv_compute_iff; tauto.
  Qed.

  Definition tree_equiv_counterexample i gm dir r1 r2 tr1 tr2 :=
    is_tree [Areg r1] i gm dir tr1 /\
      is_tree [Areg r2] i gm dir tr2 /\
      tree_nequiv_tr_dir i gm dir tr1 tr2.

  Lemma tree_nequiv_dir_counterexample {dir r1 r2}:
    forall i gm tr1 tr2,
      tree_equiv_counterexample i gm dir r1 r2 tr1 tr2 ->
      tree_nequiv_dir dir r1 r2.
  Proof.
    unfold tree_nequiv_dir, tree_equiv_dir, tree_equiv_tr_dir; firstorder.
  Qed.

  Lemma tree_nequiv_counterexample {r1 r2}:
    forall i gm dir tr1 tr2,
      tree_equiv_counterexample i gm dir r1 r2 tr1 tr2 ->
      tree_nequiv r1 r2.
  Proof.
    unfold tree_nequiv, tree_equiv, tree_equiv_dir, tree_equiv_tr_dir; firstorder.
  Qed.

  Lemma tree_nequiv_compute_dir_counterexample {dir r1 r2}:
    forall i gm,
      tree_nequiv_tr_dir i gm dir
        (compute_tr [Areg r1] i gm dir)
        (compute_tr [Areg r2] i gm dir) ->
      tree_nequiv_dir dir r1 r2.
  Proof.
    unfold tree_nequiv_dir, tree_nequiv_tr_dir, tree_equiv_dir, tree_equiv_tr_dir.
    intros * Hneq Heq; apply Hneq, Heq; eauto using compute_tr_reg_is_tree.
  Qed.

  Lemma tree_nequiv_compute_counterexample {r1 r2}:
    forall i gm dir,
      tree_nequiv_tr_dir i gm dir
        (compute_tr [Areg r1] i gm dir)
        (compute_tr [Areg r2] i gm dir) ->
      tree_nequiv r1 r2.
  Proof.
    unfold tree_nequiv, tree_nequiv_tr_dir, tree_equiv.
    intros * Hneq Heq; apply Hneq, Heq; eauto using compute_tr_reg_is_tree.
  Qed.
End Setup.

Notation "tr1 '≅[' dir ']' tr2" := (tree_equiv_dir dir tr1 tr2) (at level 70).
Notation "tr1 '≅' tr2" := (tree_equiv tr1 tr2) (at level 70).
Notation "tr1 '≇[' dir ']' tr2" := (tree_nequiv_dir dir tr1 tr2) (at level 70).
Notation "tr1 '≇' tr2" := (tree_nequiv tr1 tr2) (at level 70).

#[export]
Hint Unfold
  tree_equiv
  tree_equiv_dir
  tree_equiv_tr_dir
  tree_equiv_compute
  tree_equiv_compute_dir
  tree_equiv_counterexample
  tree_nequiv
  tree_nequiv_dir
  tree_nequiv_tr_dir
  tree_nequiv_compute
  tree_nequiv_compute_dir
  tree_nequiv_counterexample
  : tree_equiv.
