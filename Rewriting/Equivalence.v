From Coq Require Export List Equivalence.
From Warblre Require Import Base.
From Linden Require Import Regex Chars Groups Tree Semantics FunctionalSemantics FunctionalUtils ComputeIsTree.

Export ListNotations.

Section Definitions.
  Context {char: Parameters.Character.class}.

  Definition tree_equiv_tr_dir i gm dir tr1 tr2 :=
    tree_leaves tr1 gm i dir = tree_leaves tr2 gm i dir.

  Definition tree_nequiv_tr_dir i gm dir tr1 tr2 :=
    tree_res tr1 gm i dir <> tree_res tr2 gm i dir.

  Section IsTree.
    Definition tree_equiv_dir dir r1 r2 :=
      forall i gm tr1 tr2,
        is_tree [Areg r1] i gm dir tr1 ->
        is_tree [Areg r2] i gm dir tr2 ->
        tree_equiv_tr_dir i gm dir tr1 tr2.

    Definition tree_equiv r1 r2 :=
      forall dir, tree_equiv_dir dir r1 r2.

    Definition tree_nequiv_dir dir r1 r2 :=
      exists i gm tr1 tr2,
        is_tree [Areg r1] i gm dir tr1 /\
        is_tree [Areg r2] i gm dir tr2 /\
        tree_nequiv_tr_dir i gm dir tr1 tr2.

    Definition tree_nequiv r1 r2 :=
      exists dir, tree_nequiv_dir dir r1 r2.
  End IsTree.

  Section ComputeTree.
    Definition tree_equiv_compute_dir dir r1 r2 :=
      forall i gm,
        tree_equiv_tr_dir
          i gm dir
          (compute_tr [Areg r1] i gm dir)
          (compute_tr [Areg r2] i gm dir).

    Definition tree_equiv_compute r1 r2 :=
      forall dir, tree_equiv_compute_dir dir r1 r2.

    Definition tree_nequiv_compute_dir dir r1 r2 :=
      exists i gm,
        tree_nequiv_tr_dir
          i gm dir
          (compute_tr [Areg r1] i gm dir)
          (compute_tr [Areg r2] i gm dir).

    Definition tree_nequiv_compute r1 r2 :=
      exists dir, tree_nequiv_compute_dir dir r1 r2.
  End ComputeTree.

  Lemma tree_equiv_compute_dir_iff {dir r1 r2} :
    tree_equiv_dir dir r1 r2 <-> tree_equiv_compute_dir dir r1 r2.
  Proof.
    unfold tree_equiv_dir, tree_equiv_compute_dir, tree_equiv_tr_dir; split.
    - eauto 6 using compute_tr_is_tree.
    - intros Heq * H1 H2.
      pattern tr1; eapply compute_tr_ind with (2 := H1); eauto.
      pattern tr2; eapply compute_tr_ind with (2 := H2); eauto.
  Qed.

  Lemma tree_equiv_compute_iff {r1 r2} :
    tree_equiv r1 r2 <-> tree_equiv_compute r1 r2.
  Proof.
    unfold tree_equiv, tree_equiv_compute; split; intros;
      apply tree_equiv_compute_dir_iff; eauto.
  Qed.

  Lemma tree_nequiv_compute_dir_iff r1 r2 dir :
    tree_nequiv_dir dir r1 r2 <-> tree_nequiv_compute_dir dir r1 r2.
  Proof.
    unfold tree_nequiv_dir, tree_nequiv_compute_dir, tree_nequiv_tr_dir.
    split.
    - intros (i & gm & tr1 & tr2 & Htr1 & Htr2 & Hneq).
      rewrite (is_tree_eq_compute_tr Htr1), (is_tree_eq_compute_tr Htr2) in Hneq.
      eauto.
    - intros (i & gm & Hneq).
      eauto 7 using compute_tr_is_tree.
  Qed.

  Lemma tree_nequiv_compute_iff {r1 r2} :
    tree_nequiv r1 r2 <-> tree_nequiv_compute r1 r2.
  Proof.
    unfold tree_nequiv, tree_nequiv_compute.
    pose proof tree_nequiv_compute_dir_iff r1 r2.
    split; intros (dir & Hneq); exists dir; specialize (H dir); intuition.
  Qed.
End Definitions.

#[export]
Hint Unfold
  tree_equiv
  tree_equiv_dir
  tree_equiv_tr_dir
  tree_equiv_compute
  tree_equiv_compute_dir
  tree_nequiv
  tree_nequiv_dir
  tree_nequiv_tr_dir
  tree_nequiv_compute
  tree_nequiv_compute_dir
  : tree_equiv.

Ltac tree_equiv_rw :=
  try setoid_rewrite tree_equiv_compute_dir_iff;
  try setoid_rewrite tree_equiv_compute_iff;
  try setoid_rewrite tree_nequiv_compute_dir_iff;
  try setoid_rewrite tree_nequiv_compute_iff;
  autounfold with tree_equiv; intros.

Ltac tree_inv H :=
  erewrite is_tree_determ with (1 := H);
  [ | repeat (econstructor; simpl; rewrite ?app_nil_r; unfold seq_list)].

Ltac tree_equiv_inv :=
  autounfold with tree_equiv; intros * Hl Hr;
  tree_inv Hl; [ tree_inv Hr | ].

Hint Unfold
     compute_tr
     anchor_satisfied
     is_boundary
     read_char
     word_char
     andb orb negb xorb
  : tree_equiv_symbex.

Ltac tree_equiv_symbex_step :=
  match goal with
  | _ => progress simpl
  | [  |- context[match ?x with _ => _ end] ] =>
      lazymatch x with
      | context[match _ with _ => _ end] => fail
      | _ => destruct x eqn:?
      end
  end.

Ltac tree_equiv_symbex_prepare :=
  repeat (autounfold with tree_equiv_symbex; simpl).

Ltac tree_equiv_symbex :=
  repeat tree_equiv_symbex_prepare;
  repeat tree_equiv_symbex_step.

Section Relation.
  Context {char: Parameters.Character.class}.
  Context (dir: Direction).

  Ltac eqv := repeat red; tree_equiv_rw; solve [congruence | intuition | firstorder].

  #[global] Add Relation regex (tree_equiv_dir dir)
      reflexivity proved by ltac:(eqv)
      symmetry proved by ltac:(eqv)
      transitivity proved by ltac:(eqv)
      as tree_equiv_dir_rel.

  #[global] Add Relation regex tree_equiv
      reflexivity proved by ltac:(eqv)
      symmetry proved by ltac:(eqv)
      transitivity proved by ltac:(eqv)
      as tree_equiv_rel.

  #[global] Add Relation regex (tree_equiv_compute_dir dir)
      reflexivity proved by ltac:(eqv)
      symmetry proved by ltac:(eqv)
      transitivity proved by ltac:(eqv)
      as tree_equiv_compute_dir_rel.

  #[global] Add Relation regex tree_equiv_compute
      reflexivity proved by ltac:(eqv)
      symmetry proved by ltac:(eqv)
      transitivity proved by ltac:(eqv)
      as tree_equiv_compute_rel.

  (* #[global] Instance : Irreflexive (tree_nequiv_dir dir) := ltac:(eqv). *)
  (* #[global] Add Relation regex (tree_nequiv_dir dir) *)
  (*     symmetry proved by ltac:(eqv) *)
  (*     as tree_nequiv_dir_rel. *)

  (* #[global] Instance : Irreflexive tree_nequiv := ltac:(eqv). *)
  (* #[global] Add Relation regex tree_nequiv *)
  (*     symmetry proved by ltac:(eqv) *)
  (*     as tree_nequiv_rel. *)

  (* #[global] Instance : Irreflexive (tree_nequiv_compute_dir dir) := ltac:(eqv). *)
  (* #[global] Add Relation regex (tree_nequiv_compute_dir dir) *)
  (*     symmetry proved by ltac:(eqv) *)
  (*     as tree_nequiv_compute_dir_rel. *)

  (* #[global] Instance : Irreflexive tree_nequiv_compute := ltac:(eqv). *)
  (* #[global] Add Relation regex tree_nequiv_compute *)
  (*     symmetry proved by ltac:(eqv) *)
  (*     as tree_nequiv_compute_rel. *)
End Relation.

Notation "r1 ≅[ dir ] r2" := (tree_equiv_dir dir r1 r2) (at level 70, format "r1  ≅[ dir ]  r2").
Notation "r1 ≅ r2" := (tree_equiv r1 r2) (at level 70, format "r1  ≅  r2").
Notation "r1 ≇[ dir ] r2" := (tree_nequiv_dir dir r1 r2) (at level 70, format "r1  ≇[ dir ]  r2").
Notation "r1 ≇ r2" := (tree_nequiv r1 r2) (at level 70, format "r1  ≇  r2").
