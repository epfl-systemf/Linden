From Coq Require Import List.
From Warblre Require Import Base.
From Linden Require Import Regex Chars Groups Tree Semantics FunctionalSemantics FunctionalUtils.
Import ListNotations.

Module Right.
  Section EquivalenceProof.
    Context {char: Parameters.Character.class}.
    Context {x0 x1 y: regex}.

    Definition factored: regex :=
      Sequence (Disjunction x0 x1) y.

    Definition expanded: regex :=
      Disjunction (Sequence x0 y) (Sequence x1 y).

    Theorem expand_correct i gm:
      forall trf tre,
        is_tree [Areg factored] i gm forward trf ->
        is_tree [Areg expanded] i gm forward tre ->
        tree_leaves trf gm i forward =
          tree_leaves tre gm i forward.
    Proof.
      intros * Hf He.
      erewrite is_tree_determ with (1 := Hf).
      erewrite is_tree_determ with (1 := He).
      2, 3: repeat (econstructor; simpl); eapply compute_tr_is_tree.
      1: reflexivity.
      all: do 2 apply ComputeIsTree.inp_valid_checks_Areg; apply ComputeIsTree.inp_valid_checks_nil.
    Qed.
  End EquivalenceProof.
End Right.

Module Left.
  Section Counterexample.
    Context {char: Parameters.Character.class}.
    Context (c: Parameters.Character).

    Let capture n := Group n (Character (CdSingle c)).

    Definition x := Disjunction (capture 1) Epsilon.
    Definition y0 := capture 2.
    Definition y1 := Epsilon.

    Definition factored: regex :=
      Sequence x (Disjunction y0 y1).

    Definition expanded: regex :=
      Disjunction (Sequence x y0) (Sequence x y1).

    Definition input := [c].

    Theorem expand_incorrect:
      forall trf tre,
        priotree factored input trf ->
        priotree expanded input tre ->
        tree_res trf GroupMap.empty (init_input input) forward <>
          tree_res tre GroupMap.empty (init_input input) forward.
    Proof.
      intros * Hf He.
      pattern trf; eapply compute_tr_ind with (3 := Hf).
      2: { apply ComputeIsTree.inp_valid_checks_Areg, ComputeIsTree.inp_valid_checks_nil. }
      pattern tre; eapply compute_tr_ind with (3 := He).
      2: { apply ComputeIsTree.inp_valid_checks_Areg, ComputeIsTree.inp_valid_checks_nil. }
      unfold compute_tr; repeat (simpl; rewrite ?EqDec.reflb).
      inversion 1.
    Qed.
  End Counterexample.
End Left.
