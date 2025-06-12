From Linden Require Import RewritingSetup.

Module Right.
  Section EquivalenceProof.
    Context {char: Parameters.Character.class}.
    Context {x0 x1 y: regex}.

    Definition factored: regex :=
      Sequence (Disjunction x0 x1) y.

    Definition expanded: regex :=
      Disjunction (Sequence x0 y) (Sequence x1 y).

    Theorem factored_expanded_right_equiv:
      factored ≅[forward] expanded.
    Proof.
      autounfold with tree_equiv; intros * Hf He.
      erewrite is_tree_determ with (1 := Hf).
      erewrite is_tree_determ with (1 := He).
      2, 3: repeat (econstructor; simpl); eapply compute_tr_is_tree; eauto with inp_valid.
      1: reflexivity.
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

    Definition input := init_input [c].

    Theorem factored_expanded_left_nequiv:
      factored ≇ expanded.
    Proof.
      eapply (tree_nequiv_compute_counterexample input GroupMap.empty forward).
      autounfold with tree_equiv; unfold compute_tr; repeat (simpl; rewrite ?EqDec.reflb).
      inversion 1.
    Qed.
  End Counterexample.
End Left.
