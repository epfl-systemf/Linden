From Coq Require Import List.
From Warblre Require Import Base.
From Linden Require Import Regex Chars Groups Tree Semantics FunctionalSemantics FunctionalUtils.
Import ListNotations.

Section Anchors.
  Context {char: Parameters.Character.class}.

  Definition desugar_anchor (a: anchor) :=
    match a with
    | BeginInput =>
        Lookaround NegLookBehind (Character CdAll)
    | EndInput =>
        Lookaround NegLookAhead (Character CdAll)
    | WordBoundary =>
        Disjunction
          (Sequence
             (Lookaround NegLookBehind (Character CdWordChar))
             (Lookaround LookAhead (Character CdWordChar)))
          (Sequence
             (Lookaround LookBehind (Character CdWordChar))
             (Lookaround NegLookAhead (Character CdWordChar)))
    | NonWordBoundary =>
        Sequence
          (Disjunction
             (Lookaround LookBehind (Character CdWordChar))
             (Lookaround NegLookAhead (Character CdWordChar)))
          (Disjunction
             (Lookaround NegLookBehind (Character CdWordChar))
             (Lookaround LookAhead (Character CdWordChar)))
    end.

  Ltac destr :=
    repeat match goal with
      | _ => progress simpl
      | [  |- context[match ?x with _ => _ end] ] =>
          lazymatch x with
          | context[match _ with _ => _ end] => fail
          | _ => destruct x eqn:?
          end
      end; reflexivity.

  Theorem desugar_anchor_correct' (a: anchor) (i: input) dir gm:
    tree_leaves (compute_tr [Areg (Anchor a)] i gm dir) gm i dir =
      tree_leaves (compute_tr [Areg (desugar_anchor a)] i gm dir) gm i dir.
  Proof.
    unfold compute_tr;
      destruct a, dir; simpl;
      unfold compute_tr, anchor_satisfied, is_boundary, word_char, xorb, negb.
    all: destr.
  Qed.

  Theorem desugar_anchor_correct (a: anchor) (i: input) dir gm:
    forall tra trl,
      is_tree [Areg (Anchor a)] i gm dir tra ->
      is_tree [Areg (desugar_anchor a)] i gm dir trl ->
      tree_leaves tra gm i dir =
        tree_leaves trl gm i dir.
  Proof.
    eintros tra trlk Ha Hlk.
    pattern tra; eapply compute_tr_ind with (3 := Ha).
    2: { apply ComputeIsTree.inp_valid_checks_Areg, ComputeIsTree.inp_valid_checks_nil. }
    pattern trlk; eapply compute_tr_ind with (3 := Hlk).
    2: { apply ComputeIsTree.inp_valid_checks_Areg, ComputeIsTree.inp_valid_checks_nil. }
    apply desugar_anchor_correct'.
  Qed.
End Anchors.
