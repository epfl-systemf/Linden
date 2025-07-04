From Linden.Rewriting Require Import ProofSetup.

Section Anchors.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).
  Hypothesis (noMultiline: RegExpRecord.multiline rer = false).
  Hypothesis (caseSensitive: RegExpRecord.ignoreCase rer = false).
  (* We need case sensitiveness because nothing guarantees that Characters.ascii_word_characters
  is stable by canonicalization if we have case insensitiveness. *)

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

  Lemma exist_canonicalized_casesenst:
    forall cset c,
      CharSet.CharSetExt.exist_canonicalized rer cset (Character.canonicalize rer c) =
      CharSet.CharSetExt.contains cset c.
  Proof.
    intros cset c.
    rewrite CharSet.CharSetExt.exist_canonicalized_equiv.
    rewrite canonicalize_casesenst by auto.
    apply Bool.eq_iff_eq_true.
    rewrite CharSet.CharSetExt.exist_iff. setoid_rewrite canonicalize_casesenst; auto.
    split.
    - intros [c0 [Hcontains Heq]]. rewrite EqDec.inversion_true in Heq. subst c0. auto.
    - intro Hcontains. exists c. split; auto. apply EqDec.reflb.
  Qed.

  Theorem desugar_anchor_correct (a: anchor):
    Anchor a ≅[rer] desugar_anchor a.
  Proof.
    destruct a; tree_equiv_rw.
    all: destruct dir; tree_equiv_symbex.
    all: try reflexivity.
    all: try rewrite noMultiline in Heqb; try discriminate.
    all: try rewrite exist_canonicalized_casesenst in *.
    all: try (setoid_rewrite Heqb0 in Heqb; discriminate).
    all: try (setoid_rewrite Heqb2 in Heqb; discriminate).
    all: try (setoid_rewrite Heqb1 in Heqb0; discriminate).
    all: try (setoid_rewrite Heqb2 in Heqb0; discriminate).
    all: try (setoid_rewrite Heqb1 in Heqb; discriminate).
  Qed.
End Anchors.
