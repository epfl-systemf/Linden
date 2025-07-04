From Linden.Rewriting Require Import ProofSetup.

Section Anchors.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Hypothesis ascii_word_canon:
    forall c,
      In c Character.ascii_word_characters ->
      In (Character.canonicalize rer c) Character.ascii_word_characters.

  Hypothesis line_terminators_canon:
    forall c,
      In c Character.line_terminators <->
      In (Character.canonicalize rer c) Character.line_terminators.

  Definition CdList (cs: list Parameters.Character) :=
    List.fold_right (fun c cd => CdUnion (CdSingle c) cd) CdEmpty cs.

  Definition desugar_anchor (a: anchor) :=
    match a with
    | BeginInput =>
        if RegExpRecord.multiline rer then
          Disjunction
            (Lookaround NegLookBehind (Character CdAll))
            (Lookaround LookBehind (Character (CdList Character.line_terminators)))
        else
            (Lookaround NegLookBehind (Character CdAll))
    | EndInput =>
        if RegExpRecord.multiline rer then
          Disjunction
            (Lookaround NegLookAhead (Character CdAll))
            (Lookaround LookAhead (Character (CdList Character.line_terminators)))
        else
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

  Lemma char_match_cdlist c cs:
    char_match rer c (CdList cs) = inb_canonicalized rer c cs.
  Proof.
    unfold CdList, char_match, inb_canonicalized; induction cs; simpl.
    all: try rewrite Utils.List.inb_cons, IHcs; reflexivity.
  Qed.

  Lemma char_match_line_terminators c:
    char_match rer c (CdList Character.line_terminators) =
      Utils.List.inb c Character.line_terminators.
  Proof.
    rewrite char_match_cdlist; unfold inb_canonicalized.
    apply Bool.eq_iff_eq_true; rewrite !Utils.List.inb_spec, in_map_iff.
    split; [ intros (c' & Hc & HIn) | solve[eauto] ].
    rewrite line_terminators_canon in *; congruence.
  Qed.

  (* FIXME why do I need this? *)
  Instance: Parameters := (@LWParameters.LWParameters params).

  (* FIXME move closer to definition *)
  Lemma wordCharacters_spec c:
    CharSet.CharSetExt.In c (wordCharacters rer) <->
      CharSet.CharSetExt.In c Characters.ascii_word_characters \/
        CharSet.CharSetExt.In (Character.canonicalize rer c) Characters.ascii_word_characters.
  Proof.
    unfold wordCharacters, Semantics.Semantics.wordCharacters,
      Coercions.wrap_CharSet; simpl.
    rewrite !CharSet.CharSetExt.union_spec.
    rewrite !CharSet.CharSetExt.filter_spec.
    rewrite !Bool.andb_true_iff, !Bool.negb_true_iff.
    rewrite !CharSet.CharSetExt.contains_spec.
    rewrite !CharSet.CharSetExt.contains_false_iff.
    setoid_rewrite CharSet.CharSetExt.from_list_spec.
    pose proof char_all_in c.
    assert (In c Character.ascii_word_characters \/ ~  In c Character.ascii_word_characters)
      by (rewrite <- !CharSet.CharSetExt.from_list_contains;
          destruct CharSet.CharSetExt.contains; eauto).
    intuition.
  Qed.

  Lemma wordCharacters_canonical t:
    CharSet.CharSetExt.contains (wordCharacters rer) t =
      CharSet.CharSetExt.exist_canonicalized rer (wordCharacters rer) (Character.canonicalize rer t).
  Proof.
    apply Bool.eq_true_iff_eq.
    rewrite CharSet.CharSetExt.exist_canonicalized_equiv, CharSet.CharSetExt.exist_iff.
    setoid_rewrite CharSet.CharSetExt.contains_spec.
    setoid_rewrite EqDec.inversion_true.
    setoid_rewrite wordCharacters_spec.
    setoid_rewrite CharSet.CharSetExt.from_list_spec.
    split; [ | intros (c & HIn & <-) ];
      intuition eauto using ascii_word_canon.
  Qed.

  Lemma char_match_word_char c:
    char_match rer c CdWordChar =
      CharSet.CharSetExt.contains (wordCharacters rer) c.
  Proof.
    unfold char_match; simpl.
    symmetry; apply wordCharacters_canonical.
  Qed.

  Hint Rewrite char_match_line_terminators char_match_word_char : tree_equiv_symbex.

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
  Qed.
End Anchors.

