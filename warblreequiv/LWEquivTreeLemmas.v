From Linden Require Import RegexpTranslation LindenParameters Regex MSInput CharsWarblre Chars.
From Warblre Require Import StaticSemantics List Parameters Notation Match Result Errors RegExpRecord.
From Coq Require Import Lia ZArith.
Import Notation.
Import MatchState.
Import Match.
Import Result.
Import Result.Notations.

Lemma num_groups_equiv:
  forall wreg lreg n,
    equiv_regex' wreg lreg n ->
    num_groups lreg = countLeftCapturingParensWithin_impl wreg.
Proof.
  intros wreg lreg n Hequiv.
  induction Hequiv as [
    n |
    n c |
    n |
    n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
    n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
    n wr lr wquant lquant wgreedylazy greedy Hequiv IH Hequivquant Hequivgreedy |
    name n wr lr Hequiv IH
    ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. lia.
  - simpl. lia.
  - inversion Hequivquant; inversion Hequivgreedy; simpl; assumption.
  - simpl. f_equal. assumption.
Qed.

Lemma capupd_valid `{specParameters: Parameters}:
  forall str rer msend nrange n cap,
    MatchState.Valid str rer msend ->
    CaptureRange.Valid str nrange ->
    List.Update.Nat.One.update nrange (captures msend) n = Success cap ->
    MatchState.Valid str rer (match_state str (endIndex msend) cap).
Proof.
  intros str rer msend nrange n cap [Honinp [Hiton [Hlencap Hcapvalid]]] Hnrangevalid Hupdsucc.
  split; [|split; [|split]].
  - reflexivity.
  - assumption.
  - transitivity (length (captures msend)).
    2: assumption.
    symmetry.
    eapply List.Update.Nat.One.success_length. eassumption.
  - eapply List.Update.Nat.One.prop_preservation; eassumption.
Qed.

Lemma grouprange_valid `{specParameters: Parameters}:
  forall str0 rer ms msend,
    MatchState.Valid str0 rer ms -> MatchState.Valid str0 rer msend ->
    (MatchState.endIndex ms <= MatchState.endIndex msend)%Z ->
    CaptureRange.Valid str0 (Some (capture_range (MatchState.endIndex ms) (MatchState.endIndex msend))).
Proof.
  intros str0 rer ms msend [_ [Hitonms _]] [_ [Hitonmsend _]] Hle.
  constructor; assumption.
Qed.

Lemma equiv_def_groups:
  forall wr lr n parenCount ctx,
    equiv_regex' wr lr n ->
    parenCount = StaticSemantics.countLeftCapturingParensWithin wr ctx ->
    def_groups lr = List.seq (n+1) parenCount.
Proof.
  intros wr lr n parenCount ctx Hequiv.
  revert parenCount ctx.
  induction Hequiv as [
    n |
    n c |
    n |
    n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
    n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
    n wr lr wquant lquant wgreedylazy greedy Hequiv IH Hequivquant Hequivgreedy |
    name n wr lr Hequiv IH
    ].
  - intros parenCount ctx Hcount.
    simpl in *. subst parenCount. reflexivity.
  - intros parenCount ctx Hcount.
    simpl in *. subst parenCount. reflexivity.
  - intros parenCount ctx Hcount.
    simpl in *. subst parenCount. reflexivity.
  - intros parenCount ctx Hcount.
    simpl in *.
    specialize (IH1 (countLeftCapturingParensWithin wr1 ctx) ctx eq_refl).
    specialize (IH2 (countLeftCapturingParensWithin wr2 ctx) ctx eq_refl).
    rewrite IH1, IH2.
    unfold countLeftCapturingParensWithin in *.
    rewrite num_groups_equiv with (wreg := wr1) (n := n). 2: assumption.
    subst parenCount.
    symmetry.
    replace (countLeftCapturingParensWithin_impl _ + n + 1) with ((n + 1) + countLeftCapturingParensWithin_impl wr1) by lia.
    apply List.seq_app.
  - (* Sequence: same as disjunction *)
    intros parenCount ctx Hcount.
    simpl in *.
    specialize (IH1 (countLeftCapturingParensWithin wr1 ctx) ctx eq_refl).
    specialize (IH2 (countLeftCapturingParensWithin wr2 ctx) ctx eq_refl).
    rewrite IH1, IH2.
    unfold countLeftCapturingParensWithin in *.
    rewrite num_groups_equiv with (wreg := wr1) (n := n). 2: assumption.
    subst parenCount.
    symmetry.
    replace (countLeftCapturingParensWithin_impl _ + n + 1) with ((n + 1) + countLeftCapturingParensWithin_impl wr1) by lia.
    apply List.seq_app.
  - intros parenCount ctx Hcount.
    simpl in *.
    inversion Hequivquant; inversion Hequivgreedy; simpl in *; eapply IH; eassumption.
  - intros parenCount ctx Hcount.
    simpl in *.
    specialize (IH (countLeftCapturingParensWithin wr ctx) ctx eq_refl).
    rewrite IH.
    subst parenCount.
    replace (n + 1) with (S n) by lia.
    apply List.cons_seq.
Qed.


Lemma char_match_warblre:
  forall rer chr c,
    RegExpRecord.ignoreCase rer = false ->
    CharSet.exist_canonicalized rer (CharSet.singleton c) (char_canonicalize rer chr) = true ->
    char_match chr (single c) = true.
Proof.
  intros rer chr c Hcasesenst Hexist_canon.
  apply <- single_match.
  rewrite canonicalize_casesenst in Hexist_canon. 2: assumption.
  rewrite CharSet.exist_canonicalized_equiv in Hexist_canon.
  rewrite CharSet.singleton_exist in Hexist_canon.
  rewrite canonicalize_casesenst in Hexist_canon. 2: assumption.
  symmetry. now apply Typeclasses.EqDec.inversion_true.
Qed.


Lemma read_char_success:
  forall ms inp chr c rer inp_adv,
    RegExpRecord.ignoreCase rer = false ->
    ms_matches_inp ms inp ->
    List.Indexing.Int.indexing (MatchState.input ms) (MatchState.endIndex ms) = Success chr ->
    CharSet.exist_canonicalized rer (CharSet.singleton c) (char_canonicalize rer chr) = true ->
    advance_input inp = Some inp_adv ->
    read_char (single c) inp = Some (chr, inp_adv).
Proof.
  intros ms inp chr c rer inp_adv Hcasesenst Hms_inp Hreadsuccess Hcharcorresp Hadv.
  destruct inp as [next pref].
  destruct next as [|x next'].
  1: discriminate.
  injection Hadv as <-.
  simpl.
  inversion Hms_inp as [str0 end_ind cap next2 pref2 Hlenpref Heqstr0 Heqms Heqnext2].
  subst next2 pref2.
  subst ms str0.
  simpl in *.
  rewrite List.Indexing.Int.of_nat in Hreadsuccess.
  apply List.Indexing.Nat.concat in Hreadsuccess.
  destruct Hreadsuccess as [ [Habs _] | [Hzero Hreadsuccess] ].
  1: {
    rewrite List.rev_length in Habs. lia.
  }
  rewrite List.rev_length in Hreadsuccess.
  replace (end_ind - length pref) with 0 in Hreadsuccess by lia.
  injection Hreadsuccess as <-.
  now rewrite char_match_warblre with (rer := rer).
Qed.

Lemma char_mismatch_warblre:
  forall rer chr c,
    RegExpRecord.ignoreCase rer = false ->
    CharSet.exist_canonicalized rer (CharSet.singleton c) (char_canonicalize rer chr) = false ->
    char_match chr (single c) = false.
Proof.
  intros rer chr c Hcasesenst Hexist_false.
  rewrite CharSet.exist_canonicalized_equiv in Hexist_false.
  rewrite CharSet.singleton_exist in Hexist_false.
  rewrite canonicalize_casesenst in Hexist_false. 2: assumption.
  rewrite canonicalize_casesenst in Hexist_false. 2: assumption.
  apply Typeclasses.EqDec.inversion_false in Hexist_false.
  destruct char_match eqn:Hchar_match.
  2: reflexivity.
  rewrite single_match in Hchar_match.
  congruence.
Qed.

Lemma read_char_fail:
  forall rer ms chr inp c,
    RegExpRecord.ignoreCase rer = false ->
    ms_matches_inp ms inp ->
    List.Indexing.Int.indexing (MatchState.input ms) (MatchState.endIndex ms) = Success chr ->
    CharSet.exist_canonicalized rer (CharSet.singleton c) (char_canonicalize rer chr) = false ->
    read_char (single c) inp = None.
Proof.
  intros rer ms chr inp c Hcasesenst Hms_inp Hreadsuccess Hnocorresp.
  destruct inp as [next pref].
  destruct ms as [str0 endInd cap].
  inversion Hms_inp as [s end_ind cap0 next0 pref0 Hlenpref Hmatches Heqs Heqend_ind].
  subst s cap0 pref0 next0 endInd.
  simpl in *.
  rewrite List.Indexing.Int.of_nat in Hreadsuccess.
  subst str0.
  subst end_ind.
  apply List.Indexing.Nat.concat in Hreadsuccess.
  destruct Hreadsuccess as [ [Habs _] | [_ Hreadsuccess] ].
  1: {
    rewrite List.rev_length in Habs. lia.
  }
  rewrite List.rev_length in Hreadsuccess.
  replace (length pref - length pref) with 0 in Hreadsuccess by lia.
  destruct next as [|x next'].
  1: discriminate.
  injection Hreadsuccess as <-.
  now rewrite char_mismatch_warblre with (rer := rer).
Qed.
  

Lemma advance_input_compat:
  forall inp str0 inp_adv,
    input_compat inp str0 ->
    advance_input inp = Some inp_adv ->
    input_compat inp_adv str0.
Proof.
  intros inp str0 inp_adv Hinpcompat Hadv.
  inversion Hinpcompat as [next pref str1 Hcompat Heqinp Heqstr1].
  subst str1 inp.
  destruct next as [ | x next' ].
  1: discriminate.
  injection Hadv as <-.
  constructor.
  subst str0.
  simpl.
  rewrite <- List.app_assoc.
  reflexivity.
Qed.

Lemma ms_advance_valid:
  forall ms rer ms_adv,
    MatchState.Valid (MatchState.input ms) rer ms ->
    (MatchState.endIndex ms + 1 <= Z.of_nat (length (MatchState.input ms)))%Z ->
    ms_adv = advance_ms ms ->
    MatchState.Valid (MatchState.input ms_adv) rer ms_adv.
Proof.
  intros ms rer ms_adv [Honinp [Hiton [Hlencap Hcapvalid]]] Hinb Heqms_adv.
  destruct ms as [input endIndex cap].
  unfold advance_ms in Heqms_adv.
  simpl in Heqms_adv.
  subst ms_adv.
  simpl in *.
  split; [|split; [|split]].
  - reflexivity.
  - unfold IteratorOn in *. simpl. lia.
  - apply Hlencap.
  - apply Hcapvalid.
Qed.

Lemma ms_matches_inp_adv:
  forall ms inp ms_adv inp_adv,
    ms_matches_inp ms inp ->
    ms_adv = advance_ms ms ->
    advance_input inp = Some inp_adv ->
    ms_matches_inp ms_adv inp_adv.
Proof.
  intros ms inp ms_adv inp_adv Hmatches Heqms_adv Hinp_adv.
  destruct ms as [input endIndex cap].
  destruct inp as [next pref].
  destruct next as [|x next'].
  1: discriminate.
  injection Hinp_adv as <-.
  unfold advance_ms in Heqms_adv.
  simpl in *.
  subst ms_adv.
  inversion Hmatches as [s end_ind cap1 next1 pref1 Hlenpref Hmatches' Heqs Heqend_ind].
  subst cap1 pref1 next1 s.
  replace (Z.of_nat end_ind + 1)%Z with (Z.of_nat (end_ind + 1)) by lia.
  constructor.
  - simpl. lia.
  - simpl. rewrite <- List.app_assoc. apply Hmatches'.
Qed.

