From Warblre Require Import Match Notation Parameters RegExpRecord List Result.
From Linden Require Import Chars MSInput.
From Coq Require Import ZArith Lia.
Import Notation.
Import Match.MatchState.

Lemma valid_inv_iteratoron {specParameters: Parameters}:
  forall (str: list Character) (rer: RegExpRecord) (ms: MatchState),
    Valid str rer ms ->
    Match.IteratorOn str (MatchState.endIndex ms).
Proof.
  intros str rer ms [Hon [H []]].
  apply H.
Qed.

Lemma capture_reset_preserve_validity `{specParameters: Parameters}:
  forall parenIndex parenCount (rer:RegExpRecord)
    (x:MatchState) (VALID: Valid (MatchState.input x) rer x)
    (xupd: list (option CaptureRange))
    (UPD: @List.Update.Nat.Batch.update _ Errors.MatchError Errors.match_assertion_error None (MatchState.captures x) (List.Range.Nat.Bounds.range (parenIndex + 1 - 1) (parenIndex + parenCount + 1 - 1)) = Success xupd),
    Valid (MatchState.input x) rer (match_state (MatchState.input x) (MatchState.endIndex x) xupd).
Proof.
  intros r ctx rer x VALID xupd UPD.
  apply change_captures with (cap:=MatchState.captures x).
    - apply List.Update.Nat.Batch.success_length in UPD. rewrite <- UPD.
      destruct VALID as [_ [_ [LENGTH _]]]. auto.
    - destruct VALID as [_ [_ [_ FORALL]]].
      eapply List.Update.Nat.Batch.prop_preservation; eauto.
      apply Match.CaptureRange.vCrUndefined.
    - destruct x. now simpl in *.
Qed.

Lemma read_oob_fail:
  forall (ms: MatchState) (inp: input),
    (MatchState.endIndex ms + 1 > Z.of_nat (length (MatchState.input ms)))%Z ->
    ms_matches_inp ms inp ->
    exists pref, inp = Input nil pref.
Proof.
  intros ms inp Hoob Hmatches.
  inversion Hmatches as [s end_ind cap next pref Hlenpref Heqs Heqms Heqinp].
  subst ms. simpl in *.
  assert (Hoob': end_ind + 1 > length s) by lia.
  apply (f_equal (length (A := Chars.Char))) in Heqs.
  rewrite List.app_length in Heqs.
  rewrite List.rev_length in Heqs.
  assert (Hlen: end_ind = length s) by lia.
  assert (Hnext_zerolen: length next = 0) by lia.
  exists pref.
  f_equal.
  now apply List.length_zero_iff_nil.
Qed.

Lemma endInd_neg_abs:
  forall (ms: MatchState) (inp: input),
    ms_matches_inp ms inp ->
    ~(MatchState.endIndex ms + 1 < 0)%Z.
Proof.
  intros ms inp Hmatches.
  inversion Hmatches as [s end_ind cap next pref Hlenpref Heqs Heqms Heqinp].
  subst ms.
  simpl in *.
  lia.
Qed.

Lemma read_oob_fail_bool:
  forall (ms: MatchState) (inp: input),
    ms_matches_inp ms inp ->
    ((MatchState.endIndex ms + 1 <? 0)%Z || (MatchState.endIndex ms + 1 >? Z.of_nat (length (MatchState.input ms)))%Z)%bool = true ->
    forall cd: char_descr, read_char cd inp = None.
Proof.
  intros ms inp Hmatches Hoob.
  apply Bool.orb_true_elim in Hoob.
  destruct Hoob as [Hoob|Hoob].
  - exfalso. rewrite Z.ltb_lt in Hoob. apply (endInd_neg_abs _ _ Hmatches Hoob).
  - rewrite Z.gtb_gt in Hoob.
    pose proof read_oob_fail ms inp Hoob Hmatches.
    destruct H as [pref H].
    subst inp.
    simpl. reflexivity.
Qed.

Lemma next_inbounds_nextinp:
  forall (ms: MatchState) (inp: input),
    ms_matches_inp ms inp ->
    ((MatchState.endIndex ms + 1 <? 0)%Z || (MatchState.endIndex ms + 1 >? Z.of_nat (length (MatchState.input ms)))%Z)%bool = false ->
    exists inp', advance_input inp = Some inp'.
Proof.
  intros ms inp Hmatches Hinb.
  inversion Hmatches as [s end_ind cap next pref Hlenpref Heqs Heqms Heqinp].
  subst ms. simpl in *.
  destruct next as [|c next'].
  - exfalso.
    apply Bool.orb_false_elim in Hinb.
    destruct Hinb as [_ Hinb].
    assert (Hinb': end_ind + 1 <= length s) by lia.
    apply (f_equal (length (A := Chars.Char))) in Heqs.
    rewrite List.app_length in Heqs.
    rewrite List.rev_length in Heqs.
    simpl in Heqs.
    lia.
  - eexists. reflexivity.
Qed.
