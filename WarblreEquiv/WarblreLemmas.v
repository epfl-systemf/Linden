From Warblre Require Import Match Notation Parameters RegExpRecord List Result
  Semantics Result.
From Linden Require Import Chars MSInput CharSet.
From Coq Require Import ZArith Lia List.
Import Notation.
Import Result.Notations.
Import Match.MatchState.

Local Open Scope result_flow.

(** * Lemmas concerning Warblre structures *)

(* An inversion lemma for match state validity: the iterator is on the input string *)
Lemma valid_inv_iteratoron {specParameters: Parameters}:
  forall (str: list Character) (rer: RegExpRecord) (ms: MatchState),
    Valid str rer ms ->
    Match.IteratorOn str (MatchState.endIndex ms).
Proof.
  intros str rer ms [Hon [H []]].
  apply H.
Qed.

Lemma range_seq: forall base l, List.List.Range.Nat.Length.range base l = Coq.Lists.List.seq base l.
Proof.
  intros base l.
  revert base.
  induction l as [|l IHl].
  - simpl. reflexivity.
  - intro base. simpl. f_equal. replace (base + 1)%nat with (S base) by lia.
    apply IHl.
Qed.

Lemma nth_indexing {A F} `{Result.AssertionError F}:
  forall i (l: list A) (default: A),
    nth i l default =
    match List.Indexing.Nat.indexing l i with
    | Success x => x
    | Error _ => default
    end.
Proof.
  intros i l default. unfold List.Indexing.Nat.indexing.
  destruct nth_error eqn:Hnth_error; simpl.
  - apply nth_error_nth with (d := default) in Hnth_error. congruence.
  - rewrite nth_error_None in Hnth_error.
    rewrite nth_overflow by assumption.
    pose proof error_succ_abs (S := A).
    destruct Result.assertion_failed; try reflexivity.
    destruct (H0 s eq_refl).
Qed.

Lemma batch_update_spec {A: Type} {F} `{Result.AssertionError F}:
  forall (x: A) (l: list A) idxs (lupd: list A) i,
    List.Update.Nat.Batch.update x l idxs = Success lupd ->
    forall default,
    (In i idxs -> nth i lupd default = x) /\
    (~In i idxs -> nth i lupd default = nth i l default).
Proof.
  intros x l idxs lupd i Hupdsucc default.
  revert l lupd i Hupdsucc.
  induction idxs as [|idx idxs IH].
  - simpl. intros l lupd i. unfold List.Update.Nat.Batch.update.
    unfold List.lift_to_list. simpl. intro H0. injection H0 as <-. split.
    + intros [].
    + reflexivity.
  - intros l lupd i. rewrite List.Update.Nat.Batch.step.
    destruct List.Update.Nat.One.update as [ls'|] eqn:Hupdone; simpl; try discriminate.
    intro Hupdsucc. split.
    + intro Hin. destruct (List.in_dec Nat.eq_dec i idxs) as [Hinidxs | Hnotinidxs].
      * apply IH with (l := ls'); auto.
      * rewrite ((proj2 (IH ls' lupd i Hupdsucc)) Hnotinidxs).
        assert (Hidxi: idx = i) by tauto. subst i.
        pose proof List.Update.Nat.One.indexing_updated_same _ _ _ _ Hupdone as H0.
        rewrite nth_indexing, H0. reflexivity.
    + intro Hnotin. assert (Hnoti: idx <> i) by tauto. assert (Hnotinidxs: ~In i idxs) by tauto.
      rewrite ((proj2 (IH ls' lupd i Hupdsucc)) Hnotinidxs).
      pose proof List.Update.Nat.One.indexing_updated_other _ _ _ _ Hupdone _ Hnoti.
      rewrite nth_indexing, H0. symmetry. apply nth_indexing.
Qed.


Lemma batch_update_1 {A: Type} {F} `{Result.AssertionError F}:
  forall (x: A) (l: list A) idxs (lupd: list A) i,
    List.Update.Nat.Batch.update x l idxs = Success lupd ->
    In i idxs ->
    forall default, nth i lupd default = x.
Proof.
  intros x l idxs lupd i Hupdsucc Hin default.
  apply (proj1 (batch_update_spec x l idxs lupd i Hupdsucc default)). auto.
Qed.

Lemma batch_update_2 {A: Type} {F} `{Result.AssertionError F}:
  forall (x: A) (l: list A) idxs (lupd: list A) i,
    List.Update.Nat.Batch.update x l idxs = Success lupd ->
    ~In i idxs ->
    forall default, nth i lupd default = nth i l default.
Proof.
  intros x l idxs lupd i Hupdsucc Hin default.
  apply (proj2 (batch_update_spec x l idxs lupd i Hupdsucc default)). auto.
Qed.


(* Generalization of Warblre.props.StrictlyNullable.capture_reset_preserve_validity to arbitrary parenthesis indexes and counts.
   Any successful capture reset preserves validity of MatchStates.*)
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

From Linden Require Import LindenParameters.
From Warblre Require Import Errors.

Section WarblreLemmas.
  Context `{characterClass: Character.class}.
  Context {unicodeProp: Parameters.Property.class Parameters.Character}.

  Lemma wordCharacters_casesenst:
    forall rer,
      RegExpRecord.ignoreCase rer = false ->
      exists s,
        Semantics.wordCharacters rer = Success s /\
          CharSetExt.Equal s Characters.ascii_word_characters.
  Proof.
    intros rer Hcasesenst. unfold Semantics.wordCharacters.
    unfold Coercions.Coercions.wrap_CharSet. simpl. eexists.
    split. 1: reflexivity.
    intro c.
    rewrite CharSetExt.union_spec. rewrite CharSetExt.filter_spec.
    destruct CharSetExt.contains eqn:Hascii; simpl.
    - rewrite CharSetExt.contains_spec in Hascii. tauto.
    - rewrite canonicalize_casesenst by assumption. rewrite Hascii.
      assert (false = true <-> False). { split. - discriminate. - intros []. }
      tauto.
  Qed.

  Lemma wordCharacters_casesenst_eq:
    forall rer,
      RegExpRecord.ignoreCase rer = false ->
      Semantics.wordCharacters rer = Success Characters.ascii_word_characters.
  Proof.
    intros rer Hcasesenst.
    pose proof wordCharacters_casesenst rer Hcasesenst as [s [Heqs HEqual]].
    rewrite <- CharSetExt.canonicity in HEqual. now subst s.
  Qed.
End WarblreLemmas.
