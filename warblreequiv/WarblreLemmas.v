From Warblre Require Import Match Notation Parameters RegExpRecord List Result.
From Linden Require Import Chars MSInput.
From Coq Require Import ZArith Lia.
Import Notation.
Import Match.MatchState.

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








