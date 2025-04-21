From Warblre Require Import Match Notation Parameters RegExpRecord.
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
