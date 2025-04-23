From Linden Require Import RegexpTranslation LindenParameters.
From Warblre Require Import StaticSemantics List Parameters Notation Match Result Errors.
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
