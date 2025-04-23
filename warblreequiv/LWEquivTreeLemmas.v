From Linden Require Import RegexpTranslation LindenParameters Regex.
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
