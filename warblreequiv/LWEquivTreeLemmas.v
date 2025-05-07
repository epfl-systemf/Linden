From Linden Require Import RegexpTranslation LindenParameters Regex MSInput Chars ListLemmas CharDescrCharSet.
From Linden Require Semantics.
From Warblre Require Import StaticSemantics List Parameters Notation Match Result Errors RegExpRecord Patterns Semantics Base.
From Coq Require Import Lia ZArith List.
Import Notation.
Import MatchState.
Import Match.
Import Result.
Import Result.Notations.
Import ListNotations.

Local Open Scope bool_scope.
Local Open Scope result_flow.

(** * Lemmas for 2nd part of equivalence proof *)

(* Two equivalent regexes have the same number of capturing groups. *)
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
      esc cd n Hequivesc |
      esc cd n Hequivesc |
      cc cd n Hequivcc |
      n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
    n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
    n wr lr wquant lquant wgreedylazy greedy Hequiv IH Hequivquant Hequivgreedy |
    name n wr lr Hequiv IH |
    n wr lr wlk llk Hequiv IH Hequivlk |
    n wr lanchor Hanchequiv]; simpl; try lia; try reflexivity.
  - inversion Hequivquant; inversion Hequivgreedy; auto.
  - inversion Hequivlk; auto.
  - inversion Hanchequiv; auto.
Qed.


(* Successfully updating a valid MatchState with a valid CaptureRange yields a valid MatchState. *)
Lemma capupd_valid `{specParameters: Parameters}:
  forall str rer msend nrange n cap,
    MatchState.Valid str rer msend ->
    CaptureRange.Valid str nrange ->
    List.Update.Nat.One.update nrange (captures msend) n = Success cap ->
    MatchState.Valid str rer (match_state str (endIndex msend) cap).
Proof.
  intros str rer msend nrange n cap [Honinp [Hiton [Hlencap Hcapvalid]]] Hnrangevalid Hupdsucc.
  split; [|split; [|split]]; try easy.
  - transitivity (length (captures msend)).
    2: assumption.
    symmetry.
    eapply List.Update.Nat.One.success_length. eassumption.
  - eapply List.Update.Nat.One.prop_preservation; eassumption.
Qed.


(* A capture range created from two valid match states with the second one progressing wrt. the first one is valid. *)
Lemma grouprange_valid `{specParameters: Parameters}:
  forall str0 rer ms msend,
    MatchState.Valid str0 rer ms -> MatchState.Valid str0 rer msend ->
    (MatchState.endIndex ms <= MatchState.endIndex msend)%Z ->
    CaptureRange.Valid str0 (Some (capture_range (MatchState.endIndex ms) (MatchState.endIndex msend))).
Proof.
  intros str0 rer ms msend [_ [Hitonms _]] [_ [Hitonmsend _]] Hle.
  constructor; assumption.
Qed.


(* Lemma to determine the list of defined groups of a Linden regex. *)
Lemma equiv_def_groups:
  forall wr lr n parenCount ctx,
    (* If wr and lr are equivalent with n left capturing parentheses before them, *)
    equiv_regex' wr lr n ->
    (* and if wr contains parenCount left capturing parentheses, *)
    parenCount = StaticSemantics.countLeftCapturingParensWithin wr ctx ->
    (* then the groups defined by lr are exactly the groups n+1, n+2, ..., n+parenCount. *)
    def_groups lr = List.seq (n+1) parenCount.
Proof.
  intros wr lr n parenCount ctx Hequiv.
  revert parenCount ctx.
  induction Hequiv as [
    n |
    n c |
      n |
      esc cd n Hequivesc |
      esc cd n Hequivesc |
      cc cd n Hequivcc |
    n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
    n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
    n wr lr wquant lquant wgreedylazy greedy Hequiv IH Hequivquant Hequivgreedy |
    name n wr lr Hequiv IH |
    n wr lr wlk llk Hequiv IH Hequivlk |
    n wr lanchor Hanchequiv].
  - intros parenCount ctx Hcount.
    simpl in *. subst parenCount. reflexivity.
  - intros parenCount ctx Hcount.
    simpl in *. subst parenCount. reflexivity.
  - intros parenCount ctx Hcount.
    simpl in *. subst parenCount. reflexivity.
  - intros parenCount ctx Hcount.
    simpl in *. subst parenCount. reflexivity.
  - intros parenCount ctx Hcount.
    simpl in *. subst parenCount. reflexivity.
  - intros parenCount ctx Hcount.
    simpl in *. subst parenCount. reflexivity.
  - intros parenCount ctx Hcount. simpl in *.
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
    intros parenCount ctx Hcount. simpl in *.
    specialize (IH1 (countLeftCapturingParensWithin wr1 ctx) ctx eq_refl).
    specialize (IH2 (countLeftCapturingParensWithin wr2 ctx) ctx eq_refl).
    rewrite IH1, IH2.
    unfold countLeftCapturingParensWithin in *.
    rewrite num_groups_equiv with (wreg := wr1) (n := n). 2: assumption.
    subst parenCount.
    symmetry.
    replace (countLeftCapturingParensWithin_impl _ + n + 1) with ((n + 1) + countLeftCapturingParensWithin_impl wr1) by lia.
    apply List.seq_app.
  - intros parenCount ctx Hcount. simpl in *.
    inversion Hequivquant; inversion Hequivgreedy; simpl in *; eapply IH; eassumption.
  - intros parenCount ctx Hcount. simpl in *.
    specialize (IH (countLeftCapturingParensWithin wr ctx) ctx eq_refl). rewrite IH.
    subst parenCount.
    replace (n + 1) with (S n) by lia.
    apply List.cons_seq.
  - intros parenCount ctx. inversion Hequivlk; simpl in *; eapply IH; eauto.
  - intros parenCount ctx. inversion Hanchequiv; simpl in *; intro; subst parenCount; auto.
Qed.


(* Lemma linking the character matching conditions of Linden and Warblre. *)
Lemma char_match_warblre:
  forall rer chr cd charset,
    (* Let cd and charset be equivalent. *)
    equiv_cd_charset cd charset ->
    (* If we do not ignore case, *)
    RegExpRecord.ignoreCase rer = false ->
    (* and chr corresponds to charset in the Warblre sense, *)
    CharSet.exist_canonicalized rer charset (char_canonicalize rer chr) = true ->
    (* then chr corresponds to cd in the Linden sense. *)
    char_match chr cd = true.
Proof.
  intros rer chr cd charset Hequiv Hcasesenst Hexist_canon.
  rewrite CharSet.exist_canonicalized_equiv in Hexist_canon.
  rewrite charset_exist_iff in Hexist_canon. destruct Hexist_canon as [c [Hcontains Heq]].
  do 2 rewrite canonicalize_casesenst in Heq by assumption.
  rewrite Typeclasses.EqDec.inversion_true in Heq. subst c.
  unfold equiv_cd_charset in Hequiv. specialize (Hequiv chr). congruence.
Qed.

(* Same, but for inverted character descriptors. *)
Lemma char_match_warblre_inv:
  forall rer chr cd charset,
    (* Let cd and charset be equivalent. *)
    equiv_cd_charset cd charset ->
    (* If we do not ignore case, *)
    RegExpRecord.ignoreCase rer = false ->
    (* and chr corresponds to charset in the Warblre sense, *)
    CharSet.exist_canonicalized rer charset (char_canonicalize rer chr) = true ->
    (* then chr does not correspond to CdInv cd in the Linden sense. *)
    char_match chr (CdInv cd) = false.
Proof.
  intros rer chr cd charset Hequiv Hcasesenst Hexist_canon. simpl.
  apply <- Bool.negb_false_iff. eapply char_match_warblre; eauto.
Qed.


(* If reading a character succeeds in the Warblre sense, then it succeeds in the Linden sense as well. *)
Lemma read_char_success:
  forall ms inp chr cd charset rer dir inp_adv,
    (* Let cd and charset be equivalent. *)
    equiv_cd_charset cd charset ->
    (* If we do not ignore case, *)
    RegExpRecord.ignoreCase rer = false ->
    (* then for any match state and corresponding Linden input, *)
    ms_matches_inp ms inp ->
    (* if reading character c succeeds in the Warblre sense, *)
    List.Indexing.Int.indexing (MatchState.input ms) (
        match dir with forward => MatchState.endIndex ms | backward => MatchState.endIndex ms - 1 end) = Success chr ->
    CharSet.exist_canonicalized rer charset (char_canonicalize rer chr) = true ->
    (* then reading character c succeeds in the Linden sense. *)
    advance_input inp dir = Some inp_adv ->
    read_char cd inp dir = Some (chr, inp_adv) /\
      read_char (CdInv cd) inp dir = None.
Proof.
  intros ms inp chr cd charset rer dir inp_adv Hequiv Hcasesenst Hms_inp Hreadsuccess Hcharcorresp Hadv.
  destruct inp as [next pref].
  destruct dir.
  - destruct next as [|x next']. 1: discriminate.
    injection Hadv as <-. simpl.
    inversion Hms_inp as [str0 end_ind cap next2 pref2 Hlenpref Heqstr0 Heqms Heqnext2].
    subst next2 pref2 ms str0. simpl in *.
    rewrite List.Indexing.Int.of_nat in Hreadsuccess.
    apply List.Indexing.Nat.concat in Hreadsuccess.
    destruct Hreadsuccess as [ [Habs _] | [Hzero Hreadsuccess] ].
    1: { rewrite List.rev_length in Habs. lia. }
    rewrite List.rev_length in Hreadsuccess.
    replace (end_ind - length pref) with 0 in Hreadsuccess by lia.
    injection Hreadsuccess as <-.
    now setoid_rewrite char_match_warblre with (rer := rer).
  - destruct pref as [|x pref']. 1: discriminate.
    injection Hadv as <-. simpl.
    inversion Hms_inp as [str0 end_ind cap next2 pref2 Hlenpref Heqstr0 Heqms Heqnext2].
    subst next2 pref2 ms str0. simpl in *.
    destruct end_ind as [|end_indm1]. 1: discriminate.
    replace (Z.of_nat (S end_indm1) - 1)%Z with (Z.of_nat end_indm1) in Hreadsuccess by lia.
    rewrite List.Indexing.Int.of_nat in Hreadsuccess.
    apply List.Indexing.Nat.concat in Hreadsuccess.
    destruct Hreadsuccess as [ [Hlen Hreadsuccess] | [Habs _] ].
    2: { rewrite List.app_length, List.rev_length in Habs. simpl in *. lia. }
    injection Hlenpref as <-.
    unfold List.Indexing.Nat.indexing in Hreadsuccess.
    rewrite List.nth_error_app2 in Hreadsuccess. 2: { rewrite List.rev_length. reflexivity. }
    rewrite List.rev_length, Nat.sub_diag in Hreadsuccess.
    injection Hreadsuccess as <-.
    now setoid_rewrite char_match_warblre with (rer := rer).
Qed.


(* Same as char_match_warblre, but in the mismatching case. *)
Lemma char_mismatch_warblre:
  forall rer chr cd charset,
    equiv_cd_charset cd charset ->
    RegExpRecord.ignoreCase rer = false ->
    CharSet.exist_canonicalized rer charset (char_canonicalize rer chr) = false ->
    char_match chr cd = false.
Proof.
  intros rer chr cd charset Hequiv Hcasesenst Hexist_false.
  rewrite CharSet.exist_canonicalized_equiv in Hexist_false.
  rewrite charset_exist_false_iff in Hexist_false. specialize (Hexist_false chr).
  do 2 rewrite canonicalize_casesenst in Hexist_false by assumption.
  destruct Hexist_false.
  2: { rewrite EqDec.inversion_false in H. contradiction. }
  specialize (Hequiv chr). congruence.
Qed.

(* Same as above, but with inverted character descriptors. *)
Lemma char_mismatch_warblre_inv:
  forall rer chr cd charset,
    equiv_cd_charset cd charset ->
    RegExpRecord.ignoreCase rer = false ->
    CharSet.exist_canonicalized rer charset (char_canonicalize rer chr) = false ->
    char_match chr (CdInv cd) = true.
Proof.
  intros rer chr cd charset Hequiv Hcasesenst Hexist_false. simpl.
  apply <- Bool.negb_true_iff. eapply char_mismatch_warblre; eauto.
Qed.



(* Same as read_char_success, but in the mismatching case. *)
Lemma read_char_fail:
  forall rer ms chr inp inp_adv dir cd charset,
    equiv_cd_charset cd charset ->
    RegExpRecord.ignoreCase rer = false ->
    ms_matches_inp ms inp ->
    List.Indexing.Int.indexing (MatchState.input ms) (
        match dir with forward => MatchState.endIndex ms | backward => MatchState.endIndex ms - 1 end) = Success chr ->
    CharSet.exist_canonicalized rer charset (char_canonicalize rer chr) = false ->
    advance_input inp dir = Some inp_adv ->
    read_char cd inp dir = None /\
      read_char (CdInv cd) inp dir = Some (chr, inp_adv).
Proof.
  intros rer ms chr inp inp_adv dir cd charset Hequiv Hcasesenst Hms_inp Hreadsuccess Hnocorresp Hadv.
  destruct inp as [next pref].
  destruct ms as [str0 endInd cap].
  inversion Hms_inp as [s end_ind cap0 next0 pref0 Hlenpref Hmatches Heqs Heqend_ind].
  subst s cap0 pref0 next0 endInd. simpl in *.
  destruct dir.
  - destruct next as [|x next']. 1: discriminate.
    injection Hadv as <-.
    rewrite List.Indexing.Int.of_nat in Hreadsuccess.
    subst str0 end_ind.
    apply List.Indexing.Nat.concat in Hreadsuccess.
    destruct Hreadsuccess as [ [Habs _] | [_ Hreadsuccess] ].
    1: { rewrite List.rev_length in Habs. lia. }
    rewrite List.rev_length in Hreadsuccess.
    replace (length pref - length pref) with 0 in Hreadsuccess by lia.
    injection Hreadsuccess as <-.
    now setoid_rewrite char_mismatch_warblre with (rer := rer).
  - destruct pref as [|x pref']. 1: discriminate.
    injection Hadv as <-.
    destruct end_ind as [|end_indm1]. 1: discriminate.
    replace (Z.of_nat (S end_indm1) - 1)%Z with (Z.of_nat end_indm1) in Hreadsuccess by lia.
    rewrite List.Indexing.Int.of_nat in Hreadsuccess.
    injection Hlenpref as <-. subst str0.
    apply List.Indexing.Nat.concat in Hreadsuccess.
    destruct Hreadsuccess as [ [Hlen Hreadsuccess] | [Habs _] ].
    2: { rewrite List.rev_length in Habs. simpl in *. lia. }
    unfold List.Indexing.Nat.indexing in Hreadsuccess. simpl in *.
    rewrite List.nth_error_app2 in Hreadsuccess. 2: { rewrite List.rev_length. reflexivity. }
    rewrite List.rev_length, Nat.sub_diag in Hreadsuccess.
    injection Hreadsuccess as <-.
    now setoid_rewrite char_mismatch_warblre with (rer := rer).
Qed.
  

(* Advancing an input preserves compatibility with an input string. *)
Lemma advance_input_compat:
  forall inp dir str0 inp_adv,
    input_compat inp str0 ->
    advance_input inp dir = Some inp_adv ->
    input_compat inp_adv str0.
Proof.
  intros inp dir str0 inp_adv Hinpcompat Hadv.
  inversion Hinpcompat as [next pref str1 Hcompat Heqinp Heqstr1].
  subst str1 inp.
  destruct dir.
  - destruct next as [ | x next' ]. 1: discriminate.
    injection Hadv as <-.
    constructor.
    subst str0. simpl. rewrite <- List.app_assoc.
    reflexivity.
  - destruct pref as [ | x pref' ]. 1: discriminate.
    injection Hadv as <-.
    constructor.
    subst str0. simpl. rewrite <- List.app_assoc.
    reflexivity.
Qed.


(* Advancing a valid MatchState forward yields a valid MatchState when we remain in bounds. *)
(*Lemma ms_advance_valid:
  forall ms rer ms_adv,
    MatchState.Valid (MatchState.input ms) rer ms ->
    (MatchState.endIndex ms + 1 <= Z.of_nat (length (MatchState.input ms)))%Z ->
    ms_adv = advance_ms ms forward ->
    MatchState.Valid (MatchState.input ms_adv) rer ms_adv.
Proof.
  intros ms rer ms_adv [Honinp [Hiton [Hlencap Hcapvalid]]] Hinb Heqms_adv.
  destruct ms as [input endIndex cap].
  unfold advance_ms in Heqms_adv. simpl in Heqms_adv. subst ms_adv.
  simpl in *.
  split; [|split; [|split]]; try easy.
  unfold IteratorOn in *. simpl. lia.
Qed.*)


(* Advancing corresponding MatchStates and inputs yields corresponding MatchStates and inputs. *)
Lemma ms_matches_inp_adv:
  forall ms inp dir ms_adv inp_adv,
    ms_matches_inp ms inp ->
    ms_adv = advance_ms ms dir ->
    advance_input inp dir = Some inp_adv ->
    ms_matches_inp ms_adv inp_adv.
Proof.
  intros ms inp dir ms_adv inp_adv Hmatches Heqms_adv Hinp_adv.
  destruct ms as [input endIndex cap].
  destruct inp as [next pref].
  destruct dir.
  - destruct next as [|x next']. 1: discriminate.
    injection Hinp_adv as <-.
    unfold advance_ms in Heqms_adv. simpl in *. subst ms_adv.
    inversion Hmatches as [s end_ind cap1 next1 pref1 Hlenpref Hmatches' Heqs Heqend_ind].
    subst cap1 pref1 next1 s.
    replace (Z.of_nat end_ind + 1)%Z with (Z.of_nat (end_ind + 1)) by lia.
    constructor.
    + simpl. lia.
    + simpl. rewrite <- List.app_assoc. apply Hmatches'.
  - destruct pref as [|x pref']. 1: discriminate.
    injection Hinp_adv as <-.
    unfold advance_ms in Heqms_adv. simpl in *. subst ms_adv.
    inversion Hmatches as [s end_ind cap1 next1 pref1 Hlenpref Hmatches' Heqs Heqend_ind].
    subst cap1 pref1 next1 s.
    destruct end_ind as [|end_indm1]. 1: discriminate.
    replace (Z.of_nat (S end_indm1) - 1)%Z with (Z.of_nat end_indm1) by lia.
    constructor.
    + simpl in Hlenpref. lia.
    + simpl in Hmatches'. rewrite <- List.app_assoc in Hmatches'. simpl in Hmatches'. assumption.
Qed.


(* If a MatchState has advanced or regressed and corresponds to a new Linden input, then the current string of this Linden input is different from the suffix of the original MatchState. *)
Lemma endInd_neq_advanced:
  (* For all valid MatchStates ms and ms1 and Linden input inp' *)
  forall ms ms1 inp inp1 str0,
    ms_matches_inp ms inp -> input_compat inp str0 ->
    (* such that ms1 and inp' correspond, *)
    ms_matches_inp ms1 inp1 -> input_compat inp1 str0 ->
    (* and ms1 has advanced or regressed wrt ms, *)
    (MatchState.endIndex ms1 =? MatchState.endIndex ms)%Z = false ->
    (* the current input string of inp' is different from the suffix of ms. *)
    forall dir, current_str inp1 dir <> ms_suffix ms dir.
Proof.
  intros [input endInd cap] [input1 endInd1 cap1] [next pref] [next1 pref1] str0 Hmsinp Hinpcompat Hms1inp1 Hinp1compat HendInd_neq dir. simpl.
  inversion Hmsinp. inversion Hms1inp1. subst next2 pref2 next0 pref0 s s0 cap0 cap2.
  inversion Hinpcompat. inversion Hinp1compat. subst next0 pref0 str1 next2 pref2 str2.
  replace input with str0 in * by congruence. replace input1 with str0 in * by congruence. simpl in *.
  intro Habs. subst endInd endInd1.
  destruct dir.
  - erewrite <- ms_suffix_current_str in Habs by eauto. simpl in *.
    subst next1.
    rewrite Z.eqb_neq in HendInd_neq. assert (end_ind0 <> end_ind) by lia.
    apply (f_equal (@length Char)) in H5, H12. rewrite List.app_length, List.rev_length in H5, H12. lia.
  - erewrite <- ms_suffix_current_str in Habs by eauto. simpl in *.
    subst pref1.
    rewrite Z.eqb_neq in HendInd_neq. assert (end_ind0 <> end_ind) by lia.
    apply (f_equal (@length Char)) in H5, H12. rewrite List.app_length, List.rev_length in H5, H12. lia.
Qed.


(* If we are at the end of our input, this means that the suffix of our input is empty. *)
Lemma end_input_next_empty:
  forall (ms: MatchState) (inp: Chars.input),
    MatchState.endIndex ms = Z.of_nat (length (MatchState.input ms)) ->
    ms_matches_inp ms inp ->
    exists pref, inp = Input nil pref.
Proof.
  intros ms inp Hend Hmatches.
  inversion Hmatches as [s end_ind cap next pref Hlenpref Heqs Heqms Heqinp].
  subst ms. simpl in *.
  (*assert (Hoob': end_ind + 1 > length s) by lia.*)
  apply (f_equal (length (A := Chars.Char))) in Heqs.
  rewrite List.app_length in Heqs.
  rewrite List.rev_length in Heqs.
  assert (Hlen: end_ind = length s) by lia.
  assert (Hnext_zerolen: length next = 0) by lia.
  exists pref. f_equal.
  now apply List.length_zero_iff_nil.
Qed.

(* If we are NOT at the end of our input, then the suffix of our input is nonempty. *)
Lemma end_input_next_nonempty:
  forall (ms: MatchState) (inp: Chars.input),
    MatchState.endIndex ms <> Z.of_nat (length (MatchState.input ms)) ->
    ms_matches_inp ms inp ->
    exists pref x next, inp = Input (x::next) pref.
Proof.
  intros ms [next pref] Hnotend Hmatches. destruct next as [|x next].
  - inversion Hmatches as [s end_ind cap next' pref' Hlenpref Heqs Heqms Heqinp]. subst ms next' pref'. simpl in *.
    subst s. rewrite app_nil_r, rev_length in Hnotend. lia.
  - exists pref. exists x. exists next. reflexivity.
Qed.

(* If we try to read forward out of bounds from a valid state, then we are exactly at the end of the input. *)
Lemma read_oob_fail_atend:
  forall (ms: MatchState) (inp: Chars.input),
    (MatchState.endIndex ms + 1 > Z.of_nat (length (MatchState.input ms)))%Z ->
    ms_matches_inp ms inp ->
    MatchState.endIndex ms = Z.of_nat (length (MatchState.input ms)).
Proof.
  intros ms inp Hend Hmatches.
  pose proof ms_matches_inp_inbounds ms inp Hmatches. lia.
Qed.

(* Corollary: if we try to read forward out of bounds from a valid state, then the suffix of our input is empty. *)
Lemma read_oob_fail_end:
  forall (ms: MatchState) (inp: Chars.input),
    (MatchState.endIndex ms + 1 > Z.of_nat (length (MatchState.input ms)))%Z ->
    ms_matches_inp ms inp ->
    exists pref, inp = Input nil pref.
Proof.
  intros. eauto using end_input_next_empty, read_oob_fail_atend.
Qed.

(* If we are at the beginning of our input, this means that the prefix of our input is empty. *)
Lemma begin_input_pref_empty:
  forall (ms: MatchState) (inp: Chars.input),
    MatchState.endIndex ms = 0%Z ->
    ms_matches_inp ms inp ->
    exists next, inp = Input next nil.
Proof.
  intros ms inp Hbegin Hmatches.
  inversion Hmatches as [s end_ind cap next pref Hlenpref Heqs Heqms Heqinp].
  subst ms. simpl in *.
  (*assert (Hoob': end_ind + 1 > length s) by lia.*)
  apply (f_equal (length (A := Chars.Char))) in Heqs.
  rewrite List.app_length in Heqs.
  rewrite List.rev_length in Heqs.
  assert (Hlen: end_ind = 0) by lia. subst end_ind.
  exists next. f_equal.
  now apply List.length_zero_iff_nil.
Qed.

(* If we are NOT at the beginning of our input, this means that the prefix of our input is not empty. *)
Lemma begin_input_pref_nonempty:
  forall (ms: MatchState) (inp: Chars.input),
    MatchState.endIndex ms <> 0%Z ->
    ms_matches_inp ms inp ->
    exists next x pref, inp = Input next (x::pref).
Proof.
  intros ms [next pref] Hnotbegin Hmatches.
  destruct pref as [|x pref].
  - inversion Hmatches as [s end_ind cap next' pref' Hlenpref Heqs Heqms Heqinp]. subst ms pref' next'. simpl in *. lia.
  - exists next. exists x. exists pref. reflexivity.
Qed.

(* If we try to read backwards out of bounds from a valid state, then we are exactly at the beginning of the input. *)
Lemma read_oob_fail_atbegin:
  forall (ms: MatchState) (inp: Chars.input),
    (MatchState.endIndex ms - 1 < 0)%Z ->
    ms_matches_inp ms inp ->
    MatchState.endIndex ms = 0%Z.
Proof.
  intros ms inp Hend Hmatches.
  pose proof ms_matches_inp_inbounds ms inp Hmatches. lia.
Qed.

(* Corollary: if we try to read backwards out of bounds from a valid state, then the prefix of our input is empty. *)
Lemma read_oob_fail_begin:
  forall (ms: MatchState) (inp: Chars.input),
    (MatchState.endIndex ms - 1 < 0)%Z ->
    ms_matches_inp ms inp ->
    exists next, inp = Input next nil.
Proof.
  intros. eauto using begin_input_pref_empty, read_oob_fail_atbegin.
Qed.


(* If a MatchState matches some input, then its end index (plus one) cannot be negative. *)
Lemma endInd_neg_abs:
  forall (ms: MatchState) (inp: Chars.input),
    ms_matches_inp ms inp ->
    ~(MatchState.endIndex ms + 1 < 0)%Z.
Proof.
  intros ms inp Hmatches.
  inversion Hmatches as [s end_ind cap next pref Hlenpref Heqs Heqms Heqinp].
  subst ms. simpl in *.
  lia.
Qed.

(* If a MatchState matches some input, then its end index minus one cannot be greater than the length of the input string. *)
Lemma endInd_gtlen_abs:
  forall (ms: MatchState) (inp: Chars.input),
    ms_matches_inp ms inp ->
    ~(MatchState.endIndex ms - 1 > Z.of_nat (length (MatchState.input ms)))%Z.
Proof.
  intros ms inp Hmatches.
  inversion Hmatches as [s end_ind cap next pref Hlenpref Heqs Heqms Heqinp].
  subst ms. simpl in *.
  apply (f_equal (@length Chars.Char)) in Heqs. rewrite List.app_length, List.rev_length in Heqs.
  subst end_ind. lia.
Qed.

(* If we try to read forward out of bounds in the Warblre sense, then reading a character forward in the Linden sense fails. *)
Lemma read_oob_fail_end_bool:
  forall (ms: MatchState) (inp: Chars.input),
    ms_matches_inp ms inp ->
    ((MatchState.endIndex ms + 1 <? 0)%Z || (MatchState.endIndex ms + 1 >? Z.of_nat (length (MatchState.input ms)))%Z)%bool = true ->
    forall cd: char_descr, read_char cd inp forward = None.
Proof.
  intros ms inp Hmatches Hoob.
  apply Bool.orb_true_elim in Hoob.
  destruct Hoob as [Hoob|Hoob].
  - exfalso. rewrite Z.ltb_lt in Hoob. apply (endInd_neg_abs _ _ Hmatches Hoob).
  - rewrite Z.gtb_gt in Hoob.
    pose proof read_oob_fail_end ms inp Hoob Hmatches.
    destruct H as [pref H].
    subst inp. simpl. reflexivity.
Qed.

(* If we try to read backwards out of bounds in the Warblre sense, then reading a character backwards in the Linden sense fails. *)
Lemma read_oob_fail_begin_bool:
  forall (ms: MatchState) (inp: Chars.input),
    ms_matches_inp ms inp ->
    ((MatchState.endIndex ms - 1 <? 0)%Z || (MatchState.endIndex ms - 1 >? Z.of_nat (length (MatchState.input ms)))%Z)%bool = true ->
    forall cd: char_descr, read_char cd inp backward = None.
Proof.
  intros ms inp Hmatches Hoob.
  apply Bool.orb_true_elim in Hoob.
  destruct Hoob as [Hoob | Hoob].
  - rewrite Z.ltb_lt in Hoob.
    pose proof read_oob_fail_begin ms inp Hoob Hmatches.
    destruct H as [next H]. subst inp. simpl. reflexivity.
  - exfalso. rewrite Z.gtb_gt in Hoob. apply (endInd_gtlen_abs _ _ Hmatches Hoob).
Qed.

(* If we can read inbounds (in the Warblre sense), this means that we can successfully advance our input (in the Linden sense). *)
Lemma next_inbounds_nextinp:
  forall (ms: MatchState) (inp: Chars.input) (dir: Direction) (nextend: Z),
    ms_matches_inp ms inp ->
    nextend = (if (dir ==? forward)%wt then (MatchState.endIndex ms + 1)%Z else (MatchState.endIndex ms - 1)%Z) ->
    ((nextend <? 0)%Z || (nextend >? Z.of_nat (length (MatchState.input ms)))%Z)%bool = false ->
    exists inp', advance_input inp dir = Some inp'.
Proof.
  intros ms inp dir nextend Hmatches Heqnextend Hinb.
  inversion Hmatches as [s end_ind cap next pref Hlenpref Heqs Heqms Heqinp].
  subst ms. simpl in *.
  destruct dir; simpl in *.
  - destruct next as [|c next'].
    2: eexists; reflexivity.
    exfalso.
    apply Bool.orb_false_elim in Hinb.
    destruct Hinb as [_ Hinb].
    assert (Hinb': end_ind + 1 <= length s) by lia.
    apply (f_equal (length (A := Chars.Char))) in Heqs.
    rewrite List.app_length in Heqs.
    rewrite List.rev_length in Heqs.
    simpl in Heqs.
    lia.
  - destruct pref as [|c pref'].
    2: eexists; reflexivity.
    exfalso. simpl in Hlenpref. subst end_ind. simpl in *. lia.
Qed.

(* If wgreedylazy is equivalent to greedy, then compiling a corresponding quantifier yields the boolean greedy. *)
Lemma compilequant_greedy:
  forall (wquant: Patterns.QuantifierPrefix) (wgreedylazy: Patterns.QuantifierPrefix -> Patterns.Quantifier) (lquant: bool -> regex -> regex) (greedy: bool),
    equiv_greedylazy wgreedylazy greedy -> equiv_quantifier wquant lquant ->
    Semantics.CompiledQuantifier_greedy (Semantics.compileQuantifier (wgreedylazy wquant)) = greedy.
Proof.
  intros wquant wgreedylazy lquant greedy Hequivgreedy Hequivquant.
  inversion Hequivgreedy; inversion Hequivquant; reflexivity.
Qed.

(** ** Lemmas for word boundary matching *)

Lemma ifthenelse_xorb: forall a b: bool,
    ((a is true) && (b is false)) || ((a is false) && (b is true)) = xorb a b.
Proof.
  now intros [] [].
Qed.

Lemma ifthenelse_negb_xorb: forall a b: bool,
    ((a is true) && (b is true)) || ((a is false) && (b is false)) = negb (xorb a b).
Proof.
  now intros [] [].
Qed.

Lemma wordCharacters_casesenst:
  forall rer,
    RegExpRecord.ignoreCase rer = false ->
    Semantics.wordCharacters rer = Success Characters.ascii_word_characters.
Proof.
  intros rer Hcasesenst. unfold Semantics.wordCharacters.
  unfold Coercions.wrap_CharSet. simpl. f_equal.
  apply charset_ext. intro c.
  rewrite charset_union_contains, charset_filter_contains.
  destruct (CharSet.contains Characters.ascii_word_characters _) eqn:Hascii; simpl. 1: reflexivity.
  setoid_rewrite Hascii.
  rewrite canonicalize_casesenst by assumption. setoid_rewrite Hascii.
  rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma unwrap_bool:
  forall b: bool, (if b then Coercions.wrap_bool MatchError true else Coercions.wrap_bool MatchError false) = Success b.
Proof.
  now intros [].
Qed.

Lemma word_char_warblre:
  forall c, word_char c = CharSet.contains Characters.ascii_word_characters c.
Proof.
  intro c. unfold Characters.ascii_word_characters.
  apply Bool.eq_true_iff_eq.
  rewrite charset_from_list_contains. unfold word_char.
  apply Utils.List.inb_spec.
Qed.

Lemma is_boundary_xorb:
  forall inp ms a b rer,
    RegExpRecord.ignoreCase rer = false ->
    ms_matches_inp ms inp ->
    Semantics.isWordChar rer (MatchState.input ms) (MatchState.endIndex ms - 1)%Z = Success a ->
    Semantics.isWordChar rer (MatchState.input ms) (MatchState.endIndex ms) = Success b ->
    xorb a b = Semantics.is_boundary inp.
Proof.
  intros inp ms a b rer Hcasesenst Hmatches Ha Hb.
  unfold Semantics.isWordChar in *.
  rewrite wordCharacters_casesenst in * by assumption. simpl in *.
  inversion Hmatches as [str0 end_ind cap next pref Hlenpref Hstr0 Heqms Heqinp].
  subst ms inp. simpl in *.
  destruct (Z.of_nat end_ind - 1 =? -1)%Z eqn:Hbegin; destruct (Z.of_nat end_ind =? Z.of_nat (length _))%Z eqn:Hend; simpl in *.

  - (* Both at begin and end *)
    rewrite Bool.orb_true_r in Hb. injection Ha as <-. injection Hb as <-. simpl.
    replace end_ind with 0 in * by lia. assert (length str0 = 0) as Hstr0zerolen by lia.
    apply length_zero_iff_nil in Hlenpref, Hstr0zerolen. subst str0 pref. simpl in *. now subst next.

  - (* At begin but not at end *)
    replace (Z.of_nat end_ind =? -1)%Z with false in Hb by lia. simpl in Hb.
    assert (end_ind = 0) as Hbegin0 by lia.
    rewrite Hbegin0 in Hlenpref. apply length_zero_iff_nil in Hlenpref. subst pref. simpl in *.
    destruct List.Indexing.Int.indexing as [c|] eqn:Hgetchr; simpl in *. 2: discriminate.
    pose proof ms_matches_inp_currchar _ _ _ Hmatches Hgetchr as [_ [pref [next' Hinput]]].
    injection Hinput as Heqpref Heqnext. subst next str0.
    rewrite unwrap_bool in Hb. injection Hb as <-. injection Ha as <-. simpl.
    symmetry. apply word_char_warblre.

  - (* At end but not at begin *)
    rewrite Bool.orb_true_r in Hb. simpl in Hb.
    replace (Z.of_nat _ - 1 =? _)%Z with false in Ha by lia.
    destruct List.Indexing.Int.indexing as [cl|] eqn:Hcl in Ha; simpl in *. 2: discriminate.
    pose proof ms_matches_inp_prevchar _ _ _ Hmatches Hcl as [pref' [next0 Heqinp]]. injection Heqinp as Heqnext0 Heqpref. subst next0 pref.
    replace next with (@nil Char) in *.
    2: {
      symmetry. apply length_zero_iff_nil. apply (f_equal (@length Char)) in Hstr0. rewrite app_length, rev_length in Hstr0. lia.
    }
    injection Hb as <-. rewrite unwrap_bool in Ha. injection Ha as <-.
    rewrite Bool.xorb_false_r. symmetry. apply word_char_warblre.

  - (* Neither at begin, nor at end *)
    replace (Z.of_nat _ =? -1)%Z with false in Hb by lia. simpl in Hb.
    rewrite Z.eqb_neq in Hend. pose proof ms_matches_inp_inbounds _ _ Hmatches as Hinb. simpl in Hinb.
    replace (Z.of_nat end_ind - 1 =? Z.of_nat (length str0))%Z with false in Ha by lia.
    destruct List.Indexing.Int.indexing as [cr|] eqn:Hcr in Hb; simpl in *. 2: discriminate.
    destruct List.Indexing.Int.indexing as [cl|] eqn:Hcl in Ha; simpl in *. 2: discriminate.
    pose proof ms_matches_inp_currchar _ _ _ Hmatches Hcr as [_ [pref0 [next' Heqinpr]]].
    pose proof ms_matches_inp_prevchar _ _ _ Hmatches Hcl as [pref' [next0 Heqinpl]].
    injection Heqinpr as Heqnext _. injection Heqinpl as _ Heqpref. subst next pref. clear pref0 next0.
    rewrite unwrap_bool in Hb, Ha. injection Hb as <-. injection Ha as <-.
    rewrite Bool.xorb_comm. f_equal; symmetry; apply word_char_warblre.
Qed.
