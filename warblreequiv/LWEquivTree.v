From Linden Require Import TMatching Tree Chars Semantics MSInput
  Regex LindenParameters CharsWarblre RegexpTranslation ListLemmas
  WarblreLemmas.
From Warblre Require Import Result Notation RegExpRecord Match Base
  Patterns Node NodeProps Semantics.
From Coq Require Import List ZArith Lia.
Import Notation.
Import Result.Notations.
Import Match.MatchState.
Import ListNotations.
Import Patterns.
Import Zipper.
Import Zipper.Down.

Local Open Scope result_flow.

(* `tMC_is_tree tmc rer cont inp` means that the TMatcherContinuation tmc, when run with a MatchState
  compatible with input inp and valid with respect to rer, performs the actions in the continuation cont and yields a valid backtree. *)
Definition tMC_is_tree (tmc: TMatcherContinuation) (rer: RegExpRecord) (cont: continuation) (inp: input) :=
  forall (ms: MatchState) (t: tree), Valid (MatchState.input ms) rer ms -> ms_matches_inp ms inp -> tmc ms = Success t -> is_tree Epsilon cont inp t.

(* `tMC_valid tmc rer cont str0` means that the TMatcherContinuation tmc, when run on any input compatible with the string str0 under the flags in rer,
   performs the actions in the continuation cont and yields a valid backtree. *)
Definition tMC_valid (tmc: TMatcherContinuation) (rer: RegExpRecord) (cont: continuation) (str0: string) :=
  forall inp, input_compat inp str0 -> tMC_is_tree tmc rer cont inp.

(* `tm_valid tm rer lreg` means that under the given RegExpRecord (set of flags), the TMatcher tm recognizes the regexp lreg on any input, and yields a valid backtree. *)
Definition tm_valid (tm: TMatcher) (rer: RegExpRecord) (lreg: regex) :=
  forall (tmc: TMatcherContinuation) (cont: continuation) (str0: string),
  tMC_valid tmc rer cont str0 ->
  tMC_valid (fun s => tm s tmc) rer (Areg lreg::cont) str0.

Lemma tRepeatMatcher'_valid:
  forall rer greedy parenIndex parenCount,
  forall (tm: TMatcher) (lreg: regex),
    tm_valid tm rer lreg -> def_groups lreg = List.seq (parenIndex + 1) parenCount ->
    forall fuel, tm_valid (fun s tmc => tRepeatMatcher' tm 0 +∞ greedy s tmc parenIndex parenCount fuel) rer (Regex.Star greedy lreg).
Proof.
  (* We fix all of the following: in particular, we fix the regexp that is being starred as well as its context in terms of parentheses before. *)
  intros rer greedy parenIndex parenCount tm lreg Htm_valid Hgroups_valid fuel.
  induction fuel as [|fuel IHfuel].
  - (* When the fuel is zero, tRepeatMatcher' never yields a tree, so there is nothing to prove. *)
    simpl. unfold tm_valid, tMC_valid, tMC_is_tree. discriminate.
  - (* Assume that the matcher yielded by tRepeatMatcher' with fuel fuel is valid, and let's prove it for fuel+1. *)
    unfold tm_valid in *.
    intros tmc cont str0 Htmc_valid.
    unfold tMC_valid.
    intros inp Hinp_compat.
    unfold tMC_is_tree.
    intros ms t Hvalidms Hms_inp HmatchSuccess.
    simpl in *.
    (* Assume that the capture reset succeeds, otherwise there is nothing to prove. *)
    destruct List.List.Update.Nat.Batch.update as [cap'|] eqn:Heqcap'; simpl in *. 2: discriminate.
    destruct greedy.
    + (* Greedy star *)
      (* tmc' checks at the end of matching lreg whether progress has been made, and if so calls tRepeatMatcher' with one less fuel *)
      remember (fun y => if (_ =? _)%Z then _ else _) as tmc'.
      (* ms' is ms with the capture reset *)
      remember (match_state _ _ cap') as ms'.
      assert (tMC_valid tmc' rer (Acheck (ms_suffix ms)::Areg (Regex.Star true lreg)::cont) str0) as Htmc'_valid.
      {
        unfold tMC_valid.
        (* Let inp' be an input compatible with str0. *)
        intros inp' Hinp'_compat.
        unfold tMC_is_tree.
        (* Let ms1 be a MatchState that is valid and matches that input. *)
        intros ms1 t1 Hms1valid Hms1_inp Htmc'_succeeds.
        rewrite Heqtmc' in Htmc'_succeeds.
        (* Then either the input has progressed or it has not. *)
        destruct (_ =? _)%Z eqn:Heqcheck.
        - (* Case 1: the input has not progressed *)
          inversion Htmc'_succeeds as [Heqt1]. apply tree_pop_check_fail.
          rewrite ms_suffix_current_str with (ms := ms1) by assumption.
          unfold ms_suffix.
          rewrite Z.eqb_eq in Heqcheck.
          rewrite Heqcheck.
          f_equal.
          eapply inp_compat_ms_same_inp with (inp1 := inp') (inp2 := inp).
          + apply Hinp'_compat.
          + apply Hinp_compat.
          + assumption.
          + assumption.
        - (* Case 2: the input has progressed *)
          destruct tRepeatMatcher' as [subtree|] eqn:Heqsubtree; simpl.
          2: discriminate.
          inversion Htmc'_succeeds as [Htmc'_succeds'].
          apply tree_pop_check.
          + rewrite ms_suffix_current_str with (ms := ms1). 2: assumption.
            intro Habs.
            unfold ms_suffix in Habs.
            assert (Hms1_ms_inp: @MatchState.input Chars.Char
                                   char_marker ms1 = MatchState.input ms) by
              now apply inp_compat_ms_same_inp
                with (str0 := str0) (inp1 := inp') (inp2 := inp).
            rewrite Hms1_ms_inp in Habs.
            change Character with Chars.Char in *.
            change (@Parameters.character_marker LindenParameters)
                with char_marker in *.
            (* Need to prove: skipn (Z.to_nat (MatchState.endIndex
  ms1)) _ = skipn (Z.to_nat (MatchState.endIndex ms)) _ implies
  Z.to_nat (_ ms1) = Z.to_nat (_ ms), because both are less than the
  length of MatchState.input ms by validity of the match states. Then
  again by validity of the match states, the end indices are
  non-negative, so they are equal. *)
            assert (Hindices_eq: MatchState.endIndex ms1
                                 = MatchState.endIndex ms). {
              Search Match.IteratorOn.
              pose proof valid_inv_iteratoron _ _ _ Hms1valid as
                Hms1_iton.
              pose proof valid_inv_iteratoron _ _ _ Hvalidms as
                Hms_iton.
              unfold Match.IteratorOn in Hms1_iton, Hms_iton.
              change (@MatchState.input Character
                        (@Parameters.character_marker LindenParameters
                        ) ms1) with (@MatchState.input Chars.Char
                                       char_marker ms1) in Hms1_iton.
              rewrite Hms1_ms_inp in Hms1_iton.
              change Character with Chars.Char in *.
              change (@Parameters.character_marker LindenParameters)
                with char_marker in *.
              apply skipn_ind_inv with (l := MatchState.input ms).
              1-4: lia.
              apply Habs.
            }
            rewrite Z.eqb_neq in Heqcheck.
            contradiction.
          + specialize (IHfuel tmc cont str0 Htmc_valid).
            unfold tMC_valid in IHfuel.
            specialize (IHfuel inp' Hinp'_compat).
            unfold tMC_is_tree in IHfuel.
            specialize (IHfuel ms1 subtree Hms1valid Hms1_inp Heqsubtree).
            apply IHfuel.
      }
      specialize (Htm_valid tmc' (Acheck (ms_suffix ms)::Areg (Regex.Star true lreg)::cont) str0 Htmc'_valid).
      unfold tMC_valid in Htm_valid, Htmc_valid.
      specialize (Htm_valid inp Hinp_compat).
      specialize (Htmc_valid inp Hinp_compat).
      unfold tMC_is_tree in Htm_valid, Htmc_valid.
      (* StrictlyNullable.capture_reset_preserve_validity *)
      assert (Valid (MatchState.input ms') rer ms') as Hvalidms'. {
        rewrite Heqms'. simpl.
        now apply @capture_reset_preserve_validity with (specParameters := LindenParameters) (parenIndex := parenIndex) (parenCount := parenCount).
      }
      assert (ms_matches_inp ms' inp) as Hms'_inp.
      {
        rewrite Heqms'.
        inversion Hms_inp.
        simpl.
        now constructor.
      }
      destruct tm as [z|] eqn:Heqz; simpl. 2: discriminate.
      destruct tmc as [z'|] eqn:Heqz'; simpl. 2: discriminate.
      specialize (Htm_valid ms' z Hvalidms' Hms'_inp Heqz).
      specialize (Htmc_valid ms z' Hvalidms Hms_inp Heqz').
      apply tree_pop_reg.
      eapply tree_star.
      * symmetry. apply Hgroups_valid.
      * rewrite ms_suffix_current_str with (ms := ms). 2: assumption.
        inversion Htm_valid.
        apply TREECONT.
      * apply Htmc_valid.
      * inversion HmatchSuccess. reflexivity.

    (* Lazy star *)
    + (* Likely similar; TODO do it! *)
      admit.
Admitted.



(* Theorem is not true for case-insensitive matching, which is not supported (yet) by the tree semantics *)
(* Validity of the context and regexp? *)
Theorem tmatcher_bt:
  forall (rer: RegExpRecord) (lroot: regex) (wroot: Regex)
    (Hcasesenst: RegExpRecord.ignoreCase rer = false)
    (root_equiv: equiv_regex wroot lroot),
  forall (wreg: Regex) (lreg: regex) ctx,
    equiv_regex wreg lreg ->
    Root wroot (wreg, ctx) ->
  forall tm,
    tCompileSubPattern wreg ctx rer forward = Success tm ->
    tm_valid tm rer lreg.
Proof.
  intros rer lroot wroot Hcasesenst root_equiv wreg lreg ctx Hequiv.
  revert ctx.
  induction Hequiv as [
    n |
    n c |
    n |
    n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
    n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
    n wr lr Hequiv IH |
    n wr lr Hequiv IH |
    name n wr lr Hequiv IH
  ].


  - (* Empty *)
    simpl. intros _ _.
    intros tm Hcompsucc tmc cont str0 Htmc_tree inp Hinp_compat.
    inversion Hcompsucc as [Hcompsucc'].
    intros ms t Hvalidms Hms_inp Htmc_succ.
    apply tree_pop_reg. unfold tMC_valid, tMC_is_tree in Htmc_tree.
    now apply Htmc_tree with (ms := ms).


  - (* Character *)
    simpl.
    intro ctx.
    intros Hroot tm Hcompile_succ tmc cont str0 Htmc_tree inp Hinp_compat.
    intros ms t Hmsvalid Hms_inp Htm_succ.
    inversion Hcompile_succ as [Hcompile_succ'].
    clear Hcompile_succ.
    subst tm.
    unfold tCharacterSetMatcher in Htm_succ.
    simpl in Htm_succ.
    set (next_outofbounds := ((_ <? 0)%Z || _)%bool) in Htm_succ.
    destruct next_outofbounds eqn:Hoob; simpl.
    + inversion Htm_succ as [Htm_succ'].
      apply tree_pop_reg.
      apply tree_char_fail.
      (* Reading out of bounds fails *)
      admit.
    + replace (Z.min _ _) with (@MatchState.endIndex Chars.Char char_marker ms) in Htm_succ by lia.
      (* If we are in bounds, then getting the character should succeed. Since we don't prove anything in the case of errors, we just assume this here *)
      destruct List.List.Indexing.Int.indexing as [chr|err] eqn:Hgetchr; simpl in *.
      -- (* Either the character is equal to the character in the regex, or it is not. *)
        destruct CharSet.exist_canonicalized eqn:Hcharmatch; simpl in *.
        ++ (* Case 1: it is equal. *)
          (* We then want to prove that we have a read success. *)
          apply tree_pop_reg.
          (* We first need to replace t with Success (Read chr child). *)
          remember (match_state _ _ _) as ms_adv in Htm_succ.
          unfold tMC_valid, tMC_is_tree in Htmc_tree.
          destruct (tmc ms_adv) as [child|] eqn:Htmc_succ; simpl in *. 2: discriminate.
          inversion Htm_succ as [Htm_succ'].

          (* Now we apply tree_char with the next input, whose existence we need to prove. *)
          set (inp_adv_opt := advance_input inp).
          destruct inp_adv_opt as [inp_adv|] eqn:Heqinp_adv.
          2: { exfalso; admit. }
          apply tree_char with (nextinp := inp_adv).
          ** (* Reading the character succeeds indeed *)
            admit.
          ** (* The subtree is valid. *)
            apply Htmc_tree with (ms := ms_adv).
            all: admit.
        ++ (* Case 2: it is not equal. *)
          admit.
      -- discriminate.

    (* Dot *)
  - admit.


  - (* Disjunction *)
    intro ctx.
    simpl in *.
    intro Hroot.
    remember (@Disjunction_left LindenParameters wr2 :: ctx) as ctx1.
    remember (@Disjunction_right LindenParameters wr1 :: ctx) as ctx2.
    specialize (IH1 ctx1).
    specialize (IH2 ctx2).
    assert (Root wroot (wr1, ctx1)) as Hroot1.
    {
      rewrite Heqctx1.
      apply same_root_down0 with (r1 := Disjunction wr1 wr2) (ctx1 := ctx).
      - apply (@Down_Disjunction_left LindenParameters).
      - apply Hroot.
    }
    assert (Root wroot (wr2, ctx2)) as Hroot2.
    {
      apply same_root_down0 with (r1 := Disjunction wr1 wr2) (ctx1 := ctx).
      - rewrite Heqctx2. apply (@Down_Disjunction_right LindenParameters).
      - apply Hroot.
    }
    specialize (IH1 Hroot1).
    specialize (IH2 Hroot2).
    intros tm Hcompsucc.
    destruct (tCompileSubPattern wr1 ctx1 rer forward) as [tm1|]
      eqn:Htm1; simpl. 2: discriminate.
    destruct (tCompileSubPattern wr2 ctx2 rer forward) as [tm2|] eqn:Htm2;
      simpl. 2: discriminate.
    simpl in Hcompsucc.
    inversion Hcompsucc as [Hcompsucc'].
    intros tmc cont str0 Htmc_tree inp Hinp_compat.
    intros s t Hsvalid Hs_inp Heqt.
    specialize (IH1 tm1 eq_refl tmc cont str0 Htmc_tree inp Hinp_compat).
    specialize (IH2 tm2 eq_refl tmc cont str0 Htmc_tree inp Hinp_compat).
    destruct (tm1 s tmc) as [t1|] eqn:Heqt1; simpl. 2: discriminate.
    destruct (tm2 s tmc) as [t2|] eqn:Heqt2; simpl. 2: discriminate.
    specialize (IH1 s t1 Hsvalid Hs_inp).
    specialize (IH2 s t2 Hsvalid Hs_inp).
    simpl in *.
    rewrite Heqt1 in IH1.
    rewrite Heqt2 in IH2.
    apply tree_pop_reg.
    inversion Heqt as [Heqt'].
    specialize (IH1 eq_refl).
    specialize (IH2 eq_refl).
    inversion IH1.
    inversion IH2.
    now apply tree_disj.
    (* DONE! 🎉 *)


  - (* Sequence *)
    intro ctx.
    simpl in *.
    intros Hroot tm Hcompsucc.
    remember (@Seq_left LindenParameters wr2 :: ctx) as ctx1.
    remember (@Seq_right LindenParameters wr1 :: ctx) as ctx2.
    specialize (IH1 ctx1).
    specialize (IH2 ctx2).
    assert (Root wroot (wr1, ctx1)) as Hroot1.
    {
      apply same_root_down0 with (r1 := Seq wr1 wr2) (ctx1 := ctx).
      - rewrite Heqctx1. apply (@Down_Seq_left LindenParameters).
      - apply Hroot.
    }
    assert (Root wroot (wr2, ctx2)) as Hroot2.
    {
      apply same_root_down0 with (r1 := Seq wr1 wr2) (ctx1 := ctx).
      - rewrite Heqctx2. apply (@Down_Seq_right LindenParameters).
      - apply Hroot.
    }
    specialize (IH1 Hroot1).
    specialize (IH2 Hroot2).
    destruct (tCompileSubPattern wr1 ctx1 rer forward) as [tm1|] eqn:Htm1;
      simpl. 2: discriminate.
    destruct (tCompileSubPattern wr2 ctx2 rer forward) as [tm2|] eqn:Htm2;
      simpl. 2: discriminate.
    specialize (IH1 tm1 eq_refl).
    specialize (IH2 tm2 eq_refl).
    intros tmc cont str0 Htmc_tree inp Hinp_compat.
    unfold tMC_is_tree.
    intros ms t Hmsvalid Hms_inp Heqt.
    simpl in Hcompsucc.
    inversion Hcompsucc as [Hcompsucc'].
    rewrite <- Hcompsucc' in Heqt.
    remember (fun s1 => tm2 s1 tmc) as tmc2.
    assert (tMC_valid tmc2 rer (Areg lr2::cont) str0) as Htmc2_tree.
    {
      intros inp' Hinp'_compat.
      rewrite Heqtmc2.
      unfold tm_valid, tMC_valid in IH2.
      now apply IH2 with (str0 := str0).
    }
    specialize (IH1 tmc2 (Areg lr2 :: cont) str0 Htmc2_tree inp Hinp_compat).
    unfold tMC_is_tree in IH1.
    specialize (IH1 ms t Hmsvalid Hms_inp Heqt).
    apply tree_pop_reg.
    inversion IH1.
    now apply tree_sequence.
    (* DONE! 🎉 *)


  - (* Lazy star *)
    intros ctx Hroot.
    simpl.
    intros tm Hcompsucc.
    destruct tCompileSubPattern as [m|] eqn:Heqm; simpl. 2: discriminate.
    inversion Hcompsucc as [Hcompsucc'].
    intros tmc cont str0 Htmc_valid.
    remember (StaticSemantics.countLeftCapturingParensBefore _ ctx) as parenIndex.
    remember (StaticSemantics.countLeftCapturingParensWithin _ _) as parenCount.
    pose proof tRepeatMatcher'_valid rer false parenIndex parenCount m lr as Hrepeat.
    specialize (IH (Quantified_inner (Lazy Star)::ctx)).
    assert (Root wroot (wr, Quantified_inner (Lazy Star)::ctx)) as Hroot1 by
      eauto using same_root_down0, Down_Quantified_inner.
    specialize (IH Hroot1).
    rewrite Heqm in IH.
    specialize (IH m eq_refl).
    specialize (Hrepeat IH).
    assert (def_groups lr = seq (parenIndex + 1) parenCount) as Hgroups_valid by admit.
    specialize (Hrepeat Hgroups_valid).
    intros inp Hinp_compat.
    intros s t Hvalids Hs_inp Heqt.
    specialize (Hrepeat (Semantics.repeatMatcherFuel 0 s)).
    specialize (Hrepeat tmc cont str0 Htmc_valid).
    simpl in Hrepeat.
    specialize (Hrepeat inp Hinp_compat s t Hvalids Hs_inp Heqt).
    apply Hrepeat.

    (* Greedy star: copy-pasting... *)
  - intros ctx Hroot.
    simpl.
    intros tm Hcompsucc.
    destruct tCompileSubPattern as [m|] eqn:Heqm; simpl. 2: discriminate.
    inversion Hcompsucc as [Hcompsucc'].
    intros tmc cont str0 Htmc_valid.
    remember (StaticSemantics.countLeftCapturingParensBefore _ ctx) as parenIndex.
    remember (StaticSemantics.countLeftCapturingParensWithin _ _) as parenCount.
    pose proof tRepeatMatcher'_valid rer true parenIndex parenCount m lr as Hrepeat.
    specialize (IH (Quantified_inner (Greedy Star)::ctx)).
    assert (Root wroot (wr, Quantified_inner (Greedy Star)::ctx)) as Hroot1 by
      eauto using same_root_down0, Down_Quantified_inner.
    specialize (IH Hroot1).
    rewrite Heqm in IH.
    specialize (IH m eq_refl).
    specialize (Hrepeat IH).
    assert (def_groups lr = seq (parenIndex + 1) parenCount) as Hgroups_valid by admit.
    specialize (Hrepeat Hgroups_valid).
    intros inp Hinp_compat.
    intros s t Hvalids Hs_inp Heqt.
    specialize (Hrepeat (Semantics.repeatMatcherFuel 0 s)).
    specialize (Hrepeat tmc cont str0 Htmc_valid).
    simpl in Hrepeat.
    specialize (Hrepeat inp Hinp_compat s t Hvalids Hs_inp Heqt).
    apply Hrepeat.


  - (* Group *)
    intros ctx Hroot. simpl.
    intros tm Hcompsucc.
    remember (@Group_inner LindenParameters _ :: ctx) as rctx.
    specialize (IH rctx).
    assert (Root wroot (wr, rctx)) as Hrootr.
    {
      eapply same_root_down0.
      - subst rctx. apply (@Down_Group_inner LindenParameters).
      - apply Hroot.
    }
    specialize (IH Hrootr).
    destruct (tCompileSubPattern wr rctx rer forward) as [mr|] eqn:Heqmr
    ; simpl. 2: discriminate.
    specialize (IH mr eq_refl).
    simpl in Hcompsucc.
    inversion Hcompsucc as [Hcompsucc'].
    clear Hcompsucc Hcompsucc'.
    intros tmc cont str0 Htmc_tree inp Hinp_compat.
    intros ms t Hvalidms Hms_inp Heqt.
    remember (fun y: MatchState => _) as tmc2 in Heqt.
    specialize (IH tmc2 (Aclose (S n) :: cont)).
    assert (StaticSemantics.countLeftCapturingParensBefore (Group name wr) ctx + 1 = S n) as Heqid by admit.
    assert (tMC_valid tmc2 rer (Aclose (S n) :: cont) str0) as Htmc2_tree.
    {
      intros inp' Hinp'_compat.
      rewrite Heqtmc2.
      unfold tMC_is_tree.
      intros ms' subtree Hms'valid Hms'_inp Heqsubtree.
      destruct negb; simpl in *. 1: discriminate.
      rewrite Heqid in Heqsubtree.
      replace ((S n) =? 0) with false in Heqsubtree.
      2: {
        symmetry.
        rewrite Nat.eqb_neq.
        lia.
      }
      destruct (List.List.Update.Nat.One.update) as [cap|]; simpl in *. 2: discriminate.
      specialize (Htmc_tree inp' Hinp'_compat).
      unfold tMC_is_tree in Htmc_tree.
      remember (match_state _ _ cap) as ms''.
      specialize (Htmc_tree ms'').
      assert (Valid (MatchState.input ms'') rer ms'') as Hs''valid by admit. (* not entirely sure that this is actually true *)
      destruct (tmc ms'') as [subtree'|] eqn:Heqsubtree'; simpl in *.
      2: discriminate.
      inversion Heqsubtree as [Heqsubtree0].
      specialize (Htmc_tree subtree' Hs''valid).
      assert (ms_matches_inp ms'' inp') as Hs''_inp' by admit.
      specialize (Htmc_tree Hs''_inp' eq_refl).
      apply tree_pop_close.
      assumption.
    }
    specialize (IH str0 Htmc2_tree).
    apply tree_pop_reg.
    unfold tMC_valid in IH.
    specialize (IH inp Hinp_compat ms).
    destruct (mr ms tmc2) as [subtree|] eqn:Heqsubtree; simpl in *.
    2: discriminate.
    inversion Heqt as [Heqt'].
    rewrite Heqid.
    apply tree_group.
    specialize (IH subtree Hvalidms Hms_inp eq_refl).
    inversion IH.
    assumption.
Admitted.
