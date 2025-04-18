From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List Program.Wf.
From Linden Require Import Tree LindenParameters CharsWarblre TMatching Chars Regex Semantics RegexpTranslation MSInput.
From Warblre Require Import Patterns Result Notation Errors Node RegExpRecord Base Coercions Semantics Typeclasses NodeProps.
From Warblre.props Require Import Match.
Import Match.MatchState.
Import Patterns.
Import Result.Result.
Import Result.Notations.
Import Result.Notations.Boolean.
Import Coercions.
Import Notation.
Import NodeProps.
Import Zipper.
Import Down.

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
            replace (@MatchState.input Chars.Char char_marker ms1) with (MatchState.input ms) in Habs.
            2: now apply inp_compat_ms_same_inp with (str0 := str0) (inp1 := inp) (inp2 := inp').
          (* Need to prove: skipn (Z.to_nat (MatchState.endIndex ms1)) _ = skipn (Z.to_nat (MatchState.endIndex ms)) _ implies Z.to_nat (_ ms1) = Z.to_nat (_ ms), because both are less than the length of MatchState.input ms by validity of the match states. Then again by validity of the match states, the end indices are non-negative, so they are equal. *)
            admit.
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
      assert (Valid (MatchState.input ms') rer ms') as Hvalidms' by admit.
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
    set (next_outofbounds := (_ <? 0)%Z || _) in Htm_succ.
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
    destruct (tCompileSubPattern wr1 ctx1 rer forward) as [tm1|] eqn:Htm1; simpl; try exact I.
    destruct (tCompileSubPattern wr2 ctx2 rer forward) as [tm2|] eqn:Htm2; simpl; try exact I.
    intros tmc regc cont Htmc_tree inp Hinp_compat.
    unfold tMC_is_tree.
    intros s Hsvalid Hs_inp.
    specialize (IH1 tmc regc cont Htmc_tree inp Hinp_compat).
    specialize (IH2 tmc regc cont Htmc_tree inp Hinp_compat).
    unfold tMC_is_tree in IH1, IH2.
    specialize (IH1 s Hsvalid Hs_inp).
    specialize (IH2 s Hsvalid Hs_inp).
    destruct (tm1 s tmc) as [t1|] eqn:Heqt1; simpl; try exact I.
    destruct (tm2 s tmc) as [t2|] eqn:Heqt2; simpl; try exact I.
    now apply tree_disj.
    (* DONE! 🎉 *)


  - (* Sequence *)
    intro ctx.
    simpl in *.
    intro Hroot.
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
    destruct (tCompileSubPattern wr1 ctx1 rer forward) as [tm1|] eqn:Htm1; simpl; try exact I.
    destruct (tCompileSubPattern wr2 ctx2 rer forward) as [tm2|] eqn:Htm2; simpl; try exact I.
    intros tmc regc cont Htmc_tree inp Hinp_compat.
    unfold tMC_is_tree.
    intros s Hsvalid Hs_inp.
    remember (fun s1 => tm2 s1 tmc) as tmc2.
    assert (forall inp': input, input_compat inp' -> tMC_is_tree tmc2 lr2 (Areg regc :: cont) inp') as Htmc2_tree.
    {
      intros inp' Hinp'_compat.
      rewrite Heqtmc2.
      now apply IH2.
    }
    specialize (IH1 tmc2 lr2 (Areg regc :: cont) Htmc2_tree inp Hinp_compat).
    unfold tMC_is_tree in IH1.
    specialize (IH1 s Hsvalid Hs_inp).
    destruct (tm1 s tmc2) as [t|] eqn:Heqt; simpl; try exact I.
    now apply tree_sequence.
    (* DONE! 🎉 *)


  - (* Lazy star *)
    intros ctx Hroot.
    simpl.
    destruct tCompileSubPattern as [m|] eqn:Heqm; simpl. 2: exact I.
    intros tmc regc cont Htmc_valid.
    pose proof tRepeatMatcher'_valid false (StaticSemantics.countLeftCapturingParensBefore wr ctx)
    (StaticSemantics.countLeftCapturingParensWithin wr (Quantified_inner (Lazy Star) :: ctx)) m lr as Hrepeat.
    specialize (IH (Quantified_inner (Lazy Star)::ctx)).
    assert (Root wroot (wr, Quantified_inner (Lazy Star)::ctx)) as Hroot1 by
      eauto using same_root_down0, Down_Quantified_inner.
    specialize (IH Hroot1).
    rewrite Heqm in IH.
    specialize (Hrepeat IH).
    remember (StaticSemantics.countLeftCapturingParensBefore _ ctx) as parenIndex.
    remember (StaticSemantics.countLeftCapturingParensWithin _ _) as parenCount.
    assert (def_groups lr = seq (parenIndex + 1) parenCount) as Hgroups_valid by admit.
    specialize (Hrepeat Hgroups_valid).
    unfold tMC_valid.
    intros inp Hinp_compat.
    unfold tMC_is_tree.
    intros s Hvalids Hs_inp.
    specialize (Hrepeat (Semantics.repeatMatcherFuel 0 s)).
    unfold tm_valid in Hrepeat.
    specialize (Hrepeat tmc regc cont Htmc_valid).
    now apply Hrepeat.

    (* Greedy star: copy-pasting... *)
  - intros ctx Hroot.
    simpl.
    destruct tCompileSubPattern as [m|] eqn:Heqm; simpl. 2: exact I.
    intros tmc regc cont Htmc_valid.
    pose proof tRepeatMatcher'_valid true (StaticSemantics.countLeftCapturingParensBefore wr ctx)
    (StaticSemantics.countLeftCapturingParensWithin wr (Quantified_inner (Greedy Star) :: ctx)) m lr as Hrepeat.
    specialize (IH (Quantified_inner (Greedy Star)::ctx)).
    assert (Root wroot (wr, Quantified_inner (Greedy Star)::ctx)) as Hroot1.
    {
      eapply same_root_down0.
      - apply (@Down_Quantified_inner LindenParameters).
      - apply Hroot.
    }
    specialize (IH Hroot1).
    rewrite Heqm in IH.
    specialize (Hrepeat IH).
    remember (StaticSemantics.countLeftCapturingParensBefore _ ctx) as parenIndex.
    remember (StaticSemantics.countLeftCapturingParensWithin _ _) as parenCount.
    assert (def_groups lr = seq (parenIndex + 1) parenCount) as Hgroups_valid by admit.
    specialize (Hrepeat Hgroups_valid).
    unfold tMC_valid.
    intros inp Hinp_compat.
    unfold tMC_is_tree.
    intros s Hvalids Hs_inp.
    specialize (Hrepeat (Semantics.repeatMatcherFuel 0 s)).
    unfold tm_valid in Hrepeat.
    specialize (Hrepeat tmc regc cont Htmc_valid).
    now apply Hrepeat.


  - (* Group *)
    intros ctx Hroot. simpl.
    remember (@Group_inner LindenParameters _ :: ctx) as rctx.
    specialize (IH rctx).
    assert (Root wroot (wr, rctx)) as Hrootr.
    {
      eapply same_root_down0.
      - subst rctx. apply (@Down_Group_inner LindenParameters).
      - apply Hroot.
    }
    specialize (IH Hrootr).
    destruct (tCompileSubPattern wr rctx rer forward) as [mr|] eqn:Heqmr; simpl; try exact I.
    intros tmc regc cont Htmc_tree inp Hinp_compat.
    unfold tMC_is_tree.
    intros s Hvalids Hs_inp.
    remember (fun y: MatchState => _) as tmc2.
    (* Let's try something *)
    specialize (IH tmc2 Epsilon (Aclose (S n) :: Areg regc :: cont)).
    assert (StaticSemantics.countLeftCapturingParensBefore (Group name wr) ctx + 1 = S n) as Heqid by admit.
    assert (forall inp : input, input_compat inp -> tMC_is_tree tmc2 Epsilon (Aclose (S n) :: Areg regc :: cont) inp) as Htmc2_tree.
    {
      intros inp' Hinp'_compat.
      rewrite Heqtmc2.
      unfold tMC_is_tree.
      intros s' Hs'valid Hs'_inp.
      destruct negb; simpl; try exact I.
      rewrite Heqid.
      replace ((S n) =? 0) with false.
      2: {
        symmetry.
        rewrite Nat.eqb_neq.
        lia.
      }
      destruct (List.List.Update.Nat.One.update) as [cap|]; simpl; try exact I.
      specialize (Htmc_tree inp' Hinp'_compat).
      unfold tMC_is_tree in Htmc_tree.
      remember (match_state _ _ cap) as s''.
      specialize (Htmc_tree s'').
      assert (Valid (MatchState.input s'') rer s'') as Hs''valid by admit. (* not entirely sure that this is actually true *)
      specialize (Htmc_tree Hs''valid).
      assert (ms_matches_inp s'' inp') as Hs''_inp' by admit.
      specialize (Htmc_tree Hs''_inp').
      destruct (tmc s'') as [subtree|] eqn:Heqsubtree; simpl; try exact I.
      apply tree_pop_close.
      apply tree_pop_reg.
      assumption.
    }
    rewrite Heqid.
    specialize (IH Htmc2_tree inp Hinp_compat).
    unfold tMC_is_tree in IH.
    specialize (IH s Hvalids Hs_inp).
    destruct (mr s tmc2) as [subtree|] eqn:Heqsubtree; simpl; try exact I.
    apply tree_group.
    apply is_tree_eps with (cont1 := nil). apply IH.
Admitted.
