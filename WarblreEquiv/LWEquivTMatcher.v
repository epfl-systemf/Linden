From Coq Require Import Lia PeanoNat ZArith List.
Import ListNotations.
From Linden Require Import LWEquivTMatcherDef LWEquivTMatcherLemmas TMatching Groups
  LindenParameters Tree Chars ListLemmas MSInput Tactics LKFactorization CharSet GroupMapMS.
From Warblre Require Import Result Notation Base Semantics Coercions
  Errors Patterns Node RegExpRecord.
Import Notation.
Import Coercions.
Import Result.Notations.
Import Patterns.

Local Open Scope result_flow.
Local Open Scope bool_scope.


(** * First part of equivalence proof: Warblre's matchers and the corresponding tree matchers yield equivalent results *)
(* This file contains the theorems stating the first part of the equivalence.
   The equivalence itself is defined in LWEquivTMatcherDef.v. *)

Section LWEquivTMatcher.
  Context `{characterClass: Character.class}.

  (** ** The identity continuations. *)
  Definition id_mcont: MatcherContinuation := fun x => Success (Some x).
  Definition id_tmcont: TMatcherContinuation := fun _ => Success Match.

  (* These two continuations are easily equivalent (under all input strings
     and both directions and with no groups opened). *)
  Lemma id_equiv: forall str0 dir, equiv_tree_mcont str0 id_mcont id_tmcont nil dir.
  Proof.
    constructor. simpl. constructor. assumption.
  Qed.


  (** ** Lemma for repeated matching. *)
  Lemma repeatMatcher'_tRepeatMatcher':
    (* For all pairs of a matcher m and a tree matcher tm *)
    forall (str0: string) (m: Matcher) (tm: TMatcher) (dir: Direction) (greedy: bool)
      (parenIndex parenCount: non_neg_integer),
      (* that are equivalent, *)
      equiv_tree_matcher str0 m tm (List.seq (parenIndex + 1) parenCount) dir ->
      (* for any fuel, min and max, *)
      forall fuel: nat,
      forall (min: non_neg_integer) (max: non_neg_integer_or_inf),
        (* the corresponding repeat matcher and tree matcher are equivalent with the same direction. *)
        equiv_tree_matcher str0
          (fun ms mc => Semantics.repeatMatcher' m min max greedy ms mc parenIndex parenCount fuel)
          (fun ms tmc => tRepeatMatcher' tm dir min max greedy ms tmc parenIndex parenCount fuel)
          (List.seq (parenIndex + 1) parenCount) dir.
  Proof.
    intros str0 m tm dir greedy parenIndex parenCount Hm_tm_equiv fuel.
    induction fuel as [|fuel IHfuel].
    1: constructor.

    intros min max. unfold equiv_tree_matcher. intros mc tmc gl Hgldisj Hequivcont.
    unfold equiv_tree_mcont. intros gm idx ms Hmsstr0 Hmsidx Hmsgm Hgmgl. simpl.
    destruct (max =? 0)%NoI eqn:Hmax0; simpl.
    (* Case max = 0: use hypothesis on continuation *)
    1: { unfold equiv_tree_mcont in Hequivcont. now apply Hequivcont. }

    (* Case max > 0 *)
    destruct List.List.Update.Nat.Batch.update as [cap'|] eqn:Heqcap'; simpl. 2: constructor.
    set (match_state (MatchState.input ms) (MatchState.endIndex ms) cap')
      as ms_reset.
    (* tmcnext and mcnext perform the progress check, then if this check succeeds, *)
    (* perform the recursive call with decreased min/max. *)
    set (fun y: MatchState => _) as tmcnext.
    set (fun (y: MatchState) => (_: MatchResult)) as mcnext.
    (* These two continuations are equivalent. *)
    assert (equiv_tree_mcont str0 mcnext tmcnext gl dir) as Hequivnext. {
      unfold equiv_tree_mcont.
      intros gm1 idx1 ms1 Hms1str0 Hms1idx1 Hgm1ms1 Hms1gl.
      unfold mcnext, tmcnext.
      (* Case analysis on whether the progress check fails *)
      destruct ((min ==? 0)%wt && _)%bool eqn:Hprogress; simpl.
      - (* Fails *) constructor. simpl. constructor.
      - (* Succeeds *)
        set (if (min ==? 0)%wt then 0 else min - 1) as nextmin.
        set (if (max =? +∞)%NoI then +∞ else (max - 1)%NoI) as nextmax.
        specialize (IHfuel nextmin nextmax mc tmc gl Hgldisj Hequivcont). unfold equiv_tree_mcont in IHfuel.
        specialize (IHfuel gm1 idx1 ms1 Hms1str0 Hms1idx1 Hgm1ms1 Hms1gl).
        destruct (min ==? 0)%wt; inversion IHfuel; simpl; constructor; auto.
    }
    (* Therefore, the results of matching the inner regexp, then looping, are *)
    (* equivalent. *)
    set (gm_reset := GroupMap.reset (seq (parenIndex+1) parenCount) gm).
    assert (equiv_results (tm ms_reset tmcnext) gm_reset idx dir
              (m ms_reset mcnext))
      as Hequiv_loop. {
      specialize (Hm_tm_equiv mcnext tmcnext gl Hgldisj Hequivnext).
      unfold equiv_tree_mcont in Hm_tm_equiv.
      specialize (Hm_tm_equiv gm_reset idx ms_reset).
      do 2 specialize_prove Hm_tm_equiv by now simpl.
      specialize_prove Hm_tm_equiv by admit.
      specialize_prove Hm_tm_equiv by admit. (* True because the list of open groups does not collide with the list of reset groups by hypothesis *)
      apply Hm_tm_equiv.
    }


    (* By hypothesis, the results of exiting the loop are equivalent. *)
    pose proof Hequivcont gm idx ms Hmsstr0 Hmsidx Hmsgm Hgmgl as Hequiv_exit.
    assert (equiv_results
              (let! z =<< tm ms_reset tmcnext in Success (GroupAction (Reset (List.seq (parenIndex + 1) parenCount)) z))
              gm idx dir (m ms_reset mcnext)) as Hequiv_loopreset. {
      inversion Hequiv_loop; simpl; constructor.
      simpl. fold gm_reset. assumption.
    }
    destruct (negb (min =? 0)) eqn:Hmin_nonzero; simpl. 1: apply Hequiv_loopreset.
    (* Case min = 0 *)
    destruct greedy.
    - setoid_rewrite func_monad_swap
         with (f1 := fun z => GroupAction (Reset (List.seq (parenIndex + 1)
                                                         parenCount)) z)
              (f2 := id).
       apply equiv_choice; try assumption.
       rewrite monad_id. assumption.
    - setoid_rewrite func_monad_swap
         with (f2 := fun z => GroupAction (Reset (List.seq (parenIndex + 1)
                                                         parenCount)) z)
              (f1 := id).
      apply equiv_choice; try assumption.
      rewrite monad_id. assumption.
  Admitted.


  (** ** Lemma for character set matchers. *)
  Lemma charset_tcharset:
    forall rer m tm charset str0 invert dir
      (Heqm: Semantics.characterSetMatcher rer charset invert dir = m)
      (Heqtm: tCharacterSetMatcher rer charset invert dir = tm),
      equiv_tree_matcher str0 m tm nil dir.
  Proof.
    intros. unfold equiv_tree_matcher. intros mc tmc gl _ Hequiv. unfold equiv_tree_mcont. intros gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl.
    subst m tm.
    unfold tCharacterSetMatcher, Semantics.characterSetMatcher. simpl.
    set (nextend := if (dir ==? forward)%wt then _ else _).
    set ((_ <? 0)%Z || _)%bool as oob. destruct oob eqn:Hoob.
    1: { constructor. simpl. constructor. }

    set (Z.min _ _) as index.
    remember (List.List.Indexing.Int.indexing _ _) as readchr.
    destruct readchr as [readchr|]; simpl. 2: constructor.
    set (CharSetExt.exist_canonicalized _ _ _) as read_matches.
    destruct ((if invert then false else true) && _); simpl. 1: constructor; constructor.
    destruct ((if invert then true else false) && _); simpl. 1: constructor; constructor.
    remember (match_state _ _ _) as ms'.
    unfold equiv_tree_mcont in Hequiv.
    specialize (Hequiv gm (advance_idx idx dir) ms').
    specialize_prove Hequiv. { rewrite Heqms'; auto. }
    specialize_prove Hequiv by admit. (* True because oob = false *)
    specialize_prove Hequiv. { unfold equiv_groupmap_ms. rewrite Heqms'. apply Hgmms. }
    specialize (Hequiv Hgmgl).
    destruct (tmc ms') as [child|]; simpl. 2: constructor.
    destruct (mc ms') as [res|]; simpl. 2: constructor.
    constructor. simpl.
    (*replace index with (MatchState.endIndex ms) in Heqreadchr by lia.*)
    now inversion Hequiv as [child0 gm0 idx' dir0 res0 Hequiv' Heqchild0 Heqgm0 Heqidx' Heqdir0 Heqres0 | |].
  Admitted.


  (** ** Lemma for lookarounds. *)

  (* A dummy match state to be able to discriminate; probably not strictly necessary. *)
  Definition dummy_match_state: MatchState := match_state nil 0%Z nil.

  (* List of groups defined by a regex given the regex and its context. *)
  Definition def_groups_reg (reg: Regex) (ctx: RegexContext): list group_id :=
    let parenIndex := StaticSemantics.countLeftCapturingParensBefore reg ctx in
    let parenCount := StaticSemantics.countLeftCapturingParensWithin reg ctx in
    List.seq (parenIndex + 1) parenCount.

  (* The lemma; lkdir is the lookaround direction, pos is the lookaround positivity, lkreg is the lookaround regex. *)
  Lemma compile_tcompile_lk:
    forall lkdir pos lkreg rer
      (IH:
        forall ctx m tm dir
          (Heqm: Semantics.compileSubPattern lkreg ctx rer dir = Success m)
          (Heqtm: tCompileSubPattern lkreg ctx rer dir = Success tm),
          forall str0, equiv_tree_matcher str0 m tm (def_groups_reg lkreg ctx) dir),
    forall ctx m tm dir
      (Heqm: Semantics.compileSubPattern ((to_warblre_lookaround lkdir pos) lkreg) ctx rer dir = Success m)
      (Heqtm: tLookaroundMatcher tCompileSubPattern lkdir pos lkreg ctx rer dir = Success tm),
    forall str0, equiv_tree_matcher str0 m tm (def_groups_reg ((to_warblre_lookaround lkdir pos) lkreg) ctx) dir.
  Proof.
    intros. pose proof (lookaroundMatcher_fact lkdir pos lkreg ctx rer dir) as Hfact. setoid_rewrite Heqm in Hfact. clear Heqm.
    unfold tLookaroundMatcher in Heqtm. unfold lookaroundMatcher in Hfact.
    (* Assume that compiling the lookaround expressions succeed *)
    destruct Semantics.compileSubPattern as [mlk|] eqn:Heqmlk; simpl in *. 2: discriminate (Hfact id_mcont dummy_match_state).
    destruct tCompileSubPattern as [tmlk|] eqn:Heqtmlk; simpl in *. 2: discriminate.
    (* We cannot inject Hfact because we only have functional equality *)
    injection Heqtm as <-. unfold equiv_tree_matcher.
    (* Let mc and tmc be a pair of equivalent continuations that close the groups in gl. *)
    (* These continuations will be run after the lookaround *)
    intros mc tmc gl Hgldisj Hequivcont. unfold equiv_tree_mcont.
    (* Let gm, idx and ms be corresponding group map, index and MatchState. *)
    intros gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl.
    (* We can now inject Hfact *)
    specialize (Hfact mc ms). injection Hfact as ->.
    (* We apply IH to prove that tmlk ms id_tmcont and mlk ms id_mcont have equivalent results *)
    specialize (IH _ mlk tmlk lkdir Heqmlk Heqtmlk str0 id_mcont id_tmcont nil).
    specialize_prove IH by admit. (* Nil is always disjoint from anything *)
    specialize (IH (id_equiv str0 lkdir)).
    unfold equiv_tree_mcont in IH.
    (* tmlk ms id_tmcont is interpreted with the group map to_group_map ms and the empty open groups list *)
    (* mlk ms id_tmcont is interpreted with the MatchState ms *)
    set (gmlk := to_group_map ms). specialize (IH gmlk idx ms Hmsstr0 Hmsidx).
    do 2 specialize_prove IH by admit. (* True because gmlk is a translation of ms to a group map *) simpl in *.
    (* Assume that the matcher and tree matcher succeed *)
    destruct tmlk as [tlk|] eqn:Htlk; try solve[constructor]. simpl.
    destruct mlk as [mslkopt|] eqn:Hmslkopt; try solve[constructor]. simpl.
    (* IH tells us that tree_res tlk gmlk idx lkdir and mslkopt represent the same results *)
    inversion IH as [tlk' gmlk' idx' lkdir' mslkopt' IH' | |]. subst tlk' gmlk' idx' lkdir' mslkopt'.
    replace (Z.to_nat (MatchState.endIndex ms)) with idx by lia.

    (* Case analysis on whether these results are successes or failures *)
    inversion IH' as [HNonel HNoner | gmafterlk msafterlk Hequivafterlk Heqgmafterlk Heqmsafterlk]; simpl in *; destruct pos; destruct mslkopt as [mslk|]; simpl in *; try solve[now constructor]; try discriminate.
    - (* Failure, positive lookaround: easy *) constructor. simpl. constructor.
    - (* Failure, negative lookaround *)
      (* Apply hypothesis on continuation with group map gm, index idx, match state ms (same as before lookaround) *)
      unfold equiv_tree_mcont in Hequivcont. specialize (Hequivcont gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl).
      inversion Hequivcont as [t1 gm' idx' dir' wres Hequivcont' Heqt1 Heqgm' Heqidx' Heqdir' Heqwres | |]. 2,3: constructor.
      simpl. constructor. simpl. replace (Regex.positivity _) with false by now destruct lkdir. replace (Regex.lk_dir _) with lkdir by now destruct lkdir.
      replace (tree_res tlk gm idx lkdir) with (@None group_map).
      2: {
        symmetry. (* Follows from group map independence *) admit.
      }
      assumption.
    - (* Success, positive lookaround *)
      replace (to_capture_list _ _ _) with (MatchState.captures msafterlk) by admit. (* follows from Hequivafterlk *)
      (* mscont takes the captures from msafterlk but takes the original index *)
      set (mscont := match_state _ _ _).
      (* tmc mscont is interpreted with a group map that is the result of merging gmafterlk into gm; *)
      (* equivalently (must be proven), with the group map that is the result of interpreting the lookaround with gm and idx *)
      assert (
        exists gmafterlk_linden,
        tree_res tlk gm idx lkdir = Some gmafterlk_linden /\
        equiv_groupmap_ms gmafterlk_linden msafterlk /\
        group_map_equiv_open_groups gmafterlk_linden gl)
        as [gmafterlk_linden [Htreerestlk [Hgmafterlk_linden_msafterlk Hgmafterlk_linden_gl]]]
        by admit.
      specialize (Hequivcont gmafterlk_linden idx mscont Hmsstr0 Hmsidx Hgmafterlk_linden_msafterlk Hgmafterlk_linden_gl).
      inversion Hequivcont as [tcont gm0 idx0 dir0 rescont Hequiv_tcont_rescont Heqtcont | |]. 2,3: constructor.
      simpl. constructor. simpl.
      replace (Regex.positivity _) with true by now destruct lkdir.
      replace (Regex.lk_dir _) with lkdir by now destruct lkdir.
      rewrite Htreerestlk. assumption.
    - constructor. simpl. constructor.
  Admitted.


  (** ** Lemma for AtomEscs *)
  Lemma compile_tcompile_atomescape:
    forall ae ctx rer m tm dir
      (Heqm: Semantics.compileSubPattern (AtomEsc ae) ctx rer dir = Success m)
      (Heqtm: tCompileSubPattern (AtomEsc ae) ctx rer dir = Success tm),
    forall str0, equiv_tree_matcher str0 m tm nil dir.
  Proof.
    intros ae ctx rer m tm dir. simpl. destruct ae; try discriminate.
    - (* ACharacterClassEsc *)
      destruct esc.
      (* \d, \D, \s, \S, \w, \W *)
      1-6: intros; injection Heqm as <-; injection Heqtm as <-; eapply charset_tcharset; reflexivity.
      + (* Unicode property *)
        destruct p.
      + (* Negative unicode property *)
        destruct p.
    - (* ACharacterEsc *)
      destruct esc; simpl.
      + (* ControlEsc *)
        destruct esc; intros; injection Heqm as <-; injection Heqtm as <-; eapply charset_tcharset; reflexivity.
      + (* AsciiControlEsc *)
        intros; injection Heqm as <-; injection Heqtm as <-; eapply charset_tcharset; reflexivity.
      + (* esc_Zero *)
        intros; injection Heqm as <-; injection Heqtm as <-; eapply charset_tcharset; reflexivity.
      + (* HexEscape *)
        intros; injection Heqm as <-; injection Heqtm as <-; eapply charset_tcharset; reflexivity.
      + (* UnicodeEsc *)
        destruct seq; intros; injection Heqm as <-; injection Heqtm as <-; eapply charset_tcharset; reflexivity.
      + (* IdentityEsc *)
        intros; injection Heqm as <-; injection Heqtm as <-; eapply charset_tcharset; reflexivity.
  Qed.

  (** ** Main theorem *)
  Theorem compile_tcompile:
    forall reg ctx rer m tm dir (* for all regexes, contexts, RegExpRecords and directions, *)
      (* if the compilations of the regexes into a matcher and a tree matcher succeed, *)
      (Heqm: Semantics.compileSubPattern reg ctx rer dir = Success m)
      (Heqtm: tCompileSubPattern reg ctx rer dir = Success tm),
      (* then the resulting matcher and tree matcher are equivalent. *)
    forall str0, equiv_tree_matcher str0 m tm (def_groups_reg reg ctx) dir.
  Proof.
    intros reg ctx rer.
    revert ctx.
    induction reg as [
      |
      chr |
      |
      ae |
      cc |
      wr1 IH1 wr2 IH2 |
      wr IH q |
      wr1 IH1 wr2 IH2 |
      name wr IH |
      |
      |
      |
      |
      wr IH |
      wr IH |
      wr IH |
      wr IH
    ]; try discriminate.

    - (* Empty *)
      intros. injection Heqm as <-. injection Heqtm as <-.
      unfold equiv_tree_matcher. intros mc tmc gl _ Hequiv.
      unfold equiv_tree_mcont. intros gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl.
      now apply Hequiv.

    - (* Character *)
      intros. injection Heqm as <-. injection Heqtm as <-. eapply charset_tcharset; reflexivity.

    - (* Dot; same as character *)
      intros. injection Heqm as <-. injection Heqtm as <-. eapply charset_tcharset; reflexivity.

    - (* AtomEsc *)
      intros. eapply compile_tcompile_atomescape; eauto.

    - (* CharacterClass *)
      simpl. intros. destruct Semantics.compileCharacterClass; simpl in *. 2: discriminate.
      injection Heqm as <-. injection Heqtm as <-. eapply charset_tcharset; reflexivity.

    - (* Disjunction *)
      simpl. intros.
      set (Disjunction_left wr2 :: ctx)%list as ctxleft.
      set (Disjunction_right wr1 :: ctx)%list as ctxright.
      specialize (IH1 ctxleft). specialize (IH2 ctxright).
      destruct (Semantics.compileSubPattern wr1 _ _ _) as [m1|] eqn:Heqm1; simpl. 2: discriminate.
      destruct (Semantics.compileSubPattern wr2 _ _ _) as [m2|] eqn:Heqm2; simpl. 2: discriminate.
      destruct tCompileSubPattern as [tm1|] eqn:Heqtm1 in Heqtm; simpl. 2: discriminate.
      destruct tCompileSubPattern as [tm2|] eqn:Heqtm2 in Heqtm; simpl. 2: discriminate.
      simpl in *.
      unfold equiv_tree_matcher. intros mc tmc gl Hgldisj Hequiv.
      unfold equiv_tree_mcont. intros gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl.
      specialize (IH1 m1 tm1 dir Heqm1 Heqtm1 str0 mc tmc gl).
      specialize (IH2 m2 tm2 dir Heqm2 Heqtm2 str0 mc tmc gl).
      (* Disjointness from groups of whole regexp implies disjointness from groups of sub-regexes. *)
      specialize_prove IH1 by admit. specialize_prove IH2 by admit.
      specialize (IH1 Hequiv). specialize (IH2 Hequiv).
      unfold equiv_tree_mcont in IH1, IH2.
      specialize (IH1 gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl).
      specialize (IH2 gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl).
      injection Heqtm as <-.
      destruct (tm1 ms tmc) as [t1|] eqn:Heqt1; simpl. 2: constructor.
      destruct (tm2 ms tmc) as [t2|] eqn:Heqt2; simpl. 2: constructor.
      injection Heqm as <-.
      destruct (m1 ms mc) as [r|] eqn:Heqr; simpl. 2: constructor.
      destruct r as [msr|] eqn:?; simpl.
      + (* First branch succeeds *)
        constructor. inversion IH1 as [t1' gm' idx' dir' Somemsr IH1' | |].
        simpl. inversion IH1'. simpl. rewrite H4. assumption.
      + destruct (m2 ms mc) as [r2|] eqn:Heqr2; simpl. 2: constructor.
        constructor.
        inversion IH1 as [t1' gm' idx' dir' None' IH1' | |]. subst t1' gm' idx' dir' None'.
        simpl. inversion IH1'. simpl.
        now inversion IH2.

    - (* Quantifier *)
      simpl. intros.
      set (Quantified_inner q :: ctx)%list as ctx' in *. specialize (IH ctx').
      destruct Semantics.compileSubPattern as [msub|] eqn:Heqmsub; simpl. 2: discriminate.
      destruct tCompileSubPattern as [tmsub|] eqn:Heqtmsub; simpl. 2: discriminate.
      specialize (IH msub tmsub dir Heqmsub Heqtmsub).
      simpl in *.
      destruct negb; simpl. 1: discriminate.
      unfold equiv_tree_matcher. intros mc tmc gl Hgldisj Hequivcont.
      unfold equiv_tree_mcont. intros gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl.
      unfold Semantics.repeatMatcher in Heqm. unfold tRepeatMatcher in Heqtm.
      injection Heqm as <-. injection Heqtm as <-.
      apply repeatMatcher'_tRepeatMatcher' with (str0 := str0) (gl := gl); auto.
      unfold def_groups_reg in IH. simpl in IH. rewrite Nat.add_0_r in IH. apply IH.

    - (* Sequence *)
      simpl. intros.
      set (Seq_left wr2 :: ctx)%list as ctxleft in *.
      set (Seq_right wr1 :: ctx)%list as ctxright in *.
      specialize (IH1 ctxleft). specialize (IH2 ctxright).
      destruct (Semantics.compileSubPattern wr1 _ _ _) as [m1|] eqn:Heqm1; simpl. 2: discriminate.
      destruct (Semantics.compileSubPattern wr2 _ _ _) as [m2|] eqn:Heqm2; simpl. 2: discriminate.
      destruct tCompileSubPattern as [tm1|] eqn:Heqtm1 in Heqtm; simpl. 2: discriminate.
      destruct tCompileSubPattern as [tm2|] eqn:Heqtm2 in Heqtm; simpl. 2: discriminate.
      simpl in *. destruct dir; injection Heqm as <-; injection Heqtm as <-; intros mc tmc gl Hgldisj Hequiv gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl.
      + specialize (IH2 m2 tm2 forward Heqm2 Heqtm2 str0 mc tmc gl). specialize_prove IH2 by admit. (* gl is indeed disjoint from the groups of the sub-regexp *)
        specialize (IH2 Hequiv).
        specialize (IH1 m1 tm1 forward Heqm1 Heqtm1 str0 (fun ms0 => m2 ms0 mc) (fun ms0 => tm2 ms0 tmc) gl).
        specialize_prove IH1 by admit. specialize (IH1 IH2). auto.
      + specialize (IH1 m1 tm1 backward Heqm1 Heqtm1 str0 mc tmc gl). specialize_prove IH1 by admit. specialize (IH1 Hequiv).
        specialize (IH2 m2 tm2 backward Heqm2 Heqtm2 str0 (fun ms0 => m1 ms0 mc) (fun ms0 => tm1 ms0 tmc) gl). specialize_prove IH2 by admit. specialize (IH2 IH1). auto.

    - (* Group *)
      simpl. intros.
      set (Group_inner name :: ctx)%list as ctx' in *. specialize (IH ctx').
      destruct (Semantics.compileSubPattern wr ctx' rer dir) as [msub|] eqn:Heqmsub; simpl. 2: discriminate.
      destruct tCompileSubPattern as [tmsub|] eqn:Heqtmsub in Heqtm; simpl. 2: discriminate.
      intros mc tmc gl Hgldisj Hequiv gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl.
      simpl in *.
      injection Heqm as <-. injection Heqtm as <-.
      (* treecont and origcont close the group and continue with the rest of the regexp *)
      remember (fun y : MatchState => _) as treecont.
      remember (fun y : MatchState => let! r =<< _ in let! cap =<< _ in mc _) as origcont.
      remember (StaticSemantics.countLeftCapturingParensBefore _ ctx + 1) as gid.
      set (gl' := ((gid, idx)::gl)%list).
      specialize (IH msub tmsub dir Heqmsub Heqtmsub str0 origcont treecont gl').
      (* Letting parenIndex be gid-1 and parenCount be the number of groups defined
         by the sub-regexp plus one, gl is disjoint from [parenIndex + 1, parenIndex + parenCount]
         so gl' = (gid, idx)::gl is disjoint from [parenIndex + 2 = gid + 1, parenIndex + parenCount] *)
      specialize_prove IH by admit.
      specialize_prove IH. {
        unfold equiv_tree_mcont.
        intros gmafter idxafter msafter Hmsafterstr0 Hmsafteridxafter Hgmaftermsafter Hgmaftergl'.
        rewrite Heqtreecont, Heqorigcont. clear Heqtreecont Heqorigcont.
        set (extr1 := MatchState.endIndex ms). set (extr2 := MatchState.endIndex msafter).
        set (if (dir ==? forward)%wt then _ else _) as rangeresult. destruct rangeresult as [r|] eqn:Heqrange; simpl. 2: constructor.
        destruct (gid =? 0) eqn:Hgid_nonzero; simpl. 1: constructor.
        destruct List.List.Update.Nat.One.update as [cap'|] eqn:Hcapupd; simpl. 2: constructor.
        set (match_state _ _ cap') as mscont.
        destruct (tmc mscont) as [t|] eqn:Heqt; simpl. 2: constructor.
        destruct (mc mscont) as [res|] eqn:Heqres; simpl. 2: constructor.
        constructor. simpl. unfold equiv_tree_mcont in Hequiv.
        specialize (Hequiv (GroupMap.close idxafter gid gmafter) idxafter mscont Hmsstr0 Hmsafteridxafter).
        specialize_prove Hequiv by admit.
        specialize_prove Hequiv by admit.
        inversion Hequiv; congruence.
      }
      unfold equiv_tree_mcont in IH.
      specialize (IH (GroupMap.open idx gid gm) idx ms Hmsstr0 Hmsidx).
      do 2 specialize_prove IH by admit.
      destruct (tmsub ms treecont) as [t|] eqn:Heqt; simpl. 2: constructor.
      destruct (msub ms origcont) as [res|] eqn:Heqres; simpl. 2: constructor.
      constructor. simpl. inversion IH. auto.

    - (* Input start *)
      simpl. intros ctx m tm dir Heqm Heqtm. injection Heqm as <-. injection Heqtm as <-.
      intro str0. unfold equiv_tree_matcher. intros mc tmc gl Hgldisj Hequivcont.
      unfold equiv_tree_mcont. intros gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl.
      destruct (if (_: bool) then Success true else _) as [anchormatch|]; simpl. 2: constructor.
      destruct anchormatch.
      + unfold equiv_tree_mcont in Hequivcont. specialize (Hequivcont gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl). inversion Hequivcont; try solve[constructor]; simpl.
        constructor. auto.
      + constructor. simpl. constructor.

    - (* Input end: same as input start, but the placeholders in the first destruct are different *)
      simpl. intros ctx m tm dir Heqm Heqtm. injection Heqm as <-. injection Heqtm as <-.
      intro str0. unfold equiv_tree_matcher. intros mc tmc gl Hgldisj Hequivcont.
      unfold equiv_tree_mcont. intros gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl.
      destruct (if (_: bool) then Success true else _) as [anchormatch|]; simpl. 2: constructor.
      destruct anchormatch.
      + unfold equiv_tree_mcont in Hequivcont. specialize (Hequivcont gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl). inversion Hequivcont; try solve[constructor]; simpl.
        constructor. auto.
      + constructor. simpl. constructor.

    (* Word boundary *)
    - simpl. intros ctx m tm dir Hcompsucc Htcompsucc str0. injection Hcompsucc as <-. injection Htcompsucc as <-.
      unfold equiv_tree_matcher.
      intros mc tmc gl Hgldisj Hequivcont. unfold equiv_tree_mcont.
      intros gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl.
      destruct Semantics.isWordChar as [a|] eqn:Hwca; simpl. 2: constructor.
      destruct (Semantics.isWordChar rer (_ ms) (MatchState.endIndex ms)) as [b|] eqn:Hwcb; simpl. 2: constructor.
      destruct (_ && _ || _ && _); simpl.
      + unfold equiv_tree_mcont in Hequivcont. specialize (Hequivcont gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl).
        destruct tmc as [t|]; simpl. 2: constructor.
        destruct mc as [res|]; simpl. 2: constructor.
        constructor. simpl. now inversion Hequivcont.
      + constructor. constructor.

    (* Non word boundary; same proof as above, except the placeholders at the main destruct differ *)
    - simpl. intros ctx m tm dir Hcompsucc Htcompsucc str0. injection Hcompsucc as <-. injection Htcompsucc as <-.
      unfold equiv_tree_matcher.
      intros mc tmc gl Hgldisj Hequivcont. unfold equiv_tree_mcont.
      intros gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl.
      destruct Semantics.isWordChar as [a|] eqn:Hwca; simpl. 2: constructor.
      destruct (Semantics.isWordChar rer (_ ms) (MatchState.endIndex ms)) as [b|] eqn:Hwcb; simpl. 2: constructor.
      destruct (_ && _ || _ && _); simpl.
      + unfold equiv_tree_mcont in Hequivcont. specialize (Hequivcont gm idx ms Hmsstr0 Hmsidx Hgmms Hgmgl).
        destruct tmc as [t|]; simpl. 2: constructor.
        destruct mc as [res|]; simpl. 2: constructor.
        constructor. simpl. now inversion Hequivcont.
      + constructor. constructor.

      (* Positive lookahead *)
    - simpl. intros. apply compile_tcompile_lk with (lkdir := forward) (pos := true) (lkreg := wr) (rer := rer) (ctx := ctx); auto.

      (* Negative lookahead *)
    - simpl. intros. apply compile_tcompile_lk with (lkdir := forward) (pos := false) (lkreg := wr) (rer := rer) (ctx := ctx); auto.

      (* Positive lookbehind *)
    - simpl. intros. apply compile_tcompile_lk with (lkdir := backward) (pos := true) (lkreg := wr) (rer := rer) (ctx := ctx); auto.

      (* Negative lookbehind *)
    - simpl. intros. apply compile_tcompile_lk with (lkdir := backward) (pos := false) (lkreg := wr) (rer := rer) (ctx := ctx); auto.
  Admitted.
End LWEquivTMatcher.
