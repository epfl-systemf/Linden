From Linden Require Import EquivDef RegexpTranslation Regex LindenParameters
  Semantics FunctionalSemantics LWEquivTreeLemmas CharDescrCharSet Tactics
  NumericLemmas MSInput Chars Groups EquivLemmas Utils CharSet GroupMapLemmas.
From Warblre Require Import Parameters Semantics RegExpRecord Patterns
  Node Result Notation Typeclasses List Base Node Match.
Import Patterns.
Import Result.Notations.
Import Notation.
Import NodeProps.Zipper.
Import Match.
From Coq Require Import ZArith PeanoNat Lia RelationClasses.

Local Open Scope result_flow.

Section Equiv.
  Context `{characterClass: Character.class}.

  (* The identity continuation *)
  Definition id_mcont: MatcherContinuation :=
    fun x => Success (Some x).

  (* The identity continuation is equivalent to the empty list of actions with any list of forbidden groups and any list of open groups *)
  Lemma id_equiv:
    forall gl forbgroups dir str0 rer,
      equiv_cont id_mcont gl forbgroups nil dir str0 rer.
  Proof.
    intros. unfold equiv_cont. intros gm ms inp res [|fuel] t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden; simpl; try discriminate.
    unfold id_mcont. intro H. injection H as <-. intro H. injection H as <-.
    simpl. constructor. assumption.
  Qed.

  (* Case when the repeat matcher is done iterating the regex because min = max = 0. *)
  Lemma repeatMatcher'_done_equiv:
    forall greedy parenIndex parenCount rer,
    forall (m: Matcher) (lreg: regex) (dir: Direction),
      equiv_matcher m lreg rer dir ->
      def_groups lreg = List.seq (parenIndex + 1) parenCount ->
      forall fuel, equiv_matcher
        (fun ms mc => Semantics.repeatMatcher' m 0 (NoI.N 0) greedy ms mc parenIndex parenCount fuel)
        (Regex.Quantified greedy 0 (NoI.N 0) lreg) rer dir.
  Proof.
    intros greedy parenIndex parenCount rer m lreg dir Hequiv Hgroupsvalid fuel.
    unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
    unfold equiv_cont. intros gm ms inp res [|treefuel] t Hinpcompat Hgmms Hgmgl Hmsinp Hmsvalidchecks Hgmvalid Hnoforbidden; simpl; try discriminate.
    destruct fuel as [|fuel]; simpl; try discriminate.
    intros Hres Ht. eapply Hequivcont; eauto using ms_valid_wrt_checks_tail.
  Qed.

  (* Case when the repeat matcher can choose between iterating the sub-regexp and exiting the quantifier because min = 0 but max != 0. *)
  Lemma repeatMatcher'_free_equiv:
    forall greedy parenIndex parenCount rer,
    forall (m: Matcher) (lreg: regex) (dir: Direction),
      equiv_matcher m lreg rer dir ->
      def_groups lreg = List.seq (parenIndex + 1) parenCount ->
      forall fuel delta, equiv_matcher
        (fun ms mc => Semantics.repeatMatcher' m 0 delta greedy ms mc parenIndex parenCount fuel)
        (Regex.Quantified greedy 0 delta lreg) rer dir.
    Proof.
      (* We perform induction on the fuel. The case fuel = 0 is immediate. *)
      intros greedy parenIndex parenCount rer m lreg dir Hequiv Hgroupsvalid fuel.
      induction fuel as [|fuel IHfuel]. 1: discriminate.

      (* For delta = 0, we apply repeatMatcher'_done_equiv. *)
      intro delta.
      destruct (delta =? NoI.N (nat_to_nni 0))%NoI eqn:Hdeltazero.
      1: { rewrite noi_eqb_eq in Hdeltazero. subst delta. now apply repeatMatcher'_done_equiv. }
      simpl. rewrite Hdeltazero.
      (* Let mc be a continuation equivalent to actions act. *)
      unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
      (* We now prove that plugging mc into the repeat matcher yields a continuation that performs actions Areg (Quantified greedy 0 delta lreg)::act. *)
      (* Let ms be a valid input MatchState. *)
      unfold equiv_cont. intros gm ms inp res fueltree t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
      (* Assume that the capture reset succeeds. *)
      destruct List.Update.Nat.Batch.update as [cap'|] eqn:Heqcap'; simpl; try discriminate.
      (* mcloop performs a progress check then calls the repeat matcher with one less fuel and one less detlta. *)
      set (mcloop := fun y: MatchState => if (_ =? _)%Z then _ else _).
      set (msreset := match_state _ _ cap').
      (* We characterize mcloop. *)
      assert (Hmcloopequiv: equiv_cont mcloop gl forbgroups (Acheck inp::Areg (Regex.Quantified greedy 0 (delta - 1)%NoI lreg)::act)%list dir str0 rer). {
        unfold equiv_cont. intros gm' ms' inp' res' fueltree' t' Hinp'compat Hgm'ms' Hgm'gl Hms'inp' Hms'checks Hgm'valid Hnoforbidden'.
        unfold mcloop.
        destruct (_ =? _)%Z eqn:Heqcheck.
        - (* Case 1: the input has not progressed *)
          intro H. injection H as <-.
          destruct fueltree' as [|fueltree']; simpl; try discriminate.
          rewrite ms_same_end_same_inp with (ms := ms') (ms' := ms) (inp := inp') (inp' := inp) (str0 := str0) by assumption.
          rewrite strict_suffix_irreflexive_bool.
          intro H. injection H as <-.
          constructor.
        - (* Case 2: the input has progressed *)
          set (delta' := if (delta =? +∞)%NoI then _ else _).
          specialize (IHfuel delta').
          unfold equiv_matcher in IHfuel. specialize (IHfuel str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj).
          unfold equiv_cont in IHfuel.
          intros Hres'succ.
          destruct fueltree' as [|fueltree']; simpl; try discriminate.
          (* Follows from Hms'checks and other hypotheses linking ms', inp', inp and str0 *)
          replace (is_strict_suffix inp' inp dir) with true. 2: { symmetry; eapply progresscheck_success_ssuffix; eauto. }
          destruct compute_tree as [treecont|] eqn:Htreecontsucc; simpl; try discriminate.
          intro H. injection H as <-.
          simpl. eapply IHfuel; eauto.
          all: replace (delta') with (delta-1)%NoI by now destruct delta.
          + eauto using ms_valid_wrt_checks_tail.
          + apply Htreecontsucc.
      }
      (* About m msreset mcloop *)
      unfold equiv_matcher in Hequiv. specialize (Hequiv str0 mcloop gl _ _ Hmcloopequiv Hgldisj).
      set (gmreset := GroupMap.reset (def_groups lreg) gm).
      unfold equiv_cont in Hequiv.
      specialize (Hequiv Hdef_forbid_disj gmreset msreset inp).
      destruct fueltree as [|fueltree]; simpl; try discriminate.
      (* About mc ms *)
      unfold equiv_cont in Hequivcont. specialize (Hequivcont gm ms inp).
      
      (* Case analysis on greediness *)
      destruct greedy.
      - destruct (m msreset mcloop) as [resloop|] eqn:Hresloopsucc; simpl; try discriminate.
        specialize (Hequiv resloop fueltree).
        destruct resloop as [resloopms|]; simpl.
        + (* resloop is not None *)
          intro H. injection H as <-.
          destruct delta as [[|delta']|]; simpl in *; try discriminate.
          * (* delta is finite *)
            destruct (compute_tree _ inp (GroupMap.reset _ _) dir fueltree) as [titer|] eqn:Htitersucc; simpl; try discriminate.
            destruct (compute_tree act inp gm dir fueltree) as [tskip|] eqn:Htskipsucc; simpl; try discriminate.
            intro H. injection H as <-.
            replace (delta' - 0) with delta' in * by lia.
            specialize (Hequiv titer Hinpcompat).
            specialize_prove Hequiv. { eapply equiv_gm_ms_reset; eauto. reflexivity. }
            specialize_prove Hequiv. { eapply equiv_open_groups_reset; eauto. }
            specialize_prove Hequiv. { destruct ms. eapply ms_matches_inp_capchg; eauto. }
            specialize_prove Hequiv by admit.
            (* msreset is valid with respect to the checks in act because of the
            assumption on ms and wrt the check with inp because msreset matches inp *)
            specialize_prove Hequiv by now apply gm_reset_valid.
            specialize_prove Hequiv. { eapply noforb_reset; eauto. reflexivity. } (* gmreset does not contain any of the forbidden groups in lreg because those have just been reset, and does not contain any of the rest of the forbidden groups by assumption on gm *)
            specialize (Hequiv eq_refl Htitersucc).
            inversion Hequiv. simpl. unfold gmreset in H. rewrite <- H. simpl. constructor. assumption.
          * (* delta is infinite; copy-pasting and removing one line *)
            destruct (compute_tree _ inp (GroupMap.reset _ _) dir fueltree) as [titer|] eqn:Htitersucc; simpl; try discriminate.
            destruct (compute_tree act inp gm dir fueltree) as [tskip|] eqn:Htskipsucc; simpl; try discriminate.
            intro H. injection H as <-.
            specialize (Hequiv titer Hinpcompat).
            specialize_prove Hequiv. { eapply equiv_gm_ms_reset; eauto. reflexivity. }
            specialize_prove Hequiv. { eapply equiv_open_groups_reset; eauto. }
            specialize_prove Hequiv. { destruct ms. eapply ms_matches_inp_capchg; eauto. }
            specialize_prove Hequiv by admit.
            specialize_prove Hequiv by now apply gm_reset_valid.
            specialize_prove Hequiv. { eapply noforb_reset; eauto. reflexivity. }
            specialize (Hequiv eq_refl Htitersucc).
            inversion Hequiv. simpl. unfold gmreset in H. rewrite <- H. simpl. constructor. assumption.
        + (* resloop is None *)
          intro Hcontsucc. destruct delta as [[|delta']|]; simpl in *; try discriminate.
          * (* delta is finite *)
            destruct (compute_tree _ inp (GroupMap.reset _ _) dir fueltree) as [titer|] eqn:Htitersucc; simpl; try discriminate.
            destruct (compute_tree act inp gm dir fueltree) as [tskip|] eqn:Htskipsucc; simpl; try discriminate.
            intro H. injection H as <-.
            replace (delta' - 0) with delta' in * by lia.
            specialize (Hequiv titer Hinpcompat).
            specialize_prove Hequiv. { eapply equiv_gm_ms_reset; eauto. reflexivity. }
            specialize_prove Hequiv. { eapply equiv_open_groups_reset; eauto. }
            specialize_prove Hequiv. { destruct ms. eapply ms_matches_inp_capchg; eauto. }
            specialize_prove Hequiv by admit.
            specialize_prove Hequiv by now apply gm_reset_valid.
            specialize_prove Hequiv. { eapply noforb_reset; eauto. reflexivity. }
            specialize (Hequiv eq_refl Htitersucc).
            inversion Hequiv. simpl. unfold gmreset in H0. rewrite <- H0. simpl. eapply Hequivcont; eauto using ms_valid_wrt_checks_tail.
          * (* delta is infinite; copy-pasting and removing one line *)
            destruct (compute_tree _ inp (GroupMap.reset _ _) dir fueltree) as [titer|] eqn:Htitersucc; simpl; try discriminate.
            destruct (compute_tree act inp gm dir fueltree) as [tskip|] eqn:Htskipsucc; simpl; try discriminate.
            intro H. injection H as <-.
            specialize (Hequiv titer Hinpcompat).
            specialize_prove Hequiv. { eapply equiv_gm_ms_reset; eauto. reflexivity. }
            specialize_prove Hequiv. { eapply equiv_open_groups_reset; eauto. }
            specialize_prove Hequiv. { destruct ms. eapply ms_matches_inp_capchg; eauto. }
            specialize_prove Hequiv by admit.
            specialize_prove Hequiv by now apply gm_reset_valid.
            specialize_prove Hequiv. { eapply noforb_reset; eauto. reflexivity. }
            specialize (Hequiv eq_refl Htitersucc).
            inversion Hequiv. simpl. unfold gmreset in H0. rewrite <- H0. simpl. eapply Hequivcont; eauto using ms_valid_wrt_checks_tail.
      
      - destruct (mc ms) as [resskip|] eqn:Hresskipsucc; simpl; try discriminate.
        (* Probably similar to greedy case *)
        admit.
  Admitted.

  (* General case; the proof below mostly deals with the case max > 0 and applies the two above lemmas otherwise *)
  Lemma repeatMatcher'_equiv:
    forall greedy parenIndex parenCount rer,
    forall (m: Matcher) (lreg: regex) (dir: Direction),
      equiv_matcher m lreg rer dir ->
      def_groups lreg = List.seq (parenIndex + 1) parenCount ->
      forall fuel min delta, equiv_matcher
        (fun ms mc => Semantics.repeatMatcher' m min (NoI.N min + delta)%NoI greedy ms mc parenIndex parenCount fuel)
        (Regex.Quantified greedy min delta lreg) rer dir.
  Proof.
    intros greedy parenIndex parenCount rer m lreg dir Hequiv Hgroupsvalid fuel.
    induction fuel as [|fuel IHfuel]. 1: discriminate.

    intros min delta.
    set (max := (NoI.N min + delta)%NoI).
    destruct (max =? NoI.N (nat_to_nni 0))%NoI eqn:Hmaxzero.
    1: { (* Apply repeatMatcher'_done_equiv *)
      rewrite noi_eqb_eq in Hmaxzero. rewrite Hmaxzero.
      unfold max in Hmaxzero. destruct delta as [delta|]; try discriminate.
      simpl in Hmaxzero. destruct min; try discriminate. destruct delta; try discriminate. apply repeatMatcher'_done_equiv; auto.
    }
    destruct min as [|min'].
    1: { (* Apply repeatMatcher'_free_equiv *)
      subst max. replace (NoI.N 0 + delta)%NoI with delta by now destruct delta.
      apply repeatMatcher'_free_equiv; auto.
    }
    (* Now we have min <> 0 *)
    unfold equiv_matcher.
    intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj. unfold equiv_cont.
    intros gm ms inp res fueltree t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
    simpl.
    rewrite Hmaxzero.
    replace (min' - 0) with min' by lia.
    destruct List.Update.Nat.Batch.update as [capreset|] eqn:Hcapreset; simpl; try discriminate.
    rewrite mini_plus_plusminus_one with (mini := min') (plus := delta) by reflexivity.
    specialize (IHfuel min' delta). unfold equiv_matcher in IHfuel. specialize (IHfuel str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj).
    unfold equiv_matcher in Hequiv. specialize (Hequiv str0 _ gl forbgroups _ IHfuel Hgldisj Hdef_forbid_disj).
    set (msreset := match_state _ _ capreset).
    unfold equiv_cont in Hequiv.
    specialize (Hequiv (GroupMap.reset (def_groups lreg) gm) msreset inp res).
    intro Hressucc. destruct fueltree as [|fueltree]; simpl; try discriminate.
    destruct (compute_tree _ inp (GroupMap.reset _ _) dir fueltree) as [titer|] eqn:Htitersucc; simpl; try discriminate.
    intro H. injection H as <-.
    simpl. eapply Hequiv; eauto.
    - eapply equiv_gm_ms_reset; eauto.
    - eapply equiv_open_groups_reset; eauto.
    - destruct ms. eapply ms_matches_inp_capchg; eauto.
    - unfold msreset. apply ms_valid_wrt_checks_inpcap with (winp' := MatchState.input ms) (cap' := MatchState.captures ms).
      do 2 apply ms_valid_wrt_checks_Areg. apply ms_valid_wrt_checks_tail in Hmschecks. now destruct ms.
    - now apply gm_reset_valid.
    - eapply noforb_reset; eauto.
  Qed.

  Corollary repeatMatcher_equiv:
    forall greedy parenIndex parenCount rer,
    forall (m: Matcher) (lreg: regex) (dir: Direction),
      equiv_matcher m lreg rer dir ->
      def_groups lreg = List.seq (parenIndex + 1) parenCount ->
      forall min delta, equiv_matcher
        (fun ms mc => Semantics.repeatMatcher m min (NoI.N min + delta)%NoI greedy ms mc parenIndex parenCount)
        (Regex.Quantified greedy min delta lreg) rer dir.
  Proof.
  Admitted.


  (* Linking CharSet.exist_canonicalized and CharSet.contains *)
  Lemma exist_canonicalized_contains:
    forall rer charset chr,
    RegExpRecord.ignoreCase rer = false ->
    CharSet.exist_canonicalized rer charset (Character.canonicalize rer chr) = CharSet.contains charset chr.
  Proof.
    intros rer charset chr Hcasesenst.
    rewrite CharSet.exist_canonicalized_equiv. simpl.
    apply Bool.eq_true_iff_eq.
    setoid_rewrite CharSetExt.exist_spec. split.
    - intros [c [Hcontains Heq]]. setoid_rewrite canonicalize_casesenst in Heq. 2,3: assumption. rewrite EqDec.inversion_true in Heq. subst c. now apply CharSetExt.contains_spec.
    - intro Hcontains. exists chr. split. 1: now apply CharSetExt.contains_spec.
      apply EqDec.reflb.
  Qed.



  (* Lemma for character set matchers *)
  Lemma charSetMatcher_noninv_equiv:
    forall charset cd,
      equiv_cd_charset cd charset ->
      forall rer dir,
        RegExpRecord.ignoreCase rer = false ->
        equiv_matcher (Semantics.characterSetMatcher rer charset false dir) (Regex.Character cd) rer dir.
  Proof.
    intros charset cd Hequiv rer dir Hcasesenst.
    unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
    unfold equiv_cont. intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
    unfold Semantics.characterSetMatcher.
    set (nextend := if (dir ==? forward)%wt then _ else _).
    destruct ((nextend <? 0)%Z || _)%bool eqn:Hoob; simpl.
    + (* Out of bounds *)
      intro Hres. injection Hres as <-. destruct fuel as [|fuel]; try discriminate. simpl.
      erewrite read_oob_fail_bool by eauto.
      intro Heqt. injection Heqt as <-. simpl. constructor.
    + (* In bounds *)
      pose proof next_inbounds_nextinp ms inp dir nextend Hmsinp eq_refl Hoob as [inp' Hadv].
      destruct List.Indexing.Int.indexing as [chr|] eqn:Hgetchr; simpl; try discriminate.
      destruct CharSet.CharSetExt.exist_canonicalized eqn:Hexist; simpl.
      * (* Read succeeds *)
        intro Hcontsucc. destruct fuel as [|fuel]; simpl; try discriminate.
        rewrite (proj1 (read_char_success' ms inp chr _ _ rer dir inp' nextend Hequiv Hcasesenst Hmsinp eq_refl Hgetchr Hexist Hadv)).
        destruct compute_tree as [tcont|] eqn:Htcont; simpl; try discriminate.
        intro H. injection H as <-. simpl.
        unfold equiv_cont in Hequivcont.
        rewrite advance_idx_advance_input with (inp' := inp') by assumption.
        eapply Hequivcont with (ms := match_state (MatchState.input ms) nextend (MatchState.captures ms)); eauto.
        3: {
          apply ms_valid_wrt_checks_tail in Hmschecks. destruct dir; simpl in *; constructor; unfold nextend.
          - specialize (Hmschecks inpcheck H). inversion Hmschecks. simpl. lia.
          - specialize (Hmschecks inpcheck H). inversion Hmschecks. simpl. lia.
        }
        (* 3: advancing the end index does not make validity wrt checks false *)
        1: eauto using advance_input_compat.
        eapply ms_matches_inp_adv; eauto. unfold MSInput.advance_ms. now destruct dir.
      * (* Read fails *)
        intro Hcontsucc. injection Hcontsucc as <-.
        destruct fuel as [|fuel]; simpl; try discriminate.
        rewrite (proj1 (read_char_fail' rer ms chr inp inp' dir _ _ nextend Hequiv Hcasesenst Hmsinp eq_refl Hgetchr Hexist Hadv)).
        intro H. injection H as <-. simpl. constructor.
  Qed.

  (* TODO Factorize with non inverted case? *)
  Lemma charSetMatcher_inv_equiv:
    forall charset cd,
      equiv_cd_charset cd charset ->
      forall rer dir,
        RegExpRecord.ignoreCase rer = false ->
        equiv_matcher (Semantics.characterSetMatcher rer charset true dir) (Regex.Character (CdInv cd)) rer dir.
  Proof.
    intros charset cd Hequiv rer dir Hcasesenst.
    unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
    unfold equiv_cont. intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
    unfold Semantics.characterSetMatcher.
    set (nextend := if (dir ==? forward)%wt then _ else _).
    destruct ((nextend <? 0)%Z || _)%bool eqn:Hoob; simpl.
    + (* Out of bounds *)
      intro Hres. injection Hres as <-. destruct fuel as [|fuel]; try discriminate. simpl.
      erewrite read_oob_fail_bool by eauto.
      intro Heqt. injection Heqt as <-. simpl. constructor.
    + (* In bounds *)
      pose proof next_inbounds_nextinp ms inp dir nextend Hmsinp eq_refl Hoob as [inp' Hadv].
      destruct List.Indexing.Int.indexing as [chr|] eqn:Hgetchr; simpl; try discriminate.
      destruct CharSet.CharSetExt.exist_canonicalized eqn:Hexist; simpl.
      * (* Read succeeds *)
        intro Hcontsucc. injection Hcontsucc as <-.
        destruct fuel as [|fuel]; simpl; try discriminate.
        rewrite (proj2 (read_char_success' ms inp chr _ _ rer dir inp' nextend Hequiv Hcasesenst Hmsinp eq_refl Hgetchr Hexist Hadv)).
        intro H. injection H as <-. simpl. constructor.
      * (* Read fails *)
        intro Hcontsucc. destruct fuel as [|fuel]; simpl; try discriminate.
        rewrite (proj2 (read_char_fail' rer ms chr inp inp' dir _ _ nextend Hequiv Hcasesenst Hmsinp eq_refl Hgetchr Hexist Hadv)).
        destruct compute_tree as [tcont|] eqn:Htcont; simpl; try discriminate.
        intro H. injection H as <-. simpl.
        unfold equiv_cont in Hequivcont.
        rewrite advance_idx_advance_input with (inp' := inp') by assumption.
        eapply Hequivcont with (ms := match_state (MatchState.input ms) nextend (MatchState.captures ms)); eauto.
        3: {
          apply ms_valid_wrt_checks_tail in Hmschecks. destruct dir; simpl in *; constructor; unfold nextend.
          - specialize (Hmschecks inpcheck H). inversion Hmschecks. simpl. lia.
          - specialize (Hmschecks inpcheck H). inversion Hmschecks. simpl. lia.
        }
        (* 3: advancing the end index does not make validity wrt checks false *)
        1: eauto using advance_input_compat.
        eapply ms_matches_inp_adv; eauto. unfold MSInput.advance_ms. now destruct dir.
  Qed.

  Lemma characterClassEscape_equiv:
    forall (rer: RegExpRecord) (lroot: regex) (wroot: Regex)
      (root_equiv: equiv_regex wroot lroot),
      RegExpRecord.ignoreCase rer = false ->
    forall esc wreg lreg ctx,
      wreg = AtomEsc (ACharacterClassEsc esc) ->
      Root wroot (wreg, ctx) ->
      equiv_regex' wreg lreg (StaticSemantics.countLeftCapturingParensBefore wreg ctx) ->
      forall m dir,
        Semantics.compileSubPattern wreg ctx rer dir = Success m ->
        equiv_matcher m lreg rer dir.
  Proof.
    intros rer lroot wroot root_equiv Hcasesenst esc wreg lreg ctx -> Hroot Hequiv m dir Hcompilesucc.
    inversion Hequiv.
    - subst esc0 lreg. pose proof equiv_cd_CharacterClassEscape esc cd rer Hcasesenst H0 as [a [HcompileCharSet Hequivcdcs]].
      unfold Semantics.compileSubPattern, Semantics.compileToCharSet, Coercions.ClassAtom_to_range, Coercions.ClassEscape_to_ClassAtom, Coercions.CharacterClassEscape_to_ClassEscape in Hcompilesucc.
      setoid_rewrite HcompileCharSet in Hcompilesucc. simpl in Hcompilesucc.
      injection Hcompilesucc as <-. apply charSetMatcher_noninv_equiv; auto. rewrite CharSetExt.union_empty. auto.
    - inversion H1; congruence.
    - inversion H; congruence.
  Qed.

  Lemma characterEscape_equiv:
    forall (rer: RegExpRecord) (lroot: regex) (wroot: Regex)
      (root_equiv: equiv_regex wroot lroot),
      RegExpRecord.ignoreCase rer = false ->
    forall esc cd ctx,
      Root wroot (AtomEsc (ACharacterEsc esc), ctx) ->
      equiv_CharacterEscape esc cd ->
      forall m dir,
        Semantics.compileSubPattern (AtomEsc (ACharacterEsc esc)) ctx rer dir = Success m ->
        equiv_matcher m (Regex.Character cd) rer dir.
  Proof.
    intros rer lroot wroot Hequivroot Hcasesenst esc cd ctx Hroot Hequiv m dir.
    inversion Hequiv as [controlesc cd0 Hequiv'' Heqesc Heqcd0 | l cd0 Hequiv'' Heqesc Heqcd0 | Heqesc Heqcd | d1 d2 Heqesc Heqcd].
    - inversion Hequiv'' as [Heqcontrolesc Heqcd | Heqcontrolesc Heqcd | Heqcontrolesc Heqcd | Heqcontrolesc Heqcd | Heqcontrolesc Heqcd]; simpl; intro H; injection H as <-;
      eapply charSetMatcher_noninv_equiv; eauto; unfold nat_to_nni; rewrite Character.numeric_pseudo_bij; apply equiv_cd_single.
    - inversion Hequiv'' as [l0 i Heqi Heql0 Heqcd].
      simpl. rewrite <- Heqi. intro H. injection H as <-.
      eapply charSetMatcher_noninv_equiv; eauto. apply equiv_cd_single.
    - simpl; intro H; injection H as <-; eapply charSetMatcher_noninv_equiv; eauto; unfold nat_to_nni; rewrite Character.numeric_pseudo_bij; apply equiv_cd_single.
    - simpl. intro H. injection H as <-. eapply charSetMatcher_noninv_equiv; eauto. apply equiv_cd_single.
  Qed.

  Lemma characterClass_equiv:
    forall (rer: RegExpRecord) (lroot: regex) (wroot: Regex)
      (root_equiv: equiv_regex wroot lroot),
      RegExpRecord.ignoreCase rer = false ->
      forall cc cd ctx,
        Root wroot (CharacterClass cc, ctx) ->
        equiv_CharClass cc cd ->
        forall m dir,
          Semantics.compileSubPattern (CharacterClass cc) ctx rer dir = Success m ->
          equiv_matcher m (Regex.Character cd) rer dir.
  Proof.
    intros rer lroot wroot root_equiv Hcasesenst cc cd ctx Hroot Hequiv' m dir.
    inversion Hequiv' as [crs cd0 Hequiv'' Heqcc' Heqcd0 | crs cd0 Hequiv'' Heqcc' Heqcd0]; simpl.
    - pose proof equiv_cd_ClassRanges crs cd rer Hcasesenst Hequiv'' as [a [Heqa Hequiva]]. setoid_rewrite Heqa. simpl.
      intro H. injection H as <-. eapply charSetMatcher_noninv_equiv; eauto.
    - subst cd. pose proof equiv_cd_ClassRanges crs cd0 rer Hcasesenst Hequiv'' as [a [Heqa Hequiva]]. setoid_rewrite Heqa. simpl.
      intro H. injection H as <-. eapply charSetMatcher_inv_equiv; eauto.
  Qed.


  (* Lemma for backreferences *)
  Lemma backref_equiv:
    forall gid rer dir
      (Hcasesenst: RegExpRecord.ignoreCase rer = false)
      (Hnomultiline: RegExpRecord.multiline rer = false)
      (Hdotall: RegExpRecord.dotAll rer = true),
      equiv_matcher (Semantics.backreferenceMatcher rer gid dir)
        (Backreference (positive_to_nat gid)) rer dir.
  Proof.
    intros. unfold equiv_matcher.
    intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
    unfold equiv_cont. intros gm ms [next pref] res [|fuel] t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforb; try discriminate.
    pose proof ms_matches_inp_inbounds ms _ Hmsinp as Hmsinb.
    simpl in *. unfold Semantics.backreferenceMatcher, read_backref.
    destruct indexing as [r|] eqn:Heqr; simpl; try discriminate.
    destruct r as [[startIdx endIdx]|] eqn:Hr; simpl.
    - (* Range is defined *)
      pose proof equiv_gm_ms_indexing_find_nonneg gm ms gid startIdx endIdx Hgmms Heqr as [Hfind [HstartIdxnneg HendIdxnneg]].
      rewrite Hfind.
      set (rlen := (endIdx - startIdx)%Z).
      assert (Hrlennneg: (rlen >= 0)%Z). {
        unfold gm_valid in Hgmvalid. specialize (Hgmvalid (positive_to_nat gid)).
        rewrite Hfind in Hgmvalid. inversion Hgmvalid. lia.
      }
      replace (Z.to_nat endIdx - Z.to_nat startIdx) with (Z.to_nat rlen) by lia.
      destruct dir; simpl.
      + (* Forward *)
        set (endMatch := (MatchState.endIndex ms + rlen)%Z).
        replace (endMatch <? 0)%Z with false by lia. simpl.
        assert (Hoobiff: (endMatch >? Z.of_nat (length (MatchState.input ms)))%Z = true <->
          (Z.to_nat rlen >? length next) = true) by eauto using endMatch_oob_forward.
        simpl in Hoobiff.
        rewrite <- Bool.eq_iff_eq_true in Hoobiff. rewrite <- Hoobiff.
        destruct Z.gtb eqn:Hoob.
        * (* Out of bounds *)
          intros H1 H2. injection H1 as <-. injection H2 as <-. constructor.
        * (* In bounds *)
          destruct List.Exists.exist as [existsdiff|] eqn:Hexistsdiffres; simpl; try discriminate.
          assert (Hexistsdiffiff : existsdiff = true <-> (List.firstn (Z.to_nat rlen) next ==? substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx))%wt = false) by eauto using exists_diff_iff.
          rewrite Bool.negb_involutive_reverse with (b := existsdiff) in Hexistsdiffiff.
          rewrite Bool.negb_true_iff in Hexistsdiffiff.
          destruct existsdiff.
          -- (* Some character is different *)
             destruct Hexistsdiffiff as [Hexistsdiffiff _]. rewrite Hexistsdiffiff by reflexivity.
             intros H1 H2. injection H1 as <-. injection H2 as <-. constructor.
          -- (* No character is different *)
             assert (Hfirstn_next_substr: (List.firstn (Z.to_nat rlen) next ==?
               substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx))%wt = true). {
               symmetry. destruct EqDec.eqb; try reflexivity.
               destruct Hexistsdiffiff. discriminate (H0 eq_refl).
             }
             rewrite Hfirstn_next_substr. rewrite EqDec.inversion_true in Hfirstn_next_substr.
             set (ms' := match_state _ _ _). set (inp' := Input _ _).
             assert (Hms'inp': ms_matches_inp ms' inp'). { eapply msinp_backref_fwd; eauto. all: reflexivity. }
             assert (Hinp'compat: input_compat inp' str0). { eapply msinp_backref_fwd with (next := next) (pref := pref); eauto. reflexivity. }
             intro Hres.
             destruct compute_tree as [tcont|] eqn:Htcont; try discriminate.
             intro H. injection H as <-. simpl.
             unfold equiv_cont in Hequivcont.
             replace (length pref + length _) with (idx inp'). 2: { symmetry; eapply backref_inp'_idx_fwd; eauto. }
             apply Hequivcont with (ms := ms') (fuel := fuel); auto.
             (* Remains to prove that the new MatchState remains valid with respect to the checks in act *)
             apply ms_valid_wrt_checks_tail in Hmschecks.
             unfold ms_valid_wrt_checks. intros inpcheck Hcheckin.
             specialize (Hmschecks inpcheck Hcheckin). inversion Hmschecks as [ms0 inpcheck0 Hendge |]. subst ms0 inpcheck0.
             constructor.
             assert (MatchState.endIndex ms' >= MatchState.endIndex ms)%Z. {
               unfold ms', endMatch. simpl. lia. 
             }
             lia.
      + (* Backward *)
        replace (MatchState.endIndex ms - rlen >? Z.of_nat (length (MatchState.input ms)))%Z with false by lia.
        rewrite Bool.orb_false_r.
        assert (Hoobiff: (MatchState.endIndex ms - rlen <? 0)%Z = true <-> (Z.to_nat rlen >? length pref) = true) by eauto using beginMatch_oob_backward.
        rewrite <- Bool.eq_iff_eq_true in Hoobiff. simpl in Hoobiff.
        rewrite <- Hoobiff.
        destruct Z.ltb.
        * (* Out of bounds *)
          intros H1 H2. injection H1 as <-. injection H2 as <-. constructor.
        * (* In bounds *)
          destruct List.Exists.exist as [existsdiff|] eqn:Hexistsdiffres; simpl; try discriminate.
          assert (HbeginMatchinb: (MatchState.endIndex ms - rlen >= 0)%Z). {
            (* The fact that List.Exists.exist succeeds means that indexing the first character succeeds *)
            unfold List.Range.Int.Bounds.range in Hexistsdiffres. replace (rlen - 0)%Z with rlen in Hexistsdiffres by lia.
            destruct (Z.to_nat rlen) eqn:Hrlennat.
            1: { replace rlen with 0%Z by lia. lia. }
            simpl in Hexistsdiffres.
            destruct List.Indexing.Int.indexing in Hexistsdiffres; simpl in *; try discriminate.
            replace (Z.min _ _ + 0)%Z with (MatchState.endIndex ms - rlen)%Z in Hexistsdiffres by lia.
            destruct List.Indexing.Int.indexing as [gi|] eqn:Hindexingfirst in Hexistsdiffres; simpl in *; try discriminate.
            apply List.Indexing.Int.success_bounds in Hindexingfirst. lia.
          }
          assert (Hexistsdiffiff : existsdiff = true <-> (List.rev (List.firstn (Z.to_nat rlen) pref) ==? substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx))%wt = false) by
            eauto using exists_diff_iff_bwd.
          rewrite Bool.negb_involutive_reverse with (b := existsdiff) in Hexistsdiffiff.
          rewrite Bool.negb_true_iff in Hexistsdiffiff.
          destruct existsdiff.
          -- (* Some character is different *)
             destruct Hexistsdiffiff as [Hexistsdiffiff _]. rewrite Hexistsdiffiff by reflexivity.
             intros H1 H2. injection H1 as <-. injection H2 as <-. constructor.
          -- (* No character is different *)
             assert (Hfirstn_pref_substr: (List.rev (List.firstn (Z.to_nat rlen) pref) ==?
               substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx))%wt = true). {
               symmetry. destruct EqDec.eqb; try reflexivity.
               destruct Hexistsdiffiff. discriminate (H0 eq_refl).
             }
             rewrite Hfirstn_pref_substr. rewrite EqDec.inversion_true in Hfirstn_pref_substr.
             set (ms' := match_state _ _ _). set (inp' := Input _ _).
             assert (Hms'inp': ms_matches_inp ms' inp'). { eapply msinp_backref_bwd with (next := next) (pref := pref) (rlen := rlen); eauto. reflexivity. }
             assert (Hinp'compat: input_compat inp' str0). { eapply msinp_backref_bwd with (next := next) (pref := pref) (rlen := rlen); eauto. }
             intro Hres.
             destruct compute_tree as [tcont|] eqn:Htcont; try discriminate.
             intro H. injection H as <-. simpl.
             unfold equiv_cont in Hequivcont.
             replace (length pref - length _) with (idx inp').
             2: { symmetry. eapply backref_inp'_idx_bwd; eauto.
             inversion Hmsinp. subst next0 pref0 ms. simpl in *.
             lia. }
             apply Hequivcont with (ms := ms') (fuel := fuel); auto.
             (* Remains to prove that the new MatchState remains valid with respect to the checks in act *)
             apply ms_valid_wrt_checks_tail in Hmschecks.
             unfold ms_valid_wrt_checks. intros inpcheck Hcheckin.
             specialize (Hmschecks inpcheck Hcheckin). inversion Hmschecks as [|ms0 inpcheck0 Hendge]. subst ms0 inpcheck0.
             constructor.
             assert (MatchState.endIndex ms' <= MatchState.endIndex ms)%Z. {
               unfold ms'. simpl. lia. 
             }
             lia.
    - (* Range is undefined *)
      destruct GroupMap.find as [[startIdx [endIdx|]]|] eqn:Hfind.
      + exfalso. eapply equiv_gm_ms_indexing_none; eauto.
      + destruct compute_tree as [tcont|] eqn:Htcont; try discriminate.
        intros Hres H. injection H as <-.
        simpl.
        replace (Tree.advance_idx_n (length pref) 0 dir) with (idx (Input next pref)). 2: {
          unfold Tree.advance_idx_n. simpl.
          destruct dir; lia.
        }
        apply Hequivcont with (ms := ms) (fuel := fuel); auto.
        now apply ms_valid_wrt_checks_tail in Hmschecks.
      + (* Copy-pasting *)
        destruct compute_tree as [tcont|] eqn:Htcont; try discriminate.
        intros Hres H. injection H as <-.
        simpl.
        replace (Tree.advance_idx_n (length pref) 0 dir) with (idx (Input next pref)). 2: {
          unfold Tree.advance_idx_n. simpl.
          destruct dir; lia.
        }
        apply Hequivcont with (ms := ms) (fuel := fuel); auto.
        now apply ms_valid_wrt_checks_tail in Hmschecks.
  Qed.

  (* Main equivalence theorem: *)
  Theorem equiv:
    forall (rer: RegExpRecord) (lroot: regex) (wroot: Regex)
      (* Assume that we do not ignore case, *)
      (Hcasesenst: RegExpRecord.ignoreCase rer = false)
      (* that we do not consider line ends and starts to be input ends and starts, respectively, *)
      (Hnomultiline: RegExpRecord.multiline rer = false)
      (* and that dot matches all characters. *)
      (Hdotall: RegExpRecord.dotAll rer = true)
      (* Let lroot and wroot be a pair of equivalent regexes. *)
      (root_equiv: equiv_regex wroot lroot),
      (* Then for any sub-regex wreg of the root Warblre regex, *)
    forall (wreg: Regex) (lreg: regex) ctx
      (Hroot: Root wroot (wreg, ctx))
      (* and any Linden regex lreg that is equivalent to this sub-regex with the right number of left capturing parentheses before, *)
      (Hequiv: equiv_regex' wreg lreg (StaticSemantics.countLeftCapturingParensBefore wreg ctx)),
      forall m dir
        (* if compileSubPattern with direction dir yields a Matcher for regex wreg, *)
        (Hcompsucc: Semantics.compileSubPattern wreg ctx rer dir = Success m),
        (* then this Matcher is equivalent to the regex lreg and direction dir. *)
        equiv_matcher m lreg rer dir.
  Proof.
    do 12 intro.
    remember (StaticSemantics.countLeftCapturingParensBefore _ _) as n in Hequiv.
    revert ctx Hroot Heqn.
    induction Hequiv as [
        n |
        n c |
        n |
        n |
        esc cd n Hequivesc |
        esc cd n Hequivesc |
        cc cd n Hequivcc |
        n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
        n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
        n wr lr wquant lquant wgreedylazy greedy Hequiv IH Hequivquant Hequivgreedy |
        name n wr lr Hequiv IH |
        n wr lr wlk llk Hequiv IH Hequivlk |
        n wr lanchor Hanchequiv
    ].

    - (* Epsilon *)
      intros ctx _ _ m dir. simpl.
      intro. injection Hcompsucc as <-.
      unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont _ _.
      unfold equiv_cont. intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden Hmcsucc.
      destruct fuel as [|fuel]; try discriminate.
      simpl.
      intro Hsubtreesucc.
      eapply Hequivcont; eauto using ms_valid_wrt_checks_tail.
  
    - (* Character *)
      intros ctx Hroot Heqn m dir Hcompsucc.
      injection Hcompsucc as <-.
      apply charSetMatcher_noninv_equiv; auto. apply equiv_cd_single.
    
    - (* Dot *)
      intros ctx Hroot Heqn m dir Hcompsucc.
      injection Hcompsucc as <-.
      apply charSetMatcher_noninv_equiv; auto. rewrite Hdotall. apply equiv_cd_dot.

    - (* Backreference *)
      intros crx Hroot Heqn m dir. simpl.
      destruct Nat.leb eqn:Hgidinbounds; try discriminate. simpl.
      intro H. injection H as <-.
      auto using backref_equiv.
    
    - (* AtomEsc (ACharacterClassEsc esc); idem *)
      intros ctx Hroot Heqn m dir Hcompsucc.
      eapply characterClassEscape_equiv; eauto. constructor. assumption.
    
    - (* AtomEsc (ACharacterEsc esc); idem *)
      intros ctx Hroot Heqn m dir Hcompsucc.
      eapply characterEscape_equiv; eauto.
    
    - (* CharacterClass; idem *)
      intros ctx Hroot Heqn m dir Hcompsucc.
      eapply characterClass_equiv; eauto.

    - (* Disjunction *)
      intros ctx Hroot Heqn m dir.
      simpl.
      (* Compilation of the two sub-regexes succeeds *)
      destruct Semantics.compileSubPattern as [m1|] eqn:Hcompsucc1; simpl; try discriminate.
      destruct (Semantics.compileSubPattern _ (Disjunction_right _ :: ctx)) as [m2|] eqn:Hcompsucc2; simpl; try discriminate.
      intro H. injection H as <-.
      (* Specialize the induction hypotheses naturally *)
      specialize (IH1 (Disjunction_left wr2 :: ctx)%list).
      specialize_prove IH1 by eauto using Down.same_root_down0, Down_Disjunction_left.
      specialize_prove IH1. { simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. lia. }
      specialize (IH1 m1 dir Hcompsucc1).
      specialize (IH2 (Disjunction_right wr1 :: ctx)%list).
      specialize_prove IH2 by eauto using Down.same_root_down0, Down_Disjunction_right.
      specialize_prove IH2. { simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. erewrite num_groups_equiv by eauto. lia. }
      specialize (IH2 m2 dir Hcompsucc2).
      (* Introduce the required variables *)
      unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
      unfold equiv_cont. intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
      unfold equiv_matcher in IH1, IH2.
      (* Specialize the induction hypotheses again naturally *)
      specialize (IH1 str0 mc gl forbgroups act Hequivcont).
      specialize_prove IH1 by eauto using disj_parent_disj_child, Child_Disjunction_left.
      specialize_prove IH1 by eauto using disj_forbidden_child, Child_Disjunction_left.
      specialize (IH2 str0 mc gl forbgroups act Hequivcont).
      specialize_prove IH2 by eauto using disj_parent_disj_child, Child_Disjunction_right.
      specialize_prove IH2 by eauto using disj_forbidden_child, Child_Disjunction_right.
      unfold equiv_cont in IH1, IH2.
      (* Eliminate failing cases *)
      destruct fuel as [|fuel]; simpl; try discriminate.
      destruct m1 as [res1|] eqn:Hres1; simpl; try discriminate.
      destruct compute_tree as [t1|] eqn:Ht1; simpl; try discriminate.
      destruct (compute_tree (Areg lr2 :: act)%list _ _ _ _) as [t2|] eqn:Ht2; simpl; try discriminate.
      specialize (IH1 gm ms inp res1 fuel t1 Hinpcompat Hgmms Hgmgl Hmsinp).
      specialize_prove IH1. { apply ms_valid_wrt_checks_Areg. eauto using ms_valid_wrt_checks_tail. }
      specialize (IH1 Hgmvalid).
      specialize_prove IH1. { apply noforbidden_child with (parent := Regex.Disjunction lr1 lr2).
        - apply Child_Disjunction_left.
        - intros [greedy [min [delta [rsub Habs]]]]; discriminate.
        - assumption. }
      specialize (IH1 Hres1 Ht1).
      (* Case analysis on whether the left branch matches *)
      destruct res1 as [msres1|] eqn:Hmsres1; simpl.
      + (* Left choice matches *)
        intro H. injection H as <-. intro H. injection H as <-.
        simpl.
        inversion IH1 as [ | gm1 msres1' IH1' Heqgm1 Heqmsres1' ]. simpl. constructor. assumption.
      + (* Left choice does not match *)
        rename res into res2.
        intros Hres2 H. injection H as <-. simpl.
        inversion IH1 as [ HNone1 | ]. simpl.
        eapply IH2; eauto.
        * apply ms_valid_wrt_checks_Areg. eauto using ms_valid_wrt_checks_tail.
        * apply noforbidden_child with (parent := Regex.Disjunction lr1 lr2).
          -- apply Child_Disjunction_right.
          -- intros [greedy [min [delta [rsub Habs]]]]; discriminate.
          -- assumption.

    - (* Sequence *)
      intros ctx Hroot Heqn m dir. simpl.
      (* Compilation of the two sub-regexes succeeds *)
      destruct Semantics.compileSubPattern as [m1|] eqn:Hcompsucc1; simpl; try discriminate.
      destruct (Semantics.compileSubPattern _ (Seq_right _ :: ctx)%list) as [m2|] eqn:Hcompsucc2; simpl; try discriminate.
      (* Specialize the induction hypotheses naturally *)
      specialize (IH1 (Seq_left wr2 :: ctx)%list).
      specialize_prove IH1 by eauto using Down.same_root_down0, Down_Seq_left.
      specialize_prove IH1. { simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. lia. }
      specialize (IH1 m1 dir Hcompsucc1).
      specialize (IH2 (Seq_right wr1 :: ctx)%list).
      specialize_prove IH2 by eauto using Down.same_root_down0, Down_Seq_right.
      specialize_prove IH2. { simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. erewrite num_groups_equiv by eauto. lia. }
      specialize (IH2 m2 dir Hcompsucc2).
      (* Two similar reasonings for each direction *)
      destruct dir; intro H; injection H as <-.
      + (* Forward *)
        unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
        unfold equiv_cont. intros gm ms inp res [|fuel] t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden; try discriminate; simpl.
        set (mc2 := fun s => _).
        assert (Hequivcont2: equiv_cont mc2 gl (forbidden_groups lr2 ++ forbgroups) (Areg lr2 :: act)%list forward str0 rer). {
          unfold equiv_cont. clear gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
          intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hnoforbidden. unfold mc2.
          intros Hres Ht. eapply IH2; eauto.
          1: eauto using disj_parent_disj_child, Child_Sequence_right.
          eauto using disj_forbidden_child, Child_Sequence_right.
        }
        intros Hres Ht. eapply IH1; eauto.
        * eauto using disj_parent_disj_child, Child_Sequence_left.
        * eauto using disj_forbidden_seq.
        * do 2 apply ms_valid_wrt_checks_Areg. eauto using ms_valid_wrt_checks_tail.
        * now apply noforbidden_seq.

      + (* Backward *)
        unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
        unfold equiv_cont. intros gm ms inp res [|fuel] t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden; try discriminate; simpl.
        set (mc1 := fun s => _).
        assert (Hequivcont1: equiv_cont mc1 gl (forbidden_groups lr1 ++ forbgroups) (Areg lr1 :: act)%list backward str0 rer). {
          unfold equiv_cont. clear gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
          intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hnoforbidden. unfold mc1.
          intros Hres Ht. eapply IH1; eauto.
          1: eauto using disj_parent_disj_child, Child_Sequence_left.
          eauto using disj_forbidden_child, Child_Sequence_left. (* Same as forward *)
        }
        intros Hres Ht. eapply IH2; eauto.
        * eauto using disj_parent_disj_child, Child_Sequence_right.
        * eauto using disj_forbidden_seq_bwd.
        * do 2 apply ms_valid_wrt_checks_Areg. eauto using ms_valid_wrt_checks_tail.
        * now apply noforbidden_seq_bwd.

    - (* Quantified *)
      intros ctx Hroot Heqn m dir. simpl.
      destruct Semantics.compileSubPattern as [msub|] eqn:Hcompsuccsub; simpl; try discriminate.
      specialize (IH (Quantified_inner (wgreedylazy wquant)::ctx)%list).
      specialize_prove IH by eauto using Down.same_root_down0, Down_Quantified_inner.
      specialize_prove IH. {
        simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. lia.
      }
      specialize (IH msub dir Hcompsuccsub).
      set (min := Semantics.CompiledQuantifier_min _).
      set (max := Semantics.CompiledQuantifier_max _).
      rewrite compilequant_greedy with (lquant := lquant) (greedy := greedy) by assumption.
      set (parenIndex := StaticSemantics.countLeftCapturingParensBefore _ ctx).
      set (parenCount := StaticSemantics.countLeftCapturingParensWithin _ _).
      destruct (min <=? max)%NoI eqn:Hmini_le_maxi; simpl; try discriminate.
      intro H. injection H as <-.
      rewrite <- noi_add_diff with (x := min) (y := max) by assumption.
      pose proof equiv_def_groups wr lr n parenCount (Quantified_inner (wgreedylazy wquant) :: ctx)%list Hequiv eq_refl as Hgroupsvalid.
      rewrite Heqn in Hgroupsvalid. replace (StaticSemantics.countLeftCapturingParensBefore _ _) with parenIndex in Hgroupsvalid. 2: {
        unfold parenIndex, StaticSemantics.countLeftCapturingParensBefore. reflexivity.
      }
      inversion Hequivquant as [
          Heqwquant Heqlquant |
          Heqwquant Heqlquant |
          Heqwquant Heqlquant |
          nrep Heqwquant Heqlquant |
          nmin Heqwquant Heqlquant |
          mini' maxi' Hle' Heqwquant Heqlquant]; subst wquant lquant;
      inversion Hequivgreedy as [Heqwgl Heqgreedy | Heqwgl Heqgreedy]; subst wgreedylazy greedy; simpl in *; try apply repeatMatcher_equiv; auto.
      all: replace (nrep - min) with 0 by lia; apply repeatMatcher_equiv; auto.

    - (* Group *)
      intros ctx Hroot Heqn m dir. simpl.
      destruct Semantics.compileSubPattern as [msub | ] eqn:Hcompsuccsub; simpl; try discriminate.
      intro H. injection H as <-.
      unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
      unfold equiv_cont. intros gm ms inp res [|fuel] t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden; simpl; try discriminate.
      set (mcclose := fun (y: MatchState) => _).
      assert (Hequivmcclose: equiv_cont mcclose ((S n, idx inp)::gl)%list forbgroups (Aclose (S n)::act)%list dir str0 rer). {
        unfold equiv_cont. intros gm' ms' inp' res' [|fuel'] t' Hinp'compat Hgm'ms' Hgm'gl' Hms'inp' Hms'checks Hgm'valid Hnoforbidden'; simpl; try discriminate.
        destruct compute_tree as [treecont|] eqn:Htreecont; simpl; try discriminate.
        unfold mcclose.
        set (rres := if (dir ==? forward)%wt then _ else _). destruct rres as [r|] eqn:Hrres; simpl; try discriminate.
        replace (StaticSemantics.countLeftCapturingParensBefore _ ctx + 1) with (S n) by lia.
        simpl. replace (n - 0) with n by lia.
        destruct List.Update.Nat.One.update as [cap'|] eqn:Heqcap'; simpl; try discriminate.
        intros Hres' Ht'. injection Ht' as <-. simpl.
        eapply Hequivcont with (ms := match_state (MatchState.input ms) (MatchState.endIndex ms') cap'); eauto.
        - eapply equiv_gm_ms_close_group; eauto.
        - eapply equiv_open_groups_close_group; eauto.
        - eapply ms_matches_inp_close_group; eauto.
        - apply ms_valid_wrt_checks_inpcap with (winp' := MatchState.input ms') (cap' := MatchState.captures ms'). destruct ms'; simpl. eauto using ms_valid_wrt_checks_tail.
        - auto using gm_close_valid.
        - eauto using noforb_close_group.
      }
      destruct compute_tree as [treecont|] eqn:Htreecont; simpl; try discriminate.
      intros Hres H. injection H as <-. simpl.
      eapply IH; eauto.
      + eauto using Down.same_root_down0, Down_Group_inner.
      + simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. lia.
      + eauto using open_groups_disjoint_open_group. (* Group list disjointness; follows from Hgldisj and Hequiv (for group S n) *)
      + eauto using disj_forbidden_child, Child_Group.
      + eauto using equiv_gm_ms_open_group. (* Group map equivalence after opening a group; follows from Hnoforbidden (!) *)
      + eauto using equiv_gm_gl_open_group. (* Group map equivalence to open groups after opening a group *)
      + apply ms_valid_wrt_checks_Areg, ms_valid_wrt_checks_Aclose. eauto using ms_valid_wrt_checks_tail.
      + auto using gm_open_valid.
      + eauto using noforb_open_group. (* Follows from Hnoforbidden (groups other than S n), Hdef_forbid_disj and Hequiv (S n) *)

    - (* Lookaround *)
      intros ctx Hroot Heqn m dir.
      inversion Hequivlk as [Heqwlk Heqllk | Heqwlk Heqllk | Heqwlk Heqllk | Heqwlk Heqllk]; simpl.
      + (* Positive lookahead; need to factorize with other cases later *)
        subst wlk llk.
        destruct Semantics.compileSubPattern as [msub|] eqn:Hcompsuccsub; simpl; try discriminate.
        specialize (IH (Lookahead_inner :: ctx)%list).
        specialize_prove IH by eauto using Down.same_root_down0, Down_Lookahead_inner.
        specialize_prove IH. { simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. lia. }
        specialize (IH msub forward Hcompsuccsub).
        intro H. injection H as <-.
        unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
        unfold equiv_cont. intros gm ms inp res [|fuel] t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden; simpl; try discriminate.
        unfold equiv_matcher in IH. specialize (IH str0 id_mcont gl nil nil).
        specialize_prove IH by now apply id_equiv. specialize (IH Hgldisj). specialize_prove IH by apply List.Disjoint_nil_r.
        unfold equiv_cont in IH. specialize (IH gm ms inp).
        destruct msub as [rlk|] eqn:Hrlk; simpl; try discriminate.
        destruct compute_tree as [tlk|] eqn:Htlk; simpl; try discriminate.
        specialize (IH rlk fuel tlk Hinpcompat Hgmms Hgmgl Hmsinp).
        specialize_prove IH. {
          unfold ms_valid_wrt_checks. intros inpcheck H. destruct H; [discriminate|inversion H].
        }
        specialize (IH Hgmvalid).
        specialize_prove IH by admit. (* Follows from Hnoforbidden *)
        specialize (IH eq_refl Htlk).
        unfold lk_succeeds. simpl. unfold Tree.first_branch, lk_group_map. simpl.
        destruct rlk as [rlk|]; simpl.
        * (* Lookaround succeeds *)
          inversion IH as [|gmafterlk rlk' Hequivafterlk Heqgmafterlk Heqrlk']. subst rlk'.
          replace (Tree.tree_res tlk _ 0 forward is not None) with true.
          2: {
            symmetry. destruct (Tree.tree_res tlk GroupMap.empty 0 forward) eqn:Hreslk; try reflexivity.
            symmetry in Heqgmafterlk. apply Tree.res_group_map_indep with (gm2 := gm) (idx2 := idx inp) (dir2 := forward) in Hreslk. congruence.
          }
          set (msafterlk := match_state _ _ _).
          unfold equiv_cont in Hequivcont. specialize (Hequivcont gmafterlk msafterlk inp res fuel).
          destruct (compute_tree act inp gmafterlk dir fuel) as [treecont|] eqn:Heqtreecont; simpl; try discriminate.
          specialize (Hequivcont treecont Hinpcompat).
          specialize_prove Hequivcont by eauto using equiv_gmafterlk_msafterlk. (* Only depends on captures, follows from Hequivafterlk *)
          specialize_prove Hequivcont by eauto using equiv_open_groups_lk. (* Follows from Hgmgl, Heqgmafterlk, Htlk and Hnoforbidden; see paper reasoning (non-trivial, but should not depend on compileSubPattern) *)
          specialize_prove Hequivcont. { unfold msafterlk. apply ms_matches_inp_capchg with (cap := MatchState.captures ms). now destruct ms. }
          specialize_prove Hequivcont. { unfold msafterlk. apply ms_valid_wrt_checks_inpcap with (winp' := MatchState.input ms) (cap' := MatchState.captures ms). apply ms_valid_wrt_checks_tail in Hmschecks. now destruct ms. }
          specialize_prove Hequivcont by admit. (* tree_res preserves validity of group maps *)
          specialize_prove Hequivcont by eauto using noforb_lk. (* Follows from Hnoforbidden, Heqgmafterlk and Htlk; non-trivial but should not depend on compileSubPattern *)
          intro Hcontsucc. specialize (Hequivcont Hcontsucc eq_refl).
          intro H. injection H as <-.
          simpl. rewrite <- Heqgmafterlk. assumption.
        * (* Lookaround fails *)
          inversion IH as [Htreeresnone|].
          intro H. injection H as <-.
          replace (Tree.tree_res tlk _ 0 forward is not None) with false.
          2: {
            symmetry. destruct (Tree.tree_res tlk _ 0 forward) eqn:Hreslk; try reflexivity.
            symmetry in Htreeresnone. apply Tree.res_group_map_indep with (gm2 := GroupMap.empty) (idx2 := 0) (dir2 := forward) in Htreeresnone. congruence.
          }
          intro H. injection H as <-.
          simpl. constructor.
      
      + admit.
      + admit.
      + admit.

    - (* Anchor *)
      admit.
  Admitted.
End Equiv.
