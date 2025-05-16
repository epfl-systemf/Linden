From Linden Require Import EquivDef RegexpTranslation Regex LindenParameters
  Semantics LWEquivTreeLemmas CharDescrCharSet Tactics.
From Warblre Require Import Parameters Semantics RegExpRecord Patterns
  Node Result Notation Typeclasses List Base Node.
Import Patterns.
Import Result.Notations.
Import Notation.
Import NodeProps.Zipper.
From Coq Require Import ZArith PeanoNat Lia.

Local Open Scope result_flow.

Section Equiv.
  Context `{characterClass: Character.class}.

  Theorem equiv:
    forall (rer: RegExpRecord) (lroot: regex) (wroot: Regex)
      (* Assume that we do not ignore case, *)
      (Hcasesenst: RegExpRecord.ignoreCase rer = false)
      (* that we do not consider line ends and starts to be input ends and starts, respectively, *)
      (Hnomultiline: RegExpRecord.multiline rer = false)
      (* and that dot matches all characters. *)
      (Hdotall: RegExpRecord.dotAll rer = true)
      (* Let lroot and wroot be a pair of equivanent regexes. *)
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
        equiv_matcher m lreg dir.
  Proof.
    do 12 intro.
    remember (StaticSemantics.countLeftCapturingParensBefore _ _) as n in Hequiv.
    revert ctx Hroot Heqn.
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
        n wr lanchor Hanchequiv
    ].

    - (* Epsilon *)
      intros ctx _ _ m dir. simpl.
      intro. injection Hcompsucc as <-.
      unfold equiv_matcher. intros mc gl act Hequivcont _.
      unfold equiv_cont. intros gm ms inp res fuel t Hgmms Hgmgl Hmsinp Hmcsucc.
      destruct fuel as [|fuel]; try discriminate.
      simpl.
      intro Hsubtreesucc.
      eauto using Hequivcont.
  
    - (* Character *)
      intros ctx Hroot Heqn m dir Hcompsucc.
      injection Hcompsucc as <-.
      unfold equiv_matcher. intros mc gl act Hequivcont Hgldisj.
      unfold equiv_cont. intros gm ms inp res fuel t Hgmms Hgmgl Hmsinp.
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
          unshelve erewrite (proj1 (read_char_success' ms inp chr _ _ rer dir inp' nextend _ Hcasesenst Hmsinp eq_refl Hgetchr Hexist Hadv)).
          1: apply equiv_cd_single.
          destruct compute_tree' as [tcont|] eqn:Htcont; simpl; try discriminate.
          intro H. injection H as <-. simpl.
          unfold equiv_cont in Hequivcont.
          replace (Tree.advance_idx _ _) with (idx inp') by admit.
          eapply Hequivcont with (ms := match_state (MatchState.input ms) nextend (MatchState.captures ms)); eauto.
          eapply ms_matches_inp_adv; eauto. unfold MSInput.advance_ms. now destruct dir.
        * (* Read fails *)
          intro Hcontsucc. injection Hcontsucc as <-.
          destruct fuel as [|fuel]; simpl; try discriminate.
          unshelve erewrite (proj1 (read_char_fail' rer ms chr inp inp' dir _ _ nextend _ Hcasesenst Hmsinp eq_refl Hgetchr Hexist Hadv)).
          1: apply equiv_cd_single.
          intro H. injection H as <-. simpl. constructor.
    
    - (* Dot; probably very similar to character *)
      admit.
    
    - (* AtomEsc (ACharacterClassEsc esc); idem *)
      admit.
    
    - (* AtomEsc (ACharacterEsc esc); idem *)
      admit.
    
    - (* CharacterClass; idem *)
      admit.

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
      unfold equiv_matcher. intros mc gl act Hequivcont Hgldisj.
      unfold equiv_cont. intros gm ms inp res fuel t Hgmms Hgmgl Hmsinp.
      unfold equiv_matcher in IH1, IH2.
      (* Specialize the induction hypotheses again naturally *)
      specialize (IH1 mc gl act Hequivcont). specialize_prove IH1 by admit. (* Group disjointness from sub-regexp *)
      specialize (IH2 mc gl act Hequivcont). specialize_prove IH2 by admit. (* Group disjointness from sub-regexp *)
      unfold equiv_cont in IH1, IH2.
      (* Eliminate failing cases *)
      destruct fuel as [|fuel]; simpl; try discriminate.
      destruct m1 as [res1|] eqn:Hres1; simpl; try discriminate.
      destruct compute_tree' as [t1|] eqn:Ht1; simpl; try discriminate.
      destruct (compute_tree' (Areg lr2 :: act)%list _ _ _ _) as [t2|] eqn:Ht2; simpl; try discriminate.
      specialize (IH1 gm ms inp res1 fuel t1 Hgmms Hgmgl Hmsinp Hres1 Ht1).
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
        eauto using IH2.

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
        unfold equiv_matcher. intros mc gl act Hequivcont Hgldisj.
        unfold equiv_cont. intros gm ms inp res [|fuel] t Hgmms Hgmgl Hmsinp; try discriminate; simpl.
        set (mc2 := fun s => _).
        assert (Hequivcont2: equiv_cont mc2 gl (Areg lr2 :: act)%list forward). {
          unfold equiv_cont. clear gm ms inp res fuel t Hgmms Hgmgl Hmsinp.
          intros gm ms inp res fuel t Hgmms Hgmgl Hmsinp. unfold mc2.
          intros Hres Ht. eapply IH2; eauto. admit. (* Group disjointness from sub-regexp *)
        }
        intros Hres Ht. eapply IH1; eauto. admit. (* Group disjointness from sub-regexp *)
      + (* Backward *)
        unfold equiv_matcher. intros mc gl act Hequivcont Hgldisj.
        unfold equiv_cont. intros gm ms inp res [|fuel] t Hgmms Hgmgl Hmsinp; try discriminate; simpl.
        set (mc1 := fun s => _).
        assert (Hequivcont1: equiv_cont mc1 gl (Areg lr1 :: act)%list backward). {
          unfold equiv_cont. clear gm ms inp res fuel t Hgmms Hgmgl Hmsinp.
          intros gm ms inp res fuel t Hgmms Hgmgl Hmsinp. unfold mc1.
          intros Hres Ht. eapply IH1; eauto. admit. (* Group disjointness from sub-regexp *)
        }
        intros Hres Ht. eapply IH2; eauto. admit. (* Group disjointness from sub-regexp *)

    - (* Quantified *)
      admit.

    - (* Group *)
      admit.

    - (* Lookaround *)
      admit.

    - (* Anchor *)
      admit.
  Admitted.
End Equiv.
