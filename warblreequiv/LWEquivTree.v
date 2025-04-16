From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List Program.Wf.
From Linden Require Import Tree LindenParameters CharsWarblre TMatching Chars Regex Semantics RegexpTranslation.
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

Inductive ms_matches_inp: MatchState -> input -> Prop :=
| Ms_matches_inp: forall (s: string) (end_ind: nat) cap (next pref: string),
    List.length pref = end_ind -> List.rev pref ++ next = s ->
    ms_matches_inp {| MatchState.input := s; MatchState.endIndex := Z.of_nat end_ind;
        MatchState.captures := cap |} (Input next pref).

Section Main.
  Context (s0: string) (rer: RegExpRecord) (root: regex) (wroot: Regex).
  Hypothesis Hcasesenst: RegExpRecord.ignoreCase rer = false.
  Hypothesis root_translates: to_warblre_regex root = Success wroot.
  Hypothesis Hwp_root: well_parenthesized root.

  Inductive input_compat: input -> Prop :=
  | Input_compat: forall next pref, List.rev pref ++ next = s0 -> input_compat (Input next pref).

  Definition tMC_is_tree (tmc: TMatcherContinuation) (reg: regex) (cont: continuation) (inp: input) :=
    forall s: MatchState, Valid (MatchState.input s) rer s -> ms_matches_inp s inp -> match tmc s with
    | Error _ => True (* finer modeling? *)
    | Success t => is_tree reg cont inp t
    end.
  
  Definition tMC_valid (tmc: TMatcherContinuation) (reg: regex) (cont: continuation) :=
    forall inp, input_compat inp -> tMC_is_tree tmc reg cont inp.

  Definition tm_valid (tm: TMatcher) (reg: regex) :=
    forall (tmc: TMatcherContinuation) (regc: regex) (cont: continuation),
    tMC_valid tmc regc cont ->
    tMC_valid (fun s => tm s tmc) reg (Areg regc::cont).

  Lemma tRepeatMatcher'_valid:
    forall greedy parenIndex parenCount,
    forall (tm: TMatcher) (reg: regex), tm_valid tm reg -> def_groups reg = List.seq (parenIndex + 1) parenCount ->
    forall fuel, tm_valid (fun s tmc => tRepeatMatcher' tm 0 +∞ greedy s tmc parenIndex parenCount fuel) (Regex.Star greedy reg).
  Proof.
    intros greedy parenIndex parenCount tm reg Htm_valid Hgroups_valid fuel.
    induction fuel as [|fuel IHfuel].
    - simpl. unfold tm_valid, tMC_valid, tMC_is_tree. split.
    - unfold tm_valid in *.
      intros tmc regc cont Htmc_valid.
      unfold tMC_valid.
      intros inp Hinp_compat.
      unfold tMC_is_tree.
      intros s Hvalids Hs_inp.
      simpl.
      destruct List.List.Update.Nat.Batch.update as [cap'|] eqn:Heqcap'; simpl. 2: exact I.
      destruct greedy.
      (* Greedy star *)
      + remember (fun y => if (_ =? _)%Z then _ else _) as tmc'.
        remember (match_state _ _ cap') as s'.
        assert (tMC_valid tmc' Epsilon (Acheck (ms_suffix s)::Areg (Regex.Star true reg)::Areg regc::cont)) as Htmc'_valid.
        {
          unfold tMC_valid.
          intros inp' Hinp'_compat.
          unfold tMC_is_tree.
          intros s1 Hs1valid Hs1_inp.
          rewrite Heqtmc'.
          destruct (_ =? _)%Z eqn:Heqcheck.
          - apply tree_pop_check_fail. admit.
          - destruct tRepeatMatcher' as [subtree|] eqn:Heqsubtree; simpl.
            2: exact I.
            apply tree_pop_check.
            + admit.
            + specialize (IHfuel tmc regc cont Htmc_valid).
              unfold tMC_valid in IHfuel.
              specialize (IHfuel inp' Hinp'_compat).
              unfold tMC_is_tree in IHfuel.
              specialize (IHfuel s1 Hs1valid Hs1_inp).
              rewrite Heqsubtree in IHfuel.
              apply tree_pop_reg.
              apply IHfuel.
        }
        specialize (Htm_valid tmc' Epsilon (Acheck (ms_suffix s)::Areg (Regex.Star true reg)::Areg regc::cont) Htmc'_valid).
        unfold tMC_valid in Htm_valid, Htmc_valid.
        specialize (Htm_valid inp Hinp_compat).
        specialize (Htmc_valid inp Hinp_compat).
        unfold tMC_is_tree in Htm_valid, Htmc_valid.
        assert (Valid (MatchState.input s') rer s') as Hvalids' by admit.
        assert (ms_matches_inp s' inp) as Hs'_inp.
        {
          rewrite Heqs'.
          inversion Hs_inp.
          simpl.
          now constructor.
        }
        specialize (Htm_valid s' Hvalids' Hs'_inp).
        specialize (Htmc_valid s Hvalids Hs_inp).
        destruct tm as [z|] eqn:Heqz; simpl. 2: exact I.
        destruct tmc as [z'|] eqn:Heqz'; simpl. 2: exact I.
        assert (is_tree reg (Acheck (ms_suffix s) :: Areg (Regex.Star true reg) :: Areg regc :: cont) inp z) as Htm_valid2.
        {
          apply is_tree_eps with (cont1 := nil). apply Htm_valid.
        }
        eapply tree_star.
        * symmetry. apply Hgroups_valid.
        * replace (current_str inp) with (ms_suffix s) by admit.
          apply Htm_valid2.
        * apply tree_pop_reg. apply Htmc_valid.
        * reflexivity.
      
      (* Lazy star *)
      + (* Likely similar; TODO do it! *)
        admit.
  Admitted.


  (* Theorem is not true for case-insensitive matching, which is not supported (yet) by the tree semantics *)
  (* Validity of the context and regexp? *)
  Theorem tmatcher_bt: forall reg ctx,
    let wreg' := to_warblre_regex reg in
    match wreg' with
    | Error _ => True
    | Success wreg =>
      Root wroot (wreg, ctx) ->
      match tCompileSubPattern wreg ctx rer forward with
      | Error _ => True
      | Success tm => tm_valid tm reg
        (*forall (tmc: TMatcherContinuation) (regc: regex) (cont: continuation),
        (forall inp, input_compat inp -> tMC_is_tree tmc regc cont inp) ->
        forall inp, input_compat inp -> tMC_is_tree (fun s => tm s tmc) reg (Areg regc::cont) inp*)
      end
    end.
  Proof.
    intro reg.
    induction reg as [
      |
      cd |
      r1 IHreg1 r2 IHreg2 |
      r1 IHreg1 r2 IHreg2 |
      greedy r1 IHreg1 |
      id r IHr
    ].


    - (* Empty *)
      simpl. intros _ _.
      intros tmc regc cont Htmc_tree inp Hinp_compat.
      unfold tMC_is_tree.
      intros s Hvalids Hs_inp.
      specialize (Htmc_tree inp Hinp_compat s Hvalids Hs_inp).
      destruct (tmc s) as [t|] eqn:Heqtmc; simpl; try exact I.
      apply tree_pop_reg. assumption.
    

    - (* Character descriptor *)
      simpl.
      intro ctx.
      destruct (char_descr_destruct cd) as [Hchar|[Hdot|[Hall|Herror]]].
      (* Character *)
      + destruct Hchar as [c Hchar].
        rewrite Hchar.
        rewrite single_Char.
        simpl.
        intros Hroot tmc regc cont Htmc_tree inp Hinp_compat.
        specialize (Htmc_tree inp Hinp_compat).
        unfold tMC_is_tree.
        intros s Hsvalid Hs_inp.
        destruct tCharacterSetMatcher as [t|e] eqn:Heqmatcher; simpl; try exact I.
        unfold tCharacterSetMatcher in Heqmatcher.
        simpl in Heqmatcher.
        remember ((_ <? 0)%Z || _) as next_outofbounds in Heqmatcher.
        destruct next_outofbounds eqn:Hoob; simpl.
        * inversion Heqmatcher.
          apply tree_char_fail.
          (* Reading out of bounds fails *)
          admit.
        * replace (Z.min _ _) with (@MatchState.endIndex Chars.Char char_marker s) in Heqmatcher by lia.
          destruct List.List.Indexing.Int.indexing as [chr|err] eqn:Hgetchr; simpl.
          -- simpl in Heqmatcher.
             destruct CharSet.exist_canonicalized eqn:Hcharmatch; simpl.
             ++ remember (match_state _ _ _) as s' in Heqmatcher.
                unfold tMC_is_tree in Htmc_tree.
                assert (Valid (MatchState.input s') rer s') as Hs'valid by admit.
                assert (ms_matches_inp s' inp) as Hs'_inp by admit.
                specialize (Htmc_tree s' Hs'valid Hs'_inp).
                destruct (tmc s') as [child|] eqn:Heqtmc; simpl; try discriminate.
                simpl in Heqmatcher.
                inversion Heqmatcher.
                admit.
             ++ admit.
          -- discriminate.
      (* Dot *)
      + rewrite Hdot.
        rewrite dot_Dot.
        simpl.
        admit.
      (* Character descriptor "all": untranslatable *)
      + rewrite Hall.
        rewrite all_error.
        split.
      (* Other unknown character descriptors *)
      + rewrite Herror. split.


    - (* Disjunction *)
      intro ctx.
      simpl.
      destruct (to_warblre_regex r1) as [wr1|] eqn:Hr1; simpl; try exact I.
      destruct (to_warblre_regex r2) as [wr2|] eqn:Hr2; simpl; try exact I.
      simpl in *.
      intro Hroot.
      remember (@Disjunction_left LindenParameters wr2 :: ctx) as ctx1.
      remember (@Disjunction_right LindenParameters wr1 :: ctx) as ctx2.
      specialize (IHreg1 ctx1).
      specialize (IHreg2 ctx2).
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
      specialize (IHreg1 Hroot1).
      specialize (IHreg2 Hroot2).
      destruct (tCompileSubPattern wr1 ctx1 rer forward) as [tm1|] eqn:Htm1; simpl; try exact I.
      destruct (tCompileSubPattern wr2 ctx2 rer forward) as [tm2|] eqn:Htm2; simpl; try exact I.
      intros tmc regc cont Htmc_tree inp Hinp_compat.
      unfold tMC_is_tree.
      intros s Hsvalid Hs_inp.
      specialize (IHreg1 tmc regc cont Htmc_tree inp Hinp_compat).
      specialize (IHreg2 tmc regc cont Htmc_tree inp Hinp_compat).
      unfold tMC_is_tree in IHreg1, IHreg2.
      specialize (IHreg1 s Hsvalid Hs_inp).
      specialize (IHreg2 s Hsvalid Hs_inp).
      destruct (tm1 s tmc) as [t1|] eqn:Heqt1; simpl; try exact I.
      destruct (tm2 s tmc) as [t2|] eqn:Heqt2; simpl; try exact I.
      now apply tree_disj.
      (* DONE! 🎉 *)


    - (* Sequence *)
      intro ctx.
      simpl.
      destruct (to_warblre_regex r1) as [wr1|] eqn:Hr1; simpl; try exact I.
      destruct (to_warblre_regex r2) as [wr2|] eqn:Hr2; simpl; try exact I.
      simpl in *.
      intro Hroot.
      remember (@Seq_left LindenParameters wr2 :: ctx) as ctx1.
      remember (@Seq_right LindenParameters wr1 :: ctx) as ctx2.
      specialize (IHreg1 ctx1).
      specialize (IHreg2 ctx2).
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
      specialize (IHreg1 Hroot1).
      specialize (IHreg2 Hroot2).
      destruct (tCompileSubPattern wr1 ctx1 rer forward) as [tm1|] eqn:Htm1; simpl; try exact I.
      destruct (tCompileSubPattern wr2 ctx2 rer forward) as [tm2|] eqn:Htm2; simpl; try exact I.
      intros tmc regc cont Htmc_tree inp Hinp_compat.
      unfold tMC_is_tree.
      intros s Hsvalid Hs_inp.
      remember (fun s1 => tm2 s1 tmc) as tmc2.
      assert (forall inp': input, input_compat inp' -> tMC_is_tree tmc2 r2 (Areg regc :: cont) inp') as Htmc2_tree.
      {
        intros inp' Hinp'_compat.
        rewrite Heqtmc2.
        now apply IHreg2.
      }
      specialize (IHreg1 tmc2 r2 (Areg regc :: cont) Htmc2_tree inp Hinp_compat).
      unfold tMC_is_tree in IHreg1.
      specialize (IHreg1 s Hsvalid Hs_inp).
      destruct (tm1 s tmc2) as [t|] eqn:Heqt; simpl; try exact I.
      now apply tree_sequence.
      (* DONE! 🎉 *)


    - (* Quantifier *)
      intro ctx.
      simpl.
      destruct (to_warblre_regex r1) as [wr1|] eqn:Heqwr1; simpl. 2: exact I.
      intro Hroot.
      destruct greedy eqn:Hgreedy; simpl in *.
      + destruct tCompileSubPattern as [m|] eqn:Heqm; simpl. 2: exact I.
        (*unfold tRepeatMatcher, tm_valid.*)
        intros tmc regc cont Htmc_valid.
        pose proof tRepeatMatcher'_valid true (StaticSemantics.countLeftCapturingParensBefore wr1 ctx)
        (StaticSemantics.countLeftCapturingParensWithin wr1 (Quantified_inner (Greedy Star) :: ctx)) m r1 as Hrepeat.
        specialize (IHreg1 (Quantified_inner (Greedy Star)::ctx)).
        assert (Root wroot (wr1, Quantified_inner (Greedy Star)::ctx)) as Hroot1 by
          eauto using same_root_down0, Down_Quantified_inner.
        specialize (IHreg1 Hroot1).
        rewrite Heqm in IHreg1.
        specialize (Hrepeat IHreg1).
        remember (StaticSemantics.countLeftCapturingParensBefore _ ctx) as parenIndex.
        remember (StaticSemantics.countLeftCapturingParensWithin _ _) as parenCount.
        assert (def_groups r1 = seq (parenIndex + 1) parenCount) as Hgroups_valid by admit.
        specialize (Hrepeat Hgroups_valid).
        unfold tMC_valid.
        intros inp Hinp_compat.
        unfold tMC_is_tree.
        intros s Hvalids Hs_inp.
        specialize (Hrepeat (Semantics.repeatMatcherFuel 0 s)).
        unfold tm_valid in Hrepeat.
        specialize (Hrepeat tmc regc cont Htmc_valid).
        now apply Hrepeat.
      
        (* Copy-pasting... *)
      + destruct tCompileSubPattern as [m|] eqn:Heqm; simpl. 2: exact I.
        unfold tRepeatMatcher.
        unfold tm_valid.
        intros tmc regc cont Htmc_valid.
        pose proof tRepeatMatcher'_valid false (StaticSemantics.countLeftCapturingParensBefore wr1 ctx)
        (StaticSemantics.countLeftCapturingParensWithin wr1 (Quantified_inner (Lazy Star) :: ctx)) m r1 as Hrepeat.
        specialize (IHreg1 (Quantified_inner (Lazy Star)::ctx)).
        assert (Root wroot (wr1, Quantified_inner (Lazy Star)::ctx)) as Hroot1.
        {
          eapply same_root_down0.
          - apply (@Down_Quantified_inner LindenParameters).
          - apply Hroot.
        }
        specialize (IHreg1 Hroot1).
        rewrite Heqm in IHreg1.
        specialize (Hrepeat IHreg1).
        remember (StaticSemantics.countLeftCapturingParensBefore _ ctx) as parenIndex.
        remember (StaticSemantics.countLeftCapturingParensWithin _ _) as parenCount.
        assert (def_groups r1 = seq (parenIndex + 1) parenCount) as Hgroups_valid by admit.
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
      intro ctx.
      simpl.
      destruct (to_warblre_regex r) as [wr|] eqn:Heqwr; simpl; try exact I.
      intro Hroot.
      remember (@Group_inner LindenParameters _ :: ctx) as rctx.
      simpl in IHr.
      specialize (IHr rctx).
      assert (Root wroot (wr, rctx)) as Hrootr.
      {
        eapply same_root_down0.
        - subst rctx. apply (@Down_Group_inner LindenParameters).
        - apply Hroot.
      }
      specialize (IHr Hrootr).
      destruct (tCompileSubPattern wr rctx rer forward) as [mr|] eqn:Heqmr; simpl; try exact I.
      intros tmc regc cont Htmc_tree inp Hinp_compat.
      unfold tMC_is_tree.
      intros s Hvalids Hs_inp.
      remember (fun y: MatchState => _) as tmc2.
      (* Let's try something *)
      specialize (IHr tmc2 Epsilon (Aclose id :: Areg regc :: cont)).
      assert (StaticSemantics.countLeftCapturingParensBefore (Group None wr) ctx + 1 = id) as Heqid by admit.
      assert (forall inp : input, input_compat inp -> tMC_is_tree tmc2 Epsilon (Aclose id :: Areg regc :: cont) inp) as Htmc2_tree.
      {
        intros inp' Hinp'_compat.
        rewrite Heqtmc2.
        unfold tMC_is_tree.
        intros s' Hs'valid Hs'_inp.
        destruct negb; simpl; try exact I.
        rewrite Heqid.
        replace (id =? 0) with false.
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
      specialize (IHr Htmc2_tree inp Hinp_compat).
      unfold tMC_is_tree in IHr.
      specialize (IHr s Hvalids Hs_inp).
      destruct (mr s tmc2) as [subtree|] eqn:Heqsubtree; simpl; try exact I.
      apply tree_group.
      apply is_tree_eps with (cont1 := nil). apply IHr.
  Admitted.

End Main.