From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List Program.Wf.
From Linden Require Import Tree LindenParameters CharsWarblre TMatching Chars Regex Semantics RegexpTranslation.
From Warblre Require Import Patterns Result Notation Errors Node RegExpRecord Base Coercions Semantics Typeclasses.
From Warblre.props Require Import Match.
Import Match.MatchState.
Import Patterns.
Import Result.Result.
Import Result.Notations.
Import Result.Notations.Boolean.
Import Coercions.
Import Notation.

Local Open Scope result_flow.

Inductive ms_matches_inp: MatchState -> input -> Prop :=
| Ms_matches_inp: forall (s: string) (end_ind: nat) cap (next pref: string),
    List.length pref = end_ind -> List.rev pref ++ next = s ->
    ms_matches_inp {| MatchState.input := s; MatchState.endIndex := Z.of_nat end_ind;
        MatchState.captures := cap |} (Input next pref).

Section Main.
  Context (s0: string) (rer: RegExpRecord).

  Definition tMC_is_tree (tmc: TMatcherContinuation) (reg: regex) (cont: continuation) (inp: input) :=
    forall s: MatchState, Valid (MatchState.input s) rer s -> ms_matches_inp s inp -> match tmc s with
    | Error _ => True (* finer modeling? *)
    | Success t => is_tree reg cont inp t
    end.

  Inductive input_compat: input -> Prop :=
  | Input_compat: forall next pref, List.rev pref ++ next = s0 -> input_compat (Input next pref).

  (* Theorem is not true for case-insensitive matching, which is not supported (yet) by the tree semantics *)
  (* Validity of the context and regexp? *)
  Theorem tmatcher_bt: forall reg ctx
    (Hcasesenst: RegExpRecord.ignoreCase rer = false),
    let wreg' := to_warblre_regex reg in
    match wreg' with
    | Error _ => True
    | Success wreg =>
      match tCompileSubPattern wreg ctx rer forward with
      | Error _ => True
      | Success tm => forall (tmc: TMatcherContinuation) (regc: regex) (cont: continuation),
        (forall inp, input_compat inp -> tMC_is_tree tmc regc cont inp) ->
        forall inp, input_compat inp -> tMC_is_tree (fun s => tm s tmc) reg (Areg regc::cont) inp
      end
    end.
  Proof.
    intros reg ctx Hcasesenst.
    revert ctx.
    induction reg as [
      |
      cd |
      r1 IHreg1 r2 IHreg2 |
      r1 IHreg1 r2 IHreg2 |
      greedy r1 IHreg1 |
      id r IHr
    ].
    - (* Empty *)
      simpl. intros _.
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
        intros tmc regc cont Htmc_tree inp Hinp_compat.
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
      remember (@Disjunction_left LindenParameters wr2 :: ctx) as ctx1.
      remember (@Disjunction_right LindenParameters wr1 :: ctx) as ctx2.
      specialize (IHreg1 ctx1).
      specialize (IHreg2 ctx2).
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
      remember (@Seq_left LindenParameters wr2 :: ctx) as ctx1.
      remember (@Seq_right LindenParameters wr1 :: ctx) as ctx2.
      specialize (IHreg1 ctx1).
      specialize (IHreg2 ctx2).
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
      admit.
      
    - (* Group *)
      intro ctx.
      simpl.
      
      admit.