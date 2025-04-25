From Coq Require Import Lia PeanoNat ZArith.
From Linden Require Import TMatcherEquivDef LWEquivTMatcherLemmas TMatching
  LindenParameters Tree Chars TreeMSInterp ListLemmas MSInput.
From Warblre Require Import Result Notation Base Semantics Coercions
  Errors Patterns Node.
Import Notation.
Import Coercions.
Import Result.Notations.
Import Patterns.

Local Open Scope result_flow.


(** * First part of equivalence proof: Warblre's matchers and the corresponding tree matchers yield equivalent results *)
(* This file contains the theorems stating the first part of the equivalence.
   The equivalence itself is defined in TMatcherEquivDef.v. *)
(* TODO Zero group *)

(* The identity continuations. *)
Definition id_mcont: MatcherContinuation := fun x => Success (Some x).
Definition id_tmcont: TMatcherContinuation := fun _ => Success Match.

(* These two continuations are easily equivalent (under all input strings
   and with no groups opened). *)
Lemma id_equiv: forall str0, equiv_tree_mcont str0 id_mcont id_tmcont nil.
Proof.
  constructor. reflexivity.
Qed.


(* Lemma for repeated matching. *)
Lemma repeatMatcher'_tRepeatMatcher':
  (* For all pairs of a matcher m and a tree matcher tm *)
  forall (str0: string) (m: Matcher) (tm: TMatcher) (greedy: bool)
    (parenIndex parenCount: non_neg_integer),
    (* that are equivalent, *)
    equiv_tree_matcher str0 m tm ->
    (* for any fuel, min and max, *)
    forall fuel: nat,
    forall (min: non_neg_integer) (max: non_neg_integer_or_inf),
      (* the corresponding repeat matcher and tree matcher are equivalent. *)
      equiv_tree_matcher str0
        (fun ms mc => Semantics.repeatMatcher' m min max greedy ms mc parenIndex parenCount fuel)
        (fun ms tmc => tRepeatMatcher' tm min max greedy ms tmc parenIndex parenCount fuel).
Proof.
  intros str0 m tm greedy parenIndex parenCount Hm_tm_equiv fuel.
  induction fuel as [|fuel IHfuel].
  - constructor.
  - intros min max.
    intros mc tmc gl Hequivcont ms Hms_str0.
    simpl.
    destruct (max =? 0)%NoI eqn:Hmax0; simpl.
    (* Case max = 0: use hypothesis on continuation *)
    + unfold equiv_tree_mcont in Hequivcont.
      now apply Hequivcont.
    (* Case max > 0 *)
    + (* Assume that the capture reset succeeds *)
      destruct List.List.Update.Nat.Batch.update as [cap'|] eqn:Heqcap'; simpl. 2: constructor.
      set (match_state (MatchState.input ms) (MatchState.endIndex ms) cap')
        as ms_reset.
      (* tmc' and mc' perform the progress check, then if this check succeeds, *)
      (* perform the recursive call with decreased min/max. *)
      set (fun y: MatchState => _) as tmcnext.
      set (fun (y: MatchState) => (_: MatchResult)) as mcnext.
      (* These two continuations are equivalent. *)
      assert (equiv_tree_mcont str0 mcnext tmcnext gl) as Hequivnext.
      {
        intros ms1 Hms1_str0.
        unfold mcnext, tmcnext.
        (* Case analysis on whether the progress check fails *)
        destruct ((min ==? 0)%wt && _)%bool eqn:Hprogress; simpl.
        - (* Fails *) constructor. reflexivity.
        - (* Succeeds *)
          set (if (min ==? 0)%wt then 0 else min - 1) as nextmin.
          set (if (max =? +∞)%NoI then +∞ else (max - 1)%NoI) as nextmax.
          specialize (IHfuel nextmin nextmax mc tmc gl Hequivcont ms1 Hms1_str0).
          inversion IHfuel.
          + simpl. constructor. simpl. assumption.
          + constructor.
          + constructor.
      }
      (* Therefore, the results of matching the inner regexp, then looping, are *)
      (* equivalent. *)
      assert (equiv_results (tm ms_reset tmcnext) ms_reset gl
                (m ms_reset mcnext))
        as Hequiv_loop.
      {
        unfold equiv_tree_matcher in Hm_tm_equiv.
        specialize (Hm_tm_equiv mcnext tmcnext gl Hequivnext ms_reset).
        assert (Hms_reset_str0: MatchState.input ms_reset = str0) by now simpl.
        specialize (Hm_tm_equiv Hms_reset_str0).
        inversion Hm_tm_equiv; now constructor.
      }
      (* A technical lemma *)
      assert ((reset_groups_ms (F := MatchError) (List.seq (parenIndex + 1) parenCount) ms) = ms_reset) as RESET_GROUPS.
      {
        unfold reset_groups_ms.
        destruct ms.
        rewrite <- List.List.Range.Nat.Length.range_seq.
        unfold List.List.Range.Nat.Bounds.range in Heqcap'.
        rewrite decr_range by lia.
        replace (parenIndex + parenCount + 1 - 1 - (parenIndex + 1 - 1)) with parenCount in Heqcap' by lia.
        simpl in Heqcap'.
        rewrite Heqcap'.
        simpl in *.
        reflexivity.
      }
      (* By hypothesis, the results of exiting the loop are equivalent. *)
      pose proof Hequivcont ms Hms_str0 as Hequiv_exit.
      assert (equiv_results (let! z =<< tm ms_reset tmcnext
                             in Success (GroupAction (Reset (List.seq (parenIndex + 1
                                                               ) parenCount)) z)
                ) ms gl (m ms_reset mcnext)) as Hequiv_loopreset. {
        inversion Hequiv_loop.
        - simpl. constructor. simpl. rewrite RESET_GROUPS. assumption.
        - constructor.
        - constructor.
      }
      destruct (negb (min =? 0)) eqn:Hmin_nonzero; simpl.
      * (* Case min > 0: results from equivalence in loop case *)
        apply Hequiv_loopreset.
      * (* Case min = 0 *)
        destruct greedy.
        -- rewrite func_monad_swap
             with (f1 := fun z => GroupAction (Reset (List.seq (parenIndex + 1)
                                                             parenCount)) z)
                  (f2 := id).
           apply equiv_choice.
           ++ assumption.
           ++ rewrite monad_id. assumption.
       -- rewrite func_monad_swap
             with (f2 := fun z => GroupAction (Reset (List.seq (parenIndex + 1)
                                                             parenCount)) z)
                  (f1 := id).
          apply equiv_choice.
          ++ rewrite monad_id. assumption.
          ++ assumption.
Qed.


(* Lemma for character set matchers. *)
Lemma charset_tcharset:
  forall rer m tm charset str0
    (Heqm: Semantics.characterSetMatcher rer charset false forward = m)
    (Heqtm: tCharacterSetMatcher rer charset false forward = tm),
    equiv_tree_matcher str0 m tm.
Proof.
  intros. unfold equiv_tree_matcher. intros mc tmc gl Hequiv ms Hmsstr0.
  inversion Heqtm as [Heqtm']. clear Heqtm Heqtm'.
  inversion Heqm as [Heqm']. clear Heqm Heqm'.
  unfold tCharacterSetMatcher, Semantics.characterSetMatcher.
  simpl.
  remember ((_ <? 0)%Z || _)%bool as oob.
  destruct oob eqn:Hoob.
  + constructor. reflexivity.
  + remember (Z.min _ _) as index.
    remember (List.List.Indexing.Int.indexing _ _) as readchr.
    destruct readchr as [readchr|]; simpl. 2: constructor.
    remember (CharSet.exist_canonicalized _ _ _) as read_matches.
    destruct read_matches eqn:Hread_matches; simpl.
    2: constructor; reflexivity.
    remember (match_state _ _ _) as ms'.
    specialize (Hequiv ms').
    assert (MatchState.input ms' = str0) as Hms'str0.
    {
      rewrite Heqms'. simpl. apply Hmsstr0.
    }
    specialize (Hequiv Hms'str0).
    destruct (tmc ms') as [child|]; simpl. 2: constructor.
    destruct (mc ms') as [res|]; simpl. 2: constructor.
    constructor.
    replace (Z.min (MatchState.endIndex ms) (MatchState.endIndex ms + 1)) with (MatchState.endIndex ms) in Heqindex by lia.
    rewrite Heqindex in Heqreadchr.
    simpl.
    inversion Hequiv as [child0 ms'0 gl0 res0 Hequiv' Heqchild0 Heqms'0 Heqgl0 Heqres0 | |].
    unfold advance_ms.
    rewrite <- Heqms'.
    rewrite <- Hequiv'.
    reflexivity.
Qed.


(* Main theorem: *)
Theorem compile_tcompile:
  forall reg ctx rer m tm (* for all regexes, contexts and RegExoRecords, *)
    (* if the compilations of the regexes into a matcher and a tree matcher succeed, *)
    (Heqm: Semantics.compileSubPattern reg ctx rer forward = Success m)
    (Heqtm: tCompileSubPattern reg ctx rer forward = Success tm),
    (* then the resulting matcher and tree matcher are equivalent. *)
  forall str0, equiv_tree_matcher str0 m tm.
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
  ]; simpl; try discriminate.

  - (* Empty *)
    intros. inversion Heqm as [Heqm']. inversion Heqtm as [Heqtm'].
    intros mc tmc gl Hequiv ms Hmsstr0.
    apply Hequiv. assumption.

  - (* Character *)
    intros. inversion Heqm as [Heqm']. inversion Heqtm as [Heqtm']. eapply charset_tcharset; reflexivity.
    
  - (* Dot; same as character *)
    intros. inversion Heqm as [Heqm']. inversion Heqtm as [Heqtm']. eapply charset_tcharset; reflexivity.

  - (* Disjunction *)
    intros.
    remember (Disjunction_left wr2 :: ctx)%list as ctxleft.
    remember (Disjunction_right wr1 :: ctx)%list as ctxright.
    specialize (IH1 ctxleft).
    specialize (IH2 ctxright).
    destruct (Semantics.compileSubPattern wr1 _ _ _) as [m1|] eqn:Heqm1; simpl. 2: discriminate.
    destruct (Semantics.compileSubPattern wr2 _ _ _) as [m2|] eqn:Heqm2; simpl. 2: discriminate.
    destruct (tCompileSubPattern wr1 _ _ _) as [tm1|] eqn:Heqtm1; simpl. 2: discriminate.
    destruct (tCompileSubPattern wr2 _ _ _) as [tm2|] eqn:Heqtm2; simpl. 2: discriminate.
    simpl in *.
    unfold equiv_tree_matcher.
    intros mc tmc gl Hequiv ms' Hms'str0.
    specialize (IH1 m1 tm1 eq_refl eq_refl str0 mc tmc gl Hequiv ms' Hms'str0).
    specialize (IH2 m2 tm2 eq_refl eq_refl str0 mc tmc gl Hequiv ms' Hms'str0).
    simpl in *.
    inversion Heqtm as [Heqtm'].
    destruct (tm1 ms' tmc) as [t1|] eqn:Heqt1; simpl. 2: constructor.
    destruct (tm2 ms' tmc) as [t2|] eqn:Heqt2; simpl. 2: constructor.
    inversion Heqm as [Heqm'].
    destruct (m1 ms' mc) as [r|] eqn:Heqr; simpl. 2: constructor.
    destruct r eqn:?; simpl.
    + constructor. inversion IH1 as [t1' ms'' gl' res IH1' Heqt1' Heqms'' Heqgl' Heqres | |].
      simpl. rewrite <- IH1'. reflexivity.
    + destruct (m2 ms' mc) as [r2|] eqn:Heqr2; simpl. 2: constructor.
      constructor.
      inversion IH1 as [t1' ms'' gl' res IH1' Heqt1' Heqms'' Heqgl' Heqres | |].
      clear t1' ms'' gl' res Heqt1' Heqms'' Heqgl' Heqres.
      simpl. rewrite <- IH1'. simpl.
      inversion IH2 as [t2' ms''' gl'' res' IH2' Heqt2' Heqms''' Heqgl'' Heqres' | |].
      clear t2' ms''' gl'' res' Heqt2' Heqms''' Heqgl'' Heqres'. assumption.

  - (* Quantifier *)
    intros.
    remember (Quantified_inner q :: ctx)%list as ctx'.
    specialize (IH ctx').
    destruct Semantics.compileSubPattern as [msub|] eqn:Heqmsub; simpl. 2: discriminate.
    destruct tCompileSubPattern as [tmsub|] eqn:Heqtmsub; simpl. 2: discriminate.
    specialize (IH msub tmsub eq_refl eq_refl).
    simpl in *.
    destruct negb; simpl. 1: discriminate.
    unfold equiv_tree_matcher.
    intros mc tmc gl Hequivcont. unfold equiv_tree_mcont.
    intro ms.
    unfold Semantics.repeatMatcher in Heqm.
    unfold tRepeatMatcher in Heqtm.
    inversion Heqm as [Heqm'].
    inversion Heqtm as [Heqtm'].
    now apply repeatMatcher'_tRepeatMatcher'.

  - (* Sequence *)
    intros.
    remember (Seq_left wr2 :: ctx)%list as ctxleft.
    remember (Seq_right wr1 :: ctx)%list as ctxright.
    specialize (IH1 ctxleft).
    specialize (IH2 ctxright).
    destruct (Semantics.compileSubPattern wr1 _ _ _) as [m1|] eqn:Heqm1; simpl. 2: discriminate.
    destruct (Semantics.compileSubPattern wr2 _ _ _) as [m2|] eqn:Heqm2; simpl. 2: discriminate.
    destruct (tCompileSubPattern wr1 _ _ _) as [tm1|] eqn:Heqtm1; simpl. 2: discriminate.
    destruct (tCompileSubPattern wr2 _ _ _) as [tm2|] eqn:Heqtm2; simpl. 2: discriminate.
    simpl in *.
    inversion Heqm as [Heqm'].
    inversion Heqtm as [Heqtm'].
    intros mc tmc gl Hequiv ms.
    specialize (IH2 m2 tm2 eq_refl eq_refl str0 mc tmc gl Hequiv).
    specialize (IH1 m1 tm1 eq_refl eq_refl str0 (fun ms0 => m2 ms0 mc) (fun ms0 => tm2 ms0 tmc) gl IH2 ms).
    simpl in *.
    assumption.

  - (* Group *)
    intros.
    remember (Group_inner name :: ctx)%list as ctx'.
    specialize (IH ctx').
    destruct (Semantics.compileSubPattern wr ctx' rer forward) as [msub|] eqn:Heqmsub; simpl. 2: discriminate.
    destruct (tCompileSubPattern wr ctx' rer forward) as [tmsub|] eqn:Heqtmsub; simpl. 2: discriminate.
    intros mc tmc gl Hequiv ms Hmsstr0.
    simpl in *.
    inversion Heqm as [Heqm']. clear Heqm Heqm'.
    inversion Heqtm as [Heqtm']. clear Heqtm Heqtm'.
    remember (fun y : MatchState => _) as treecont.
    remember (fun y : MatchState => let! r =<< _ in let! cap =<< _ in mc _) as origcont.
    remember (StaticSemantics.countLeftCapturingParensBefore _ ctx + 1) as gid.
    set (gl' := ((gid, MatchState.endIndex ms)::gl)%list).
    specialize (IH msub tmsub eq_refl eq_refl str0 origcont treecont gl').
    assert (equiv_tree_mcont str0 origcont treecont gl') as Hequivcont.
    {
      intros y Hy_ms_sameinp.
      rewrite Heqtreecont, Heqorigcont.
      remember (MatchState.endIndex ms) as i.
      destruct negb eqn:Hi_le_y; simpl. 1: constructor.
      destruct (gid =? 0) eqn:Hgid_nonzero; simpl. 1: constructor.
      destruct List.List.Update.Nat.One.update as [cap'|] eqn:Hcapupd; simpl. 2: constructor.
      remember (match_state _ _ cap') as ms'.
      destruct (tmc ms') as [t|] eqn:Heqt; simpl. 2: constructor.
      destruct (mc ms') as [res|] eqn:Heqres; simpl. 2: constructor.
      constructor. simpl.
      rewrite EqDec.reflb. simpl.
      rewrite Hgid_nonzero.
      unfold CaptureRange_or_undefined in Hcapupd.
      rewrite Hcapupd.
      specialize (Hequiv ms').
      assert (MatchState.input ms' = str0) as Hms'str0.
      {
        rewrite Heqms'. simpl. apply Hmsstr0.
      }
      specialize (Hequiv Hms'str0).
      rewrite Heqt, Heqres in Hequiv.
      inversion Hequiv as [t' ms'' gl'' res' Hequiv' Heqt' Heqms'' Heqgl'' Heqres' | |].
      clear t' ms'' gl'' res' Heqt' Heqms'' Heqgl'' Heqres'.
      rewrite Heqms' in Hequiv'.
      rewrite Hy_ms_sameinp.
      rewrite Hmsstr0 in Hequiv'.
      assumption.
    }
    specialize (IH Hequivcont ms Hmsstr0).
    simpl in *.
    destruct (tmsub ms treecont) as [t|] eqn:Heqt; simpl. 2: constructor.
    destruct (msub ms origcont) as [res|] eqn:Heqres; simpl. 2: constructor.
    constructor. inversion IH.
    simpl.
    assumption.

Qed.
