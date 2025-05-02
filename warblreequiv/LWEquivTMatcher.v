From Coq Require Import Lia PeanoNat ZArith List.
Import ListNotations.
From Linden Require Import LWEquivTMatcherDef LWEquivTMatcherLemmas TMatching
  LindenParameters Tree Chars TreeMSInterp ListLemmas MSInput Tactics LKFactorization.
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
(* TODO Zero group *)

(* The identity continuations. *)
Definition id_mcont: MatcherContinuation := fun x => Success (Some x).
Definition id_tmcont: TMatcherContinuation := fun _ => Success Match.

(* These two continuations are easily equivalent (under all input strings
   and both directions and with no groups opened). *)
Lemma id_equiv: forall str0 dir, equiv_tree_mcont str0 id_mcont id_tmcont nil dir.
Proof.
  constructor. reflexivity.
Qed.


(* Lemma for repeated matching. *)
Lemma repeatMatcher'_tRepeatMatcher':
  (* For all pairs of a matcher m and a tree matcher tm *)
  forall (str0: string) (m: Matcher) (tm: TMatcher) (dir: Direction) (greedy: bool)
    (parenIndex parenCount: non_neg_integer),
    (* that are equivalent, *)
    equiv_tree_matcher str0 m tm dir ->
    (* for any fuel, min and max, *)
    forall fuel: nat,
    forall (min: non_neg_integer) (max: non_neg_integer_or_inf),
      (* the corresponding repeat matcher and tree matcher are equivalent with the same direction. *)
      equiv_tree_matcher str0
        (fun ms mc => Semantics.repeatMatcher' m min max greedy ms mc parenIndex parenCount fuel)
        (fun ms tmc => tRepeatMatcher' tm dir min max greedy ms tmc parenIndex parenCount fuel) dir.
Proof.
  intros str0 m tm dir greedy parenIndex parenCount Hm_tm_equiv fuel.
  induction fuel as [|fuel IHfuel].
  1: constructor.
  
  intros min max mc tmc gl Hequivcont ms Hms_str0. simpl.
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
    intros ms1 Hms1_str0.
    unfold mcnext, tmcnext.
    (* Case analysis on whether the progress check fails *)
    destruct ((min ==? 0)%wt && _)%bool eqn:Hprogress; simpl.
    - (* Fails *) constructor. reflexivity.
    - (* Succeeds *)
      set (if (min ==? 0)%wt then 0 else min - 1) as nextmin.
      set (if (max =? +∞)%NoI then +∞ else (max - 1)%NoI) as nextmax.
      specialize (IHfuel nextmin nextmax mc tmc gl Hequivcont ms1 Hms1_str0).
      destruct (min ==? 0)%wt; inversion IHfuel; simpl; constructor; auto.
  }
  (* Therefore, the results of matching the inner regexp, then looping, are *)
  (* equivalent. *)
  assert (equiv_results (tm ms_reset tmcnext) ms_reset gl dir
            (m ms_reset mcnext))
    as Hequiv_loop. {
    specialize (Hm_tm_equiv mcnext tmcnext gl Hequivnext ms_reset).
    specialize_prove Hm_tm_equiv by now simpl.
    inversion Hm_tm_equiv; now constructor.
  }

  assert ((reset_groups_ms (F := MatchError) (List.seq (parenIndex + 1) parenCount) ms) = ms_reset) as RESET_GROUPS by (eapply capture_reset_lw_same; eauto; reflexivity).
  (* By hypothesis, the results of exiting the loop are equivalent. *)
  pose proof Hequivcont ms Hms_str0 as Hequiv_exit.
  assert (equiv_results
            (let! z =<< tm ms_reset tmcnext in Success (GroupAction (Reset (List.seq (parenIndex + 1) parenCount)) z))
            ms gl dir (m ms_reset mcnext)) as Hequiv_loopreset. {
    inversion Hequiv_loop; simpl; constructor.
    simpl. rewrite RESET_GROUPS. assumption.
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
Qed.


(* Lemma for character set matchers. *)
Lemma charset_tcharset:
  forall rer m tm charset str0 dir
    (Heqm: Semantics.characterSetMatcher rer charset false dir = m)
    (Heqtm: tCharacterSetMatcher rer charset false dir = tm),
    equiv_tree_matcher str0 m tm dir.
Proof.
  intros. intros mc tmc gl Hequiv ms Hmsstr0.
  subst m tm.
  unfold tCharacterSetMatcher, Semantics.characterSetMatcher. simpl.
  set (nextend := if (dir ==? forward)%wt then _ else _).
  set ((_ <? 0)%Z || _)%bool as oob. destruct oob eqn:Hoob.
  1: { constructor. reflexivity. }
  
  set (Z.min _ _) as index.
  remember (List.List.Indexing.Int.indexing _ _) as readchr.
  destruct readchr as [readchr|]; simpl. 2: constructor.
  set (CharSet.exist_canonicalized _ _ _) as read_matches.
  destruct read_matches eqn:Hread_matches; simpl.
  2: constructor; reflexivity.
  remember (match_state _ _ _) as ms'.
  specialize (Hequiv ms').
  specialize_prove Hequiv. { rewrite Heqms'; auto. }
  destruct (tmc ms') as [child|]; simpl. 2: constructor.
  destruct (mc ms') as [res|]; simpl. 2: constructor.
  constructor.
  (*replace index with (MatchState.endIndex ms) in Heqreadchr by lia.*)
  inversion Hequiv as [child0 ms'0 gl0 dir0 res0 Hequiv' Heqchild0 Heqms'0 Heqgl0 Heqdir0 Heqres0 | |].
  unfold nextend in Heqms'.
  destruct dir; simpl in *; unfold advance_ms; rewrite <- Heqms'; rewrite <- Hequiv'; reflexivity.
Qed.


(** ** Lemma for lookarounds *)

(* A dummy match state to be able to discriminate; probably not strictly necessary. *)
Definition dummy_match_state: MatchState := match_state nil 0%Z nil.

(* The lemma; lkdir is the lookaround direction, pos is the lookaround positivity, lkreg is the lookaround regex. *)
Lemma compile_tcompile_lk:
  forall lkdir pos lkreg rer
    (IH:
      forall ctx m tm dir
        (Heqm: Semantics.compileSubPattern lkreg ctx rer dir = Success m)
        (Heqtm: tCompileSubPattern lkreg ctx rer dir = Success tm),
        forall str0, equiv_tree_matcher str0 m tm dir),
  forall ctx m tm dir
    (Heqm: Semantics.compileSubPattern ((to_warblre_lookaround lkdir pos) lkreg) ctx rer dir = Success m)
    (Heqtm: tLookaroundMatcher tCompileSubPattern lkdir pos lkreg ctx rer dir = Success tm),
  forall str0, equiv_tree_matcher str0 m tm dir.
Proof.
  intros. pose proof (lookaroundMatcher_fact lkdir pos lkreg ctx rer dir) as Hfact. rewrite Heqm in Hfact. clear Heqm.
  unfold tLookaroundMatcher in Heqtm. unfold lookaroundMatcher in Hfact.
  destruct Semantics.compileSubPattern as [mlk|] eqn:Heqmlk; simpl in *. 2: discriminate (Hfact id_mcont dummy_match_state).
  destruct tCompileSubPattern as [tmlk|] eqn:Heqtmlk; simpl in *. 2: discriminate.
  injection Heqtm as <-. unfold equiv_tree_matcher.
  intros mc tmc gl Hequivcont. unfold equiv_tree_mcont.
  intros ms Hmsstr0. specialize (Hfact mc ms). injection Hfact as ->.
  specialize (IH _ mlk tmlk lkdir Heqmlk Heqtmlk str0 id_mcont id_tmcont nil (id_equiv str0 lkdir) ms Hmsstr0). simpl in *.
  destruct tmlk as [tlk|] eqn:Htlk; try solve[constructor]. simpl.
  destruct mlk as [mslkopt|] eqn:Hmslkopt; try solve[constructor]. simpl.
  inversion IH as [tlk' ms' nil' lkdir' mslkopt' IH' | |]. subst tlk' ms' nil' lkdir' mslkopt'.
  rewrite <- IH'. unfold equiv_tree_mcont in Hequivcont.
  destruct pos; destruct mslkopt as [mslk|]; simpl; try solve[now constructor].
  - set (msafterlk := match_state _ _ _). specialize (Hequivcont msafterlk Hmsstr0).
    inversion Hequivcont as [t1 msafterlk' gl' r Hcontequiv' | |]. 2,3: constructor.
    constructor. simpl. replace (Regex.positivity _) with true by now destruct lkdir. replace (Regex.lk_dir _) with lkdir by now destruct lkdir. rewrite <- IH'. auto.
  - specialize (Hequivcont ms Hmsstr0). inversion Hequivcont as [t1 msafterlk' gl' r Hcontequiv' | |]. 2,3: constructor.
    simpl. constructor. simpl. replace (Regex.positivity _) with false by now destruct lkdir. replace (Regex.lk_dir _) with lkdir by now destruct lkdir. rewrite <- IH'. auto.
Qed.
  


(* Main theorem: *)
Theorem compile_tcompile:
  forall reg ctx rer m tm dir (* for all regexes, contexts, RegExpRecords and directions, *)
    (* if the compilations of the regexes into a matcher and a tree matcher succeed, *)
    (Heqm: Semantics.compileSubPattern reg ctx rer dir = Success m)
    (Heqtm: tCompileSubPattern reg ctx rer dir = Success tm),
    (* then the resulting matcher and tree matcher are equivalent. *)
  forall str0, equiv_tree_matcher str0 m tm dir.
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
    intros. injection Heqm as <-. injection Heqtm as <-.
    intros mc tmc gl Hequiv ms Hmsstr0.
    now apply Hequiv.

  - (* Character *)
    intros. injection Heqm as <-. injection Heqtm as <-. eapply charset_tcharset; reflexivity.
    
  - (* Dot; same as character *)
    intros. injection Heqm as <-. injection Heqtm as <-. eapply charset_tcharset; reflexivity.

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
    intros mc tmc gl Hequiv ms' Hms'str0.
    specialize (IH1 m1 tm1 dir Heqm1 Heqtm1 str0 mc tmc gl Hequiv ms' Hms'str0).
    specialize (IH2 m2 tm2 dir Heqm2 Heqtm2 str0 mc tmc gl Hequiv ms' Hms'str0).
    simpl in *.
    injection Heqtm as <-.
    destruct (tm1 ms' tmc) as [t1|] eqn:Heqt1; simpl. 2: constructor.
    destruct (tm2 ms' tmc) as [t2|] eqn:Heqt2; simpl. 2: constructor.
    injection Heqm as <-.
    destruct (m1 ms' mc) as [r|] eqn:Heqr; simpl. 2: constructor.
    destruct r eqn:?; simpl.
    + constructor. inversion IH1 as [t1' ms'' gl' dir' res IH1' Heqt1' Heqms'' Heqgl' Heqdir' Heqres | |].
      simpl. rewrite <- IH1'. reflexivity.
    + destruct (m2 ms' mc) as [r2|] eqn:Heqr2; simpl. 2: constructor.
      constructor.
      inversion IH1 as [t1' ms'' gl' dir' res IH1' Heqt1' Heqms'' Heqgl' Heqdir' Heqres | |].
      clear t1' ms'' gl' dir' res Heqt1' Heqms'' Heqgl' Heqdir' Heqres.
      simpl. rewrite <- IH1'. simpl.
      now inversion IH2.

  - (* Quantifier *)
    intros.
    remember (Quantified_inner q :: ctx)%list as ctx'.
    specialize (IH ctx').
    destruct Semantics.compileSubPattern as [msub|] eqn:Heqmsub; simpl. 2: discriminate.
    destruct tCompileSubPattern as [tmsub|] eqn:Heqtmsub; simpl. 2: discriminate.
    specialize (IH msub tmsub dir Heqmsub Heqtmsub).
    simpl in *.
    destruct negb; simpl. 1: discriminate.
    unfold equiv_tree_matcher. intros mc tmc gl Hequivcont.
    unfold equiv_tree_mcont. intro ms.
    unfold Semantics.repeatMatcher in Heqm. unfold tRepeatMatcher in Heqtm.
    injection Heqm as <-. injection Heqtm as <-.
    now apply repeatMatcher'_tRepeatMatcher'.

  - (* Sequence *)
    intros.
    remember (Seq_left wr2 :: ctx)%list as ctxleft.
    remember (Seq_right wr1 :: ctx)%list as ctxright.
    specialize (IH1 ctxleft). specialize (IH2 ctxright).
    destruct (Semantics.compileSubPattern wr1 _ _ _) as [m1|] eqn:Heqm1; simpl. 2: discriminate.
    destruct (Semantics.compileSubPattern wr2 _ _ _) as [m2|] eqn:Heqm2; simpl. 2: discriminate.
    destruct (tCompileSubPattern wr1 _ _ _) as [tm1|] eqn:Heqtm1; simpl. 2: discriminate.
    destruct (tCompileSubPattern wr2 _ _ _) as [tm2|] eqn:Heqtm2; simpl. 2: discriminate.
    simpl in *. destruct dir; injection Heqm as <-; injection Heqtm as <-; intros mc tmc gl Hequiv ms.
    + specialize (IH2 m2 tm2 forward Heqm2 Heqtm2 str0 mc tmc gl Hequiv).
      specialize (IH1 m1 tm1 forward Heqm1 Heqtm1 str0 (fun ms0 => m2 ms0 mc) (fun ms0 => tm2 ms0 tmc) gl IH2 ms). auto.
    + specialize (IH1 m1 tm1 backward Heqm1 Heqtm1 str0 mc tmc gl Hequiv).
      specialize (IH2 m2 tm2 backward Heqm2 Heqtm2 str0 (fun ms0 => m1 ms0 mc) (fun ms0 => tm1 ms0 tmc) gl IH1 ms). auto.

  - (* Group *)
    intros.
    remember (Group_inner name :: ctx)%list as ctx'. specialize (IH ctx').
    destruct (Semantics.compileSubPattern wr ctx' rer dir) as [msub|] eqn:Heqmsub; simpl. 2: discriminate.
    destruct (tCompileSubPattern wr ctx' rer dir) as [tmsub|] eqn:Heqtmsub; simpl. 2: discriminate.
    intros mc tmc gl Hequiv ms Hmsstr0.
    simpl in *.
    injection Heqm as <-. injection Heqtm as <-.
    remember (fun y : MatchState => _) as treecont.
    remember (fun y : MatchState => let! r =<< _ in let! cap =<< _ in mc _) as origcont.
    remember (StaticSemantics.countLeftCapturingParensBefore _ ctx + 1) as gid.
    set (gl' := ((gid, MatchState.endIndex ms, dir)::gl)%list).
    specialize (IH msub tmsub dir Heqmsub Heqtmsub str0 origcont treecont gl').
    specialize_prove IH. {
      intros y Hy_ms_sameinp.
      rewrite Heqtreecont, Heqorigcont.
      set (extr1 := MatchState.endIndex ms). set (extr2 := MatchState.endIndex y).
      remember (if (dir ==? forward)%wt then _ else _) as rangeresult. destruct rangeresult as [r|] eqn:Heqrange; simpl. 2: constructor.
      destruct (gid =? 0) eqn:Hgid_nonzero; simpl. 1: constructor.
      destruct List.List.Update.Nat.One.update as [cap'|] eqn:Hcapupd; simpl. 2: constructor.
      remember (match_state _ _ cap') as ms'.
      destruct (tmc ms') as [t|] eqn:Heqt; simpl. 2: constructor.
      destruct (mc ms') as [res|] eqn:Heqres; simpl. 2: constructor.
      constructor. simpl. rewrite EqDec.reflb. rewrite Hgid_nonzero.
      replace (Some (capture_range _ _)) with r.
      2: {
        destruct dir; simpl in *; destruct negb; try solve[discriminate]; inversion Heqrangeresult; auto.
      }
      unfold CaptureRange_or_undefined in Hcapupd. rewrite Hcapupd.
      specialize (Hequiv ms').
      specialize_prove Hequiv. { rewrite Heqms'; auto. }
      rewrite Heqt, Heqres in Hequiv.
      inversion Hequiv as [t' ms'' gl'' dir' res' Hequiv' Heqt' Heqms'' Heqgl'' Heqdir' Heqres' | |].
      clear t' ms'' gl'' res' Heqt' Heqms'' Heqgl'' Heqres'.
      rewrite Heqms' in Hequiv'. rewrite Hy_ms_sameinp. rewrite Hmsstr0 in Hequiv'.
      assumption.
    }
    specialize (IH ms Hmsstr0). simpl in *.
    destruct (tmsub ms treecont) as [t|] eqn:Heqt; simpl. 2: constructor.
    destruct (msub ms origcont) as [res|] eqn:Heqres; simpl. 2: constructor.
    constructor. inversion IH. auto.

    (* Positive lookahead *)
  - intros. apply compile_tcompile_lk with (lkdir := forward) (pos := true) (lkreg := wr) (rer := rer) (ctx := ctx); auto.

    (* Negative lookahead *)
  - intros. apply compile_tcompile_lk with (lkdir := forward) (pos := false) (lkreg := wr) (rer := rer) (ctx := ctx); auto.

    (* Positive lookbehind *)
  - intros. apply compile_tcompile_lk with (lkdir := backward) (pos := true) (lkreg := wr) (rer := rer) (ctx := ctx); auto.

    (* Negative lookbehind *)
  - intros. apply compile_tcompile_lk with (lkdir := backward) (pos := false) (lkreg := wr) (rer := rer) (ctx := ctx); auto.
Qed.
