From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List Program.Wf.
From Linden Require Import Tree LindenParameters CharsWarblre TMatching Chars ListLemmas.
From Warblre Require Import Patterns Result Notation Errors Node RegExpRecord Base Coercions Semantics Typeclasses.
Import Patterns.
Import Result.Result.
Import Result.Notations.
Import Result.Notations.Boolean.
Import Coercions.
Import Notation.

Local Open Scope result_flow.

(* Advance match state by one character *)
Definition advance_ms (s: MatchState): MatchState :=
  {|
    MatchState.input := MatchState.input s;
    MatchState.endIndex := (MatchState.endIndex s + 1)%Z;
    MatchState.captures := MatchState.captures s |}.

(* TODO Zero group *)

(* Reset the given groups (indexed from 1) in the given MatchState *)
Definition reset_groups_ms (gidl: list Groups.group_id) (s: MatchState): MatchState :=
  let '(match_state inp endInd cap) := s in
  let cap' := match List.List.Update.Nat.Batch.update None cap (List.map (fun x => x-1) gidl) with
    | Success cap' => cap'
    | Error _ => cap
  end in
  (match_state inp endInd cap').

(* A list of currently open groups, with for each of them their ID and the position at which they were opened.
   This is needed because we want to be able to express the result of the first branch of a sub-backtracking tree,
   which can close groups that are not opened within this tree and whose opening indices the Matchers and TMatchers
   do not record in the MatchStates passed to subsequent calls.
   An extended match state is a MatchState with a list of open groups with indices. It allows to model the capture
   of group opening indices in continuations. *)
Definition open_groups := list (Groups.group_id * integer).

Fixpoint has_group (id: Groups.group_id) (gl: open_groups): bool :=
  match gl with
  | nil => false
  | (id', _)::q => if id == id' then true else has_group id q
  end.

(* Close group id opened in gl at index end_index. If group id was indeed open, returns the new list of open groups
   (where the closed group has been removed) and the capture range of the closed group.
   Otherwise, return a dummy CaptureRange and the original list of open groups. *)
Fixpoint close_group (id: Groups.group_id) (gl: open_groups) end_index: CaptureRange * open_groups :=
  match gl with
  | nil => (capture_range (-1)%Z (-1)%Z, nil)
  | (id', start)::q =>
    if id == id' then
      (capture_range start end_index, q)
    else
      let (range, q') := close_group id q end_index in
      (range, (id', start)::q')
  end.

(* TODO Direction *)
(* Apply the given group action to the extended match state composed of a MatchState and a list of open groups with
   opening indices.
   If we try to close a nonexisting group or clear nonexisting capture ranges, do nothing. *)
Definition group_effect' (g: groupaction) (s: MatchState) (gl: open_groups): MatchState * open_groups :=
  match g with
  | Open gid =>
      (s, (gid, MatchState.endIndex s)::gl)
  | Close gid =>
      let cap := MatchState.captures s in
      let (range, gl') := close_group gid gl (MatchState.endIndex s) in
      let cap' := match Base.update cap gid range with
        | Success cap' => cap'
        | Error _ => cap
        end
      in
      (*set cap[gid] := range in*)
      (match_state (MatchState.input s) (MatchState.endIndex s) cap', gl')
  | Reset gidl =>
      let s' := reset_groups_ms gidl s in
      (s', gl)
  end.

(* We represent a call mc ms to some MatcherContinuation mc with match state ms as a sub-backtracking tree
   together with the match state ms and a list of groups that are open at that stage of matching. *)

(* TODO Direction *)
(* Given a sub-backtracking tree and an extended match state, retrieve the highest priority result represented
   by the subtree. *)
Fixpoint tree_res' (t:tree) (s: MatchState) (gl: open_groups): option MatchState :=
  match t with
  | Mismatch => None
  | Match => Some s
  | Choice t1 t2 =>
      let res1 := tree_res' t1 s gl in
      match res1 with
      | None => tree_res' t2 s gl
      | Some _ => res1
      end
  | Read c t1 =>
    tree_res' t1 (advance_ms s) gl
  | CheckFail _ => None
  | CheckPass _ t1 => tree_res' t1 s gl
  | GroupAction g t1 => 
    let (s', gl') := group_effect' g s gl in tree_res' t1 s' gl'
  end.


(* Expresses the equivalence between the first branch of a sub-backtracking tree with its corresponding
    extended match state on the one hand, with a MatchResult on the other hand.
    This simply unwraps the error monad; we currently do not say anything when either match result is an error
    (any error is equivalent to anything in both directions). *)
Inductive equiv_results: TMatchResult -> MatchState -> open_groups -> MatchResult -> Prop :=
| Equiv_results: forall (t: tree) (ms: MatchState) (open_gl: open_groups) (res: option MatchState),
    res = tree_res' t ms open_gl ->
    equiv_results (Success t) ms open_gl (Success res)
| Equiv_results_errl: forall errl ms open_gl res', equiv_results (Error errl) ms open_gl res'
| Equiv_results_errr: forall t' ms open_gl errr, equiv_results t' ms open_gl (Error errr).


(* A continuation is always called at a fixed position in the regexp, so with a fixed list of
   groups that are currently open.
   We say that a MatcherContinuation mc and a TMatcherContinuation tmc are equivalent under a given input string str0 and the list of
   open groups open_gl when given any MatchState ms compatible with the string str0 being matched,
   the sub-backtree (tmc s) with extended match state (s, open_gl) is equivalent to the MatchResult
   (mc s). *)
Definition equiv_tree_mcont (str0: string) (mc: MatcherContinuation) (tmc: TMatcherContinuation) (gl: open_groups) :=
  forall s: MatchState,
  MatchState.input s = str0 -> 
  equiv_results (tmc s) s gl (mc s).

(* A (T)Matcher matches a regexp, then calls a continuation after matching the said regexp.
   We say that a Matcher m and a TMatcher tm are equivalent under the input string str0 when given equivalent continuations,
   we obtain back equivalent continuations. *)
Definition equiv_tree_matcher (str0: string) (m: Matcher) (tm: TMatcher) :=
  forall mc tmc gl, equiv_tree_mcont str0 mc tmc gl -> equiv_tree_mcont str0 (fun s => m s mc) (fun s => tm s tmc) gl.


(* The identity continuations. *)
Definition id_mcont: MatcherContinuation := fun x => Success (Some x).
Definition id_tmcont: TMatcherContinuation := fun _ => Success Match.

(* These two continuations are easily equivalent (under all input strings and with no groups opened). *)
Lemma id_equiv: forall str0, equiv_tree_mcont str0 id_mcont id_tmcont nil.
Proof.
  constructor. reflexivity.
Qed.

Lemma repeatMatcher'_tRepeatMatcher': forall (str0: string) (m: Matcher) (tm: TMatcher),
  equiv_tree_matcher str0 m tm ->
  forall fuel: nat,
  forall (min: non_neg_integer) (max: non_neg_integer_or_inf) (greedy: bool)
  (parenIndex parenCount: non_neg_integer),
  equiv_tree_matcher str0
    (fun ms mc => Semantics.repeatMatcher' m min max greedy ms mc parenIndex parenCount fuel)
    (fun ms tmc => tRepeatMatcher' tm min max greedy ms tmc parenIndex parenCount fuel).
Proof.
  intros str0 m tm Hm_tm_equiv fuel.
  induction fuel as [|fuel IHfuel].
  - simpl. constructor.
  - intros min max greedy parenIndex parenCount mc tmc gl Hequivcont x Hxstr0.
    simpl.
    destruct (max =? 0)%NoI eqn:Hmax0; simpl.
    (* Case max = 0: use hypothesis on continuation *)
    + unfold equiv_tree_mcont in Hequivcont.
      now apply Hequivcont.
    (* Case max > 0 *)
    + (* Assume that the capture reset succeeds *)
      destruct List.List.Update.Nat.Batch.update as [cap'|] eqn:Heqcap'; simpl. 2: constructor.
      remember (match_state (MatchState.input x) (MatchState.endIndex x) cap') as s'.
      remember (fun y: MatchState => _) as tmc'.
      remember (fun (y: MatchState) => (_: MatchResult)) as mc'.
      assert (equiv_tree_mcont str0 mc' tmc' gl) as Hequiv'.
      {
        intros s Hsstr0.
        rewrite Heqmc', Heqtmc'.
        destruct ((min ==? 0)%wt && _) eqn:Hprogress; simpl.
        - constructor. reflexivity.
        - remember (if (min ==? 0)%wt then 0 else min - 1) as min'.
          remember (if (max =? +∞)%NoI then +∞ else (max - 1)%NoI) as max'.
          specialize (IHfuel min' max' greedy parenIndex parenCount mc tmc gl Hequivcont s Hsstr0).
          inversion IHfuel.
          + simpl. constructor. simpl. assumption.
          + constructor.
          + constructor.
      }
      assert (equiv_results (tm s' tmc') s' gl (m s' mc')) as Hequivres.
      {
        unfold equiv_tree_matcher in Hm_tm_equiv.
        specialize (Hm_tm_equiv mc' tmc' gl Hequiv' s').
        assert (Hs'str0: MatchState.input s' = str0).
        {
          rewrite Heqs'. simpl. assumption.
        }
        specialize (Hm_tm_equiv Hs'str0).
        inversion Hm_tm_equiv.
        2,3: constructor.
        now constructor.
      }
      assert ((reset_groups_ms (seq (parenIndex + 1) parenCount) x) = s') as RESET_GROUPS.
      {
        unfold reset_groups_ms.
        destruct x.
        rewrite <- List.List.Range.Nat.Length.range_seq.
        unfold List.List.Range.Nat.Bounds.range in Heqcap'.
        rewrite decr_range by lia.
        replace (parenIndex + parenCount + 1 - 1 - (parenIndex + 1 - 1)) with parenCount in Heqcap' by lia.
        simpl in Heqcap'.
        rewrite Heqcap'.
        simpl in *.
        congruence.
      }
      destruct (negb (min =? 0)) eqn:Hmin_nonzero; simpl.
      (* Case min > 0 *)
      * inversion Hequivres.
        2,3: constructor.
        constructor. simpl.
        rewrite RESET_GROUPS.
        simpl.
        assumption.
      (* Case min = 0 *)
      * specialize (Hequivcont x Hxstr0).
        inversion Hequivcont; inversion Hequivres; destruct greedy eqn:Hgreedy; simpl.
        all: try constructor.
        (* There must be a way to make this simpler *)
        -- subst ms open_gl ms0 open_gl0.
            rename t0 into z.
            rename t into z'.
            rename res0 into zm.
            unfold "!=?".
            destruct (zm ==? None)%wt eqn:Hzm_None; simpl.
            ++ constructor. simpl. rewrite RESET_GROUPS.
              (* rewrite H8. simpl. *)
              rewrite EqDec.inversion_true in Hzm_None.
              rewrite <- H8.
              rewrite Hzm_None.
              assumption.
            ++ constructor. simpl. rewrite RESET_GROUPS.
              rewrite <- H8. simpl.
              rewrite EqDec.inversion_false in Hzm_None.
              destruct zm; simpl.
              ** reflexivity.
              ** contradiction.
        -- subst ms open_gl ms0 open_gl0.
            rename t0 into z.
            rename t into z'.
            rename res0 into zm.
            rename res into zmc.
            unfold "!=?".
            destruct (zmc ==? None)%wt eqn:Hzmc_None; simpl.
            ++ constructor. simpl. rewrite <- H3. simpl.
              rewrite EqDec.inversion_true in Hzmc_None.
              rewrite Hzmc_None.
              rewrite RESET_GROUPS.
              simpl.
              assumption.
            ++ constructor. simpl. rewrite <- H3. simpl.
              rewrite EqDec.inversion_false in Hzmc_None.
              destruct zmc; simpl.
              ** reflexivity.
              ** contradiction.

        -- subst ms open_gl ms0 open_gl0.
            rewrite <- H4.
            destruct t'.
            ++ simpl.
              unfold "!=?".
              destruct (res ==? None)%wt eqn:Hres_None; simpl.
              ** constructor.
              ** constructor. simpl. rewrite <- H3.
                  simpl.
                  rewrite EqDec.inversion_false in Hres_None.
                  destruct res.
                  --- reflexivity.
                  --- contradiction.
            ++ simpl. constructor.

        -- subst ms open_gl ms0 open_gl0.
            rewrite <- H.
            destruct t'.
            ++ simpl.
              unfold "!=?".
              destruct (res ==? None)%wt eqn:Hres_None; simpl.
              ** constructor.
              ** constructor. simpl. rewrite RESET_GROUPS.
                  rewrite <- H7. simpl.
                  rewrite EqDec.inversion_false in Hres_None.
                  now destruct res.
            ++ simpl. constructor.
Qed.


Theorem compile_tcompile: forall reg ctx rer m tm
  (Heqm: Semantics.compileSubPattern reg ctx rer forward = Success m)
  (Heqtm: tCompileSubPattern reg ctx rer forward = Success tm),
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
  ]; simpl.

  - (* Empty *)
    intros. inversion Heqm as [Heqm']. inversion Heqtm as [Heqtm'].
    intros mc tmc gl Hequiv ms Hmsstr0.
    apply Hequiv. assumption.

  - (* Character *)
    intros. unfold equiv_tree_matcher. intros mc tmc gl Hequiv ms Hmsstr0.
    inversion Heqtm as [Heqtm']. clear Heqtm Heqtm'.
    inversion Heqm as [Heqm']. clear Heqm Heqm'.
    unfold tCharacterSetMatcher, Semantics.characterSetMatcher.
    simpl.
    remember ((_ <? 0)%Z || _) as oob.
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

  - (* Dot; same as character *)
    intros. unfold equiv_tree_matcher. intros mc tmc gl Hequiv ms Hmsstr0.
    inversion Heqtm as [Heqtm']. clear Heqtm Heqtm'.
    inversion Heqm as [Heqm']. clear Heqm Heqm'.
    unfold tCharacterSetMatcher, Semantics.characterSetMatcher.
    simpl.
    remember ((_ <? 0)%Z || _) as oob.
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

  - (* Atom escape: unsupported *)
    intros. destruct (match ae with | DecimalEsc de => _ | ACharacterClassEsc cce => _ | ACharacterEsc ce => _ | GroupEsc gn => _ end); discriminate.

  - (* Character class: unsupported *)
    intros. destruct (let! _ =<< _ in _); discriminate.

  - (* Disjunction *)
    intros.
    remember (Disjunction_left wr2 :: ctx) as ctxleft.
    remember (Disjunction_right wr1 :: ctx) as ctxright.
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
    remember (Quantified_inner q :: ctx) as ctx'.
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
    remember (Seq_left wr2 :: ctx) as ctxleft.
    remember (Seq_right wr1 :: ctx) as ctxright.
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
    remember (Group_inner name :: ctx) as ctx'.
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
    set (gl' := (gid, MatchState.endIndex ms)::gl).
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


  - (* Unsupported *)
    discriminate.
  - (* Unsupported *)
    discriminate.
  - (* Unsupported *)
    discriminate.
  - (* Unsupported *)
    discriminate.
  - (* Lookahead: unsupported *)
    discriminate.
  - (* Negative lookahead: unsupported *)
    discriminate.
  - (* Lookbehind: unsupported *)
    discriminate.
  - (* Negative lookbehind: unsupported *)
    discriminate.
Qed.
