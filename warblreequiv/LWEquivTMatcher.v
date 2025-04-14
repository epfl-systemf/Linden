From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List Program.Wf.
From Linden Require Import Tree LindenParameters CharsWarblre TMatching Chars.
From Warblre Require Import Patterns Result Notation Errors Node RegExpRecord Base Coercions Semantics Typeclasses.
Import Patterns.
Import Result.Result.
Import Result.Notations.
Import Result.Notations.Boolean.
Import Coercions.
Import Notation.

Local Open Scope result_flow.

Inductive tree_res'_error :=
  | MismatchingTree.

Instance tree_res'_error_assert: AssertionError tree_res'_error := {| Result.f := MismatchingTree |}.

Definition advance_ms (s: MatchState): MatchState :=
  {|
    MatchState.input := MatchState.input s;
    MatchState.endIndex := (MatchState.endIndex s + 1)%Z;
    MatchState.captures := MatchState.captures s |}.

Fixpoint reset_groups_ms (gidl: list Groups.group_id) (s: MatchState): Result MatchState tree_res'_error :=
  let '(match_state inp endInd cap) := s in
  match gidl with
  | nil => Success s
  | x::q =>
    set cap[x] := None in
    reset_groups_ms q (match_state inp endInd cap)
  end.

(* A list of currently open groups *)
Definition open_groups := list (Groups.group_id * integer).

Fixpoint has_group (id: Groups.group_id) (gl: open_groups): bool :=
  match gl with
  | nil => false
  | (id', _)::q => if id == id' then true else has_group id q
  end.

Fixpoint close_group (id: Groups.group_id) (gl: open_groups) end_index: Result (CaptureRange * open_groups) tree_res'_error :=
  match gl with
  | nil => Error MismatchingTree
  | (id', start)::q =>
    if id == id' then
      Success (capture_range start end_index, q)
    else
      let! (range, q') =<< close_group id q end_index in
      Success (range, (id', start)::q')
  end.

(* TODO Direction *)
Definition group_effect' (g: groupaction) (s: MatchState) (gl: open_groups): Result (MatchState * open_groups) tree_res'_error :=
  match g with
  | Open gid =>
      Success (s, (gid, MatchState.endIndex s)::gl)
  | Close gid =>
      let cap := MatchState.captures s in
      let! (range, gl') =<< close_group gid gl (MatchState.endIndex s) in
      set cap[gid] := range in
      Success (match_state (MatchState.input s) (MatchState.endIndex s) cap, gl')
  | Reset gidl =>
      let! s' =<< reset_groups_ms gidl s in
      Success (s', gl)
  end.

(* returning the highest-priority result *)
(* we also return the corresponding state *)
(* TODO Direction *)
Fixpoint tree_res' (t:tree) (s: MatchState) (gl: open_groups): Result (option MatchState) tree_res'_error :=
  match t with
  | Mismatch => Success None
  | Match => Success (Some s)
  | Choice t1 t2 =>
      let! res1 =<< tree_res' t1 s gl in
      match res1 with
      | None => tree_res' t2 s gl
      | Some _ => Success res1
      end
  | Read c t1 => 
    if List.nth (Z.to_nat (MatchState.endIndex s)) (MatchState.input s) c == c then
      tree_res' t1 (advance_ms s) gl
    else
      Error MismatchingTree
  | CheckFail _ => Success None
  | CheckPass _ t1 => tree_res' t1 s gl
  | GroupAction g t1 => 
    let! (s', gl') =<< group_effect' g s gl in tree_res' t1 s' gl'
  end.


Section Main.
  Context (s0: string).

  Definition equiv_results (s: MatchState) (gl: open_groups) (res': MatchResult) (t': TMatchResult) :=
    match t', res' with
    | Error _, _ | _, Error _ => True (* finer modeling? *)
    | Success t, Success res => tree_res' t s gl = Success res
    end.

  Definition equiv_tree_mcont (mc: MatcherContinuation) (tmc: TMatcherContinuation) (gl: open_groups) :=
    forall s: MatchState,
    MatchState.input s = s0 -> 
    equiv_results s gl (mc s) (tmc s).

  Definition equiv_tree_matcher (m: Matcher) (tm: TMatcher) :=
    forall mc tmc gl, equiv_tree_mcont mc tmc gl -> equiv_tree_mcont (fun s => m s mc) (fun s => tm s tmc) gl.

  Definition id_mcont: MatcherContinuation := fun x => Success (Some x).
  Definition id_tmcont: TMatcherContinuation := fun _ => Success Match.

  Lemma id_equiv: equiv_tree_mcont id_mcont id_tmcont nil.
  Proof.
    intros s Hss0. simpl. reflexivity.
  Qed.

  Lemma repeatMatcher'_tRepeatMatcher': forall (m: Matcher) (tm: TMatcher),
    equiv_tree_matcher m tm ->
    forall fuel: nat,
    forall (mc: MatcherContinuation) (tmc: TMatcherContinuation) (gl: open_groups),
    equiv_tree_mcont mc tmc gl ->
    forall (min: non_neg_integer) (max: non_neg_integer_or_inf) (greedy: bool)
    (x: MatchState) (parenIndex parenCount: non_neg_integer),
    MatchState.input x = s0 ->
    equiv_results x gl
      (Semantics.repeatMatcher' m min max greedy x mc parenIndex parenCount fuel)
      (tRepeatMatcher' tm min max greedy x tmc parenIndex parenCount fuel).
  Proof.
    intros m tm Hm_tm_equiv fuel.
    induction fuel as [|fuel IHfuel].
    - simpl. split.
    - intros mc tmc gl Hequivcont min max greedy x parenIndex parenCount Hxs0.
      unfold equiv_results.
      simpl.
      destruct (max =? 0)%NoI eqn:Hmax0; simpl.
      (* Case max = 0: use hypothesis on continuation *)
      + unfold equiv_tree_mcont in Hequivcont.
        apply Hequivcont. assumption.
      (* Case max > 0 *)
      + (* Assume that the capture reset succeeds *)
        destruct List.List.Update.Nat.Batch.update as [cap'|] eqn:Heqcap'; simpl. 2: exact I.
        rewrite Hxs0.
        remember (match_state s0 (MatchState.endIndex x) cap') as s'.
        remember (fun y: MatchState => _) as tmc'.
        remember (fun (y: MatchState) => (_: MatchResult)) as mc'.
        assert (equiv_tree_mcont mc' tmc' gl) as Hequiv'.
        {
          intros s Hss0.
          rewrite Heqmc', Heqtmc'.
          unfold equiv_results.
          destruct ((min ==? 0)%wt && _) eqn:Hprogress; simpl.
          - reflexivity.
          - remember (if (min ==? 0)%wt then 0 else min - 1) as min'.
            remember (if (max =? +∞)%NoI then +∞ else (max - 1)%NoI) as max'.
            specialize (IHfuel mc tmc gl Hequivcont min' max' greedy s parenIndex parenCount Hss0).
            unfold equiv_results in IHfuel.
            destruct tRepeatMatcher' as [subtree|] eqn:Heqsubtree; simpl. 2: exact I.
            destruct Semantics.repeatMatcher' as [res|] eqn:Heqres; simpl. 2: exact I.
            apply IHfuel.
        }
        assert (equiv_results s' gl (m s' mc') (tm s' tmc')) as Hequivres.
        {
          unfold equiv_tree_matcher in Hm_tm_equiv.
          specialize (Hm_tm_equiv mc' tmc' gl Hequiv' s').
          assert (Hs's0: MatchState.input s' = s0).
          {
            rewrite Heqs'. reflexivity.
          }
          specialize (Hm_tm_equiv Hs's0).
          unfold equiv_results in Hm_tm_equiv.
          unfold equiv_results.
          destruct tm as [subtree|] eqn:Heqsubtree; simpl. 2: exact I.
          destruct m as [res|] eqn:Heqres; simpl. 2: exact I.
          apply Hm_tm_equiv.
        }
        assert ((reset_groups_ms (seq (parenIndex + 1) parenCount) x) = (@Success MatchState tree_res'_error s')) as RESET_GROUPS by admit.
        destruct (negb (min =? 0)) eqn:Hmin_nonzero; simpl.
        (* Case min > 0 *)
        * unfold equiv_results in Hequivres.
          destruct tm as [subtree|] eqn:Heqsubtree; simpl. 2: exact I.
          destruct m as [res|] eqn:Heqres; simpl. 2: exact I.
          (* Resetting the groups from parenIndex + 1 to parenIndex + parenCount in x yields exactly state s',
            see Heqs' and Heqcap'. Let's admit that for now *)
          rewrite RESET_GROUPS.
          simpl.
          apply Hequivres.
        (* Case min = 0 *)
        * specialize (Hequivcont x Hxs0).
          unfold equiv_results in Hequivcont, Hequivres.
          destruct greedy eqn:Hgreedy; simpl.
          -- destruct tm as [z|] eqn:Heqz; simpl. 2: exact I.
             destruct tmc as [z'|] eqn:Heqz'; simpl. 2: exact I.
             rewrite RESET_GROUPS.
             destruct m as [zm|] eqn:Heqzm; simpl. 2: exact I.
             unfold "!=?".
             destruct (zm ==? None)%wt eqn:Hzm_None; simpl.
             ++ rewrite Hequivres. simpl.
                rewrite EqDec.inversion_true in Hzm_None.
                rewrite Hzm_None.
                destruct mc.
                2: exact I.
                assumption.
             ++ rewrite Hequivres. simpl.
                rewrite EqDec.inversion_false in Hzm_None.
                destruct zm; simpl.
                ** reflexivity.
                ** contradiction.
          -- destruct tmc as [z'|] eqn:Heqz'; simpl. 2: exact I.
             destruct tm as [z|] eqn:Heqz; simpl. 2: exact I.
             rewrite RESET_GROUPS.
             destruct mc as [zmc|] eqn:Heqzmc; simpl. 2: exact I.
             unfold "!=?".
             destruct (zmc ==? None)%wt eqn:Hzmc_None; simpl.
             ++ destruct m; simpl. 2: exact I.
                rewrite Hequivcont. simpl.
                rewrite EqDec.inversion_true in Hzmc_None.
                rewrite Hzmc_None.
                assumption.
             ++ rewrite Hequivcont. simpl.
                rewrite EqDec.inversion_false in Hzmc_None.
                destruct zmc; simpl.
                ** reflexivity.
                ** contradiction.
  Admitted.


  Theorem compile_tcompile: forall reg ctx rer,
    let m' := Semantics.compileSubPattern reg ctx rer forward in
    let tm' := tCompileSubPattern reg ctx rer forward in
    match m', tm' with
    | Error _, _ | _, Error _ => True
    | Success m, Success tm => equiv_tree_matcher m tm
    end.
  Proof.
    intros reg ctx rer.
    revert ctx.
    induction reg; simpl.

    - (* Empty *)
      unfold equiv_tree_matcher. intros. unfold equiv_tree_mcont in *. assumption.
    
    - (* Character *)
      intros _ mc tmc gl Hequiv. unfold equiv_tree_mcont in *. intros s Hss0.
      unfold tCharacterSetMatcher, Semantics.characterSetMatcher.
      simpl.
      remember ((_ <? 0)%Z || _) as b.
      destruct b.
      + simpl. reflexivity.
      + remember (Z.min _ _) as index.
        remember (List.List.Indexing.Int.indexing _ _) as chr'.
        destruct chr' as [chr'|]; simpl; try (exact I).
        remember (if CharSet.exist_canonicalized _ _ _ then false else true) as b2.
        destruct b2; simpl.
        1: reflexivity.
        remember (match_state _ _ _) as s'.
        specialize (Hequiv s').
        assert (MatchState.input s' = s0) as Hs's0.
        {
          rewrite Heqs'. simpl. apply Hss0.
        }
        specialize (Hequiv Hs's0).
        destruct (tmc s') as [child|]; simpl; try exact I.
        destruct (mc s') as [res|]; simpl; try exact I.
        replace (Z.min (MatchState.endIndex s) (MatchState.endIndex s + 1)) with (MatchState.endIndex s) in Heqindex by lia.
        rewrite Heqindex in Heqchr'.
        replace (nth _ _ chr') with chr' by admit.
        rewrite EqDec.reflb.
        rewrite <- Hequiv.
        f_equal.
        unfold advance_ms.
        rewrite Heqs'.
        reflexivity.
    
    - (* Dot; same as character *)
      intros _ mc tmc gl Hequiv. unfold equiv_tree_mcont in *. intros s Hss0.
      unfold tCharacterSetMatcher, Semantics.characterSetMatcher.
      simpl.
      remember ((_ <? 0)%Z || _) as b.
      destruct b.
      + simpl. reflexivity.
      + remember (Z.min _ _) as index.
        remember (List.List.Indexing.Int.indexing _ _) as chr'.
        destruct chr' as [chr'|]; simpl; try (exact I).
        remember (if CharSet.exist_canonicalized _ _ _ then false else true) as b2.
        destruct b2; simpl.
        1: reflexivity.
        remember (match_state _ _ _) as s'.
        specialize (Hequiv s').
        assert (MatchState.input s' = s0) as Hs's0.
        {
          rewrite Heqs'. simpl. apply Hss0.
        }
        specialize (Hequiv Hs's0).
        destruct (tmc s') as [child|]; simpl; try exact I.
        destruct (mc s') as [res|]; simpl; try exact I.
        replace (Z.min (MatchState.endIndex s) (MatchState.endIndex s + 1)) with (MatchState.endIndex s) in Heqindex by lia.
        rewrite Heqindex in Heqchr'.
        replace (nth _ _ chr') with chr' by admit.
        rewrite EqDec.reflb.
        rewrite <- Hequiv.
        f_equal.
        unfold advance_ms.
        rewrite Heqs'.
        reflexivity.
    
    - (* Atom escape: unsupported *)
      intro. destruct (match ae with | DecimalEsc de => _ | ACharacterClassEsc cce => _ | ACharacterEsc ce => _ | GroupEsc gn => _ end); split.
    
    - (* Character class: unsupported *)
      intro. destruct (let! _ =<< _ in _); split.
    
    - (* Disjunction *)
      intro ctx.
      remember (Disjunction_left reg2 :: ctx) as ctxleft.
      remember (Disjunction_right reg1 :: ctx) as ctxright.
      specialize (IHreg1 ctxleft).
      specialize (IHreg2 ctxright).
      destruct (Semantics.compileSubPattern reg1 _ _ _) as [m1|] eqn:?; simpl; try exact I.
      destruct (Semantics.compileSubPattern reg2 _ _ _) as [m2|] eqn:?; simpl; try exact I.
      destruct (tCompileSubPattern reg1 _ _ _) as [tm1|] eqn:?; simpl; try exact I.
      destruct (tCompileSubPattern reg2 _ _ _) as [tm2|] eqn:?; simpl; try exact I.
      simpl in *.
      intros mc tmc gl Hequiv s' Hs's0.
      specialize (IHreg1 mc tmc gl Hequiv s' Hs's0).
      specialize (IHreg2 mc tmc gl Hequiv s' Hs's0).
      simpl in *.
      destruct (tm1 s' tmc) as [t1|] eqn:?; simpl; try exact I.
      destruct (tm2 s' tmc) as [t2|] eqn:?; simpl; try exact I.
      destruct (m1 s' mc) as [r|] eqn:?; simpl; try exact I.
      destruct r eqn:?; simpl.
      + rewrite IHreg1. simpl. reflexivity.
      + destruct (m2 s' mc) as [r2|] eqn:?; simpl; try exact I.
        rewrite IHreg1. simpl. assumption.
    
    - (* Quantifier *)
      intro ctx.
      remember (Quantified_inner q :: ctx) as ctx'.
      specialize (IHreg ctx').
      destruct Semantics.compileSubPattern as [m|] eqn:Heqm; simpl. 2: exact I.
      destruct tCompileSubPattern as [tm|] eqn:Heqtm; simpl. 2: destruct (if (negb _) then _ else _); exact I.
      simpl in IHreg.
      destruct negb; simpl. 1: exact I.
      unfold equiv_tree_matcher.
      intros mc tmc gl Hequivcont. unfold equiv_tree_mcont.
      intros s Hss0.
      unfold Semantics.repeatMatcher.
      unfold tRepeatMatcher.
      now apply repeatMatcher'_tRepeatMatcher'.
    
    - (* Sequence *)
      intro ctx.
      remember (Seq_left reg2 :: ctx) as ctxleft.
      remember (Seq_right reg1 :: ctx) as ctxright.
      specialize (IHreg1 ctxleft).
      specialize (IHreg2 ctxright).
      destruct (Semantics.compileSubPattern reg1 _ _ _) as [m1|] eqn:?; simpl; try exact I.
      destruct (Semantics.compileSubPattern reg2 _ _ _) as [m2|] eqn:?; simpl; try exact I.
      destruct (tCompileSubPattern reg1 _ _ _) as [tm1|] eqn:?; simpl; try exact I.
      destruct (tCompileSubPattern reg2 _ _ _) as [tm2|] eqn:?; simpl; try exact I.
      simpl in *.
      intros mc tmc gl Hequiv s Hss0.
      specialize (IHreg2 mc tmc gl Hequiv).
      specialize (IHreg1 (fun s0 => m2 s0 mc) (fun s0 => tm2 s0 tmc) gl IHreg2 s Hss0).
      simpl in *.
      assumption.
    
    - (* Group *)
      intro ctx.
      remember (Group_inner name :: ctx) as ctx'.
      specialize (IHreg ctx').
      destruct (Semantics.compileSubPattern reg ctx' rer forward) as [m|] eqn:Heqm; simpl; try exact I.
      destruct (tCompileSubPattern reg ctx' rer forward) as [tm|] eqn:Heqtm; simpl; try exact I.
      intros mc tmc gl Hequiv s Hss0.
      simpl in *.
      unfold equiv_results.
      remember (fun y : MatchState => _) as treecont.
      remember (fun y : MatchState => let! r =<< _ in let! cap =<< _ in mc _) as origcont.
      remember (StaticSemantics.countLeftCapturingParensBefore _ ctx + 1) as gid.
      set (gl' := (gid, MatchState.endIndex s)::gl).
      specialize (IHreg origcont treecont gl').
      assert (equiv_tree_mcont origcont treecont gl') as Hequivcont.
      {
        intros y Hys0.
        rewrite Heqtreecont, Heqorigcont.
        remember (MatchState.endIndex s) as i.
        destruct negb eqn:Hi_le_y; simpl; try exact I.
        destruct (gid =? 0) eqn:Hgid_nonzero; simpl; try exact I.
        destruct List.List.Update.Nat.One.update as [cap'|] eqn:Hcapupd; simpl; try exact I.
        remember (match_state _ _ cap') as s'.
        destruct (tmc s') as [t|] eqn:Heqt; simpl; try exact I.
        destruct (mc s') as [res|] eqn:Heqres; simpl; try exact I.
        rewrite EqDec.reflb. simpl.
        rewrite Hgid_nonzero.
        (* Prove: the result of List.List.....Update does not depend on the type of the error that should be returned if any *)
        replace (@List.List.Update.Nat.One.update _ tree_res'_error _ _ _ (gid - 1)) with (@Success _ tree_res'_error cap') by admit.
        simpl.
        specialize (Hequiv s').
        assert (MatchState.input s' = s0) as Hs's0.
        {
          rewrite Heqs'. simpl. apply Hss0.
        }
        specialize (Hequiv Hs's0).
        rewrite Heqt, Heqres in Hequiv.
        rewrite Heqs' in Hequiv.
        rewrite Hss0 in Hequiv.
        rewrite Hys0.
        assumption.
      }
      specialize (IHreg Hequivcont s Hss0).
      simpl in *.
      destruct (tm s treecont) as [t|] eqn:Heqt; simpl; try exact I.
      destruct (m s origcont) as [res|] eqn:Heqres; simpl; try exact I.
      assumption.
    
    
    - (* Unsupported *)
      split.
    - (* Unsupported *)
      split.
    - (* Unsupported *)
      split.
    - (* Unsupported *)
      split.
    - (* Lookahead: unsupported *)
      intro. destruct (let! _ =<< _ in _); split.
    - (* Negative lookahead: unsupported *)
      intro. destruct (let! _ =<< _ in _); split.
    - (* Lookbehind: unsupported *)
      intro. destruct (let! _ =<< _ in _); split.
    - (* Negative lookbehind: unsupported *)
      intro. destruct (let! _ =<< _ in _); split.
  Admitted.

End Main.