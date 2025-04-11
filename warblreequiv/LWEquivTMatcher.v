From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List Program.Wf.
From Linden Require Import Tree LindenParameters CharsWarblre TMatching.
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


Definition equiv_tree (mc: MatcherContinuation) (tmc: TMatcherContinuation) (gl: open_groups) :=
  forall s: MatchState, 
  match tmc s, mc s with
  | Error _, _ | _, Error _ => True (* finer modeling? *)
  | Success t, Success res => tree_res' t s gl = Success res
  end.

Definition id_mcont: MatcherContinuation := fun x => Success (Some x).
Definition id_tmcont: TMatcherContinuation := fun _ => Success Match.

Lemma id_equiv: equiv_tree id_mcont id_tmcont nil.
Proof.
  intro s. simpl. reflexivity.
Qed.


Theorem compile_tcompile: forall reg ctx rer,
  let m' := Semantics.compileSubPattern reg ctx rer forward in
  let tm' := tCompileSubPattern reg ctx rer forward in
  match m', tm' with
  | Error _, _ | _, Error _ => True
  | Success m, Success tm =>
  forall mc tmc gl, equiv_tree mc tmc gl -> equiv_tree (fun s => m s mc) (fun s => tm s tmc) gl
  end.
Proof.
  intros reg ctx rer.
  revert ctx.
  induction reg; simpl.

  - (* Empty *)
    intros. unfold equiv_tree in *. assumption.
  
  - (* Character *)
    intros. unfold equiv_tree in *. intro.
    unfold tCharacterSetMatcher, Semantics.characterSetMatcher.
    simpl.
    remember ((_ <? 0)%Z || _) as b.
    destruct b.
    + simpl. reflexivity.
    + remember (Z.min _ _) as index.
      remember (List.List.Indexing.Int.indexing _ _) as chr'.
      destruct chr'; simpl; try (exact I).
      remember (if CharSet.exist_canonicalized _ _ _ then false else true) as b2.
      destruct b2; simpl.
      1: reflexivity.
      remember (match_state _ _ _) as s'.
      specialize (H s').
      destruct (tmc s'); simpl; try exact I.
      destruct (mc s'); simpl; try exact I.
      replace (Z.min (MatchState.endIndex s) (MatchState.endIndex s + 1)) with (MatchState.endIndex s) in Heqindex by lia.
      rewrite Heqindex in Heqchr'.
      replace (nth _ _ s0) with s0 by admit.
      rewrite EqDec.reflb.
      rewrite <- H.
      f_equal.
      unfold advance_ms.
      rewrite Heqs'.
      reflexivity.
  
  - (* Dot; mostly same as character *)
    intros.
    intro s.
    unfold tCharacterSetMatcher, Semantics.characterSetMatcher.
    simpl.
    remember ((_ <? 0)%Z || _) as b.
    destruct b.
    + simpl. reflexivity.
    + remember (Z.min _ _) as index.
      remember (List.List.Indexing.Int.indexing _ _) as chr'.
      destruct chr'; simpl; try (exact I).
      remember (if CharSet.exist_canonicalized _ _ _ then false else true) as b2.
      destruct b2; simpl.
      1: reflexivity.
      remember (match_state _ _ _) as s'.
      specialize (H s').
      destruct (tmc s'); simpl; try exact I.
      destruct (mc s'); simpl; try exact I.
      replace (Z.min (MatchState.endIndex s) (MatchState.endIndex s + 1)) with (MatchState.endIndex s) in Heqindex by lia.
      rewrite Heqindex in Heqchr'.
      replace (nth _ _ s0) with s0 by admit.
      rewrite EqDec.reflb.
      rewrite <- H.
      f_equal.
      unfold advance_ms.
      rewrite Heqs'.
      reflexivity.
  
  - (* Unsupported case *)
    intro. destruct (match ae with | DecimalEsc de => _ | ACharacterClassEsc cce => _ | ACharacterEsc ce => _ | GroupEsc gn => _ end); split.
  
  - (* Character class: unsupported *)
    intro. destruct (let! _ =<< _ in _); split.
  
  - (* Disjunction *)
    intro.
    remember (Disjunction_left reg2 :: ctx) as ctxleft.
    remember (Disjunction_right reg1 :: ctx) as ctxright.
    specialize (IHreg1 ctxleft).
    specialize (IHreg2 ctxright).
    destruct (Semantics.compileSubPattern reg1 _ _ _) as [m1|] eqn:?; simpl; try exact I.
    destruct (Semantics.compileSubPattern reg2 _ _ _) as [m2|] eqn:?; simpl; try exact I.
    destruct (tCompileSubPattern reg1 _ _ _) as [tm1|] eqn:?; simpl; try exact I.
    destruct (tCompileSubPattern reg2 _ _ _) as [tm2|] eqn:?; simpl; try exact I.
    simpl in *.
    intros.
    intro s'.
    specialize (IHreg1 mc tmc gl H s').
    specialize (IHreg2 mc tmc gl H s').
    simpl in *.
    destruct (tm1 s' tmc) as [t1|] eqn:?; simpl; try exact I.
    destruct (tm2 s' tmc) as [t2|] eqn:?; simpl; try exact I.
    destruct (m1 s' mc) as [r|] eqn:?; simpl; try exact I.
    destruct r eqn:?; simpl.
    + rewrite IHreg1. simpl. reflexivity.
    + destruct (m2 s' mc) as [r2|] eqn:?; simpl; try exact I.
      rewrite IHreg1. simpl. assumption.
  
  - (* Quantifier *)
    intro.
    admit.
  
  - (* Sequence *)
    intro.
    remember (Seq_left reg2 :: ctx) as ctxleft.
    remember (Seq_right reg1 :: ctx) as ctxright.
    specialize (IHreg1 ctxleft).
    specialize (IHreg2 ctxright).
    destruct (Semantics.compileSubPattern reg1 _ _ _) as [m1|] eqn:?; simpl; try exact I.
    destruct (Semantics.compileSubPattern reg2 _ _ _) as [m2|] eqn:?; simpl; try exact I.
    destruct (tCompileSubPattern reg1 _ _ _) as [tm1|] eqn:?; simpl; try exact I.
    destruct (tCompileSubPattern reg2 _ _ _) as [tm2|] eqn:?; simpl; try exact I.
    simpl in *.
    intros. intro.
    specialize (IHreg2 mc tmc gl H).
    specialize (IHreg1 (fun s0 => m2 s0 mc) (fun s0 => tm2 s0 tmc) gl IHreg2 s).
    simpl in *.
    assumption.
  
  - (* Group *)
    intro.
    remember (Group_inner name :: ctx) as ctx'.
    specialize (IHreg ctx').
    destruct (Semantics.compileSubPattern reg ctx' rer forward) as [m|] eqn:?; simpl; try exact I.
    destruct (tCompileSubPattern reg ctx' rer forward) as [tm|] eqn:?; simpl; try exact I.
    intros mc tmc gl H s.
    simpl in *.
    remember (fun y : MatchState => _) as treecont.
    remember (fun y : MatchState => let! r =<< _ in let! cap =<< _ in mc _) as origcont.
    remember (StaticSemantics.countLeftCapturingParensBefore _ ctx + 1) as gid.
    set (gl' := (gid, MatchState.endIndex s)::gl).
    specialize (IHreg origcont treecont gl').
    assert (equiv_tree origcont treecont gl') as Hequivcont.
    {
      intro y.
      rewrite Heqtreecont, Heqorigcont.
      remember (MatchState.endIndex s) as x.
      destruct negb eqn:?; simpl; try exact I.
      destruct (gid =? 0) eqn:?; simpl; try exact I.
      destruct List.List.Update.Nat.One.update eqn:?; simpl; try exact I.
      remember (match_state _ _ s0) as s'.
      destruct (tmc s') as [t|] eqn:?; simpl; try exact I.
      destruct (mc s') as [res|] eqn:?; simpl; try exact I.
      rewrite EqDec.reflb. simpl.
      rewrite Heqb0.
      (* Prove: the result of List.List.....Update does not depend on the type of the error that should be returned if any *)
      replace (@List.List.Update.Nat.One.update _ tree_res'_error _ _ _ (gid - 1)) with (@Success _ tree_res'_error s0) by admit.
      simpl.
      specialize (H s').
      rewrite Heqt, Heqm0 in H.
      rewrite Heqs' in H.
      (* mismatching inputs... but all the match states that we manipulate here use the same input, morally *)
      admit.
    }
    specialize (IHreg Hequivcont s).
    simpl in *.
    destruct (tm s treecont) as [t|] eqn:?; simpl; try exact I.
    destruct (m s origcont) as [res|] eqn:?; simpl; try exact I.
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
