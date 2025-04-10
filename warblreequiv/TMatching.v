From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List Program.Wf.
From Linden Require Import Tree LindenParameters CharsWarblre.
From Warblre Require Import Patterns Result Notation Errors Node RegExpRecord Base Coercions Semantics Typeclasses.
Import Patterns.
Import Result.Result.
Import Result.Notations.
Import Result.Notations.Boolean.
Import Coercions.
Import Notation.

Local Open Scope result_flow.

Parameter axiom: forall A: Type, A.
Arguments axiom {_}.

Definition TMatchResult := Result tree MatchError.
Definition TMatcherContinuation := Notation.MatchState -> TMatchResult.
Definition TMatcher := Notation.MatchState -> TMatcherContinuation -> TMatchResult.

Fixpoint suffix {A: Type} (n: nat) (l: list A): list A :=
  match n, l with
  | 0, _ => l
  | _, nil => nil
  | S n', x::q => suffix n' q
  end.

Definition ms_suffix (s: MatchState) :=
  suffix (Z.to_nat (MatchState.endIndex s)) (MatchState.input s).


(** >>
    22.2.2.3.1 RepeatMatcher ( m, min, max, greedy, x, c, parenIndex, parenCount )

    The abstract operation RepeatMatcher takes arguments m (a Matcher), min (a non-negative integer),
    max (a non-negative integer or +∞), greedy (a Boolean), x (a MatchState), c (a MatcherContinuation),
    parenIndex (a non-negative integer), and parenCount (a non-negative integer) and returns a MatchResult.
    It performs the following steps when called:
<<*)
(* + Coq wants to make sure the function will terminate; we do so by bounding recursion by an arbitrary fuel amount +*)
Fixpoint tRepeatMatcher' (m: TMatcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) (greedy: bool) (x: MatchState) (c: TMatcherContinuation) (parenIndex parenCount: non_neg_integer) (fuel: nat): TMatchResult :=
match fuel with
| 0 => out_of_fuel
| S fuel' =>
  (*>> 1. If max = 0, return c(x). <<*)
  if (max =? 0)%NoI then c x else
  (*>> 2. Let d be a new MatcherContinuation with parameters (y) that captures m, min, max, greedy, x, c, parenIndex, and parenCount and performs the following steps when called: <<*)
  let d: TMatcherContinuation := fun (y: MatchState) =>
    (*>> a. Assert: y is a MatchState. <<*)
    (*>> b. If min = 0 and y's endIndex = x's endIndex, return failure. <<*)
    if (min == 0)%nat && (MatchState.endIndex y =? MatchState.endIndex x)%Z
      then Success (CheckFail (ms_suffix x)) else
    (*>> c. If min = 0, let min2 be 0; otherwise let min2 be min - 1. <<*)
    let min2 :=
      if (min == 0)%nat then 0
      else min - 1
    in
    (*>> d. If max = +∞, let max2 be +∞; otherwise let max2 be max - 1. <<*)
    let max2 :=
      if (max =? +∞)%NoI then +∞
      else (max - 1)%NoI
    in
    (*>> e. Return RepeatMatcher(m, min2, max2, greedy, y, c, parenIndex, parenCount). <<*)
    let! subtree =<< tRepeatMatcher' m min2 max2 greedy y c parenIndex parenCount fuel' in
    Success (CheckPass (ms_suffix x) subtree)
  in
  (*>> 3. Let cap be a copy of x's captures List. <<*)
  let cap := MatchState.captures x in
  (*>> 4. For each integer k in the inclusive interval from parenIndex + 1 to parenIndex + parenCount, set cap[k] to undefined. <<*)
  (* + The additional +1 is normal: the range operator --- is non-inclusive on the right +*)
  set cap[(parenIndex + 1) --- (parenIndex + parenCount + 1) ] := undefined in
  let! subtree =<<
    (*>> 5. Let Input be x's input. <<*)
    let input := MatchState.input x in
    (*>> 6. Let e be x's endIndex. <<*)
    let e := MatchState.endIndex x in
    (*>> 7. Let xr be the MatchState (Input, e, cap). <<*)
    let xr := match_state input e cap in
    (*>> 8. If min ≠ 0, return m(xr, d). <<*)
    if (min !=? 0)%nat
      then m xr d else
    (*>> 9. If greedy is false, then <<*)
    if greedy is false then
      (*>> a. Let z be c(x). <<*)
      let! z =<< c x in
      (*>> b. If z is not failure, return z. <<*)
      (*>> c. Return m(xr, d). <<*)
      let! z' =<< m xr d in
      Success (Choice z z')
    else
    (*>> 10. Let z be m(xr, d). <<*)
    let! z =<< m xr d in
    (*>> 11. If z is not failure, return z. <<*)
    (*>> 12. Return c(x). <<*)
    let! z' =<< c x in
    Success (Choice z z')
  in Success (GroupAction (Reset (List.seq (parenIndex + 1) parenCount)) subtree)
end.

Definition tRepeatMatcher (m: TMatcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) (greedy: bool) (x: MatchState) (c: TMatcherContinuation) (parenIndex parenCount: non_neg_integer): TMatchResult :=
  tRepeatMatcher' m min max greedy x c parenIndex parenCount (Semantics.repeatMatcherFuel min x).

(** >>
    22.2.2.7.1 CharacterSetMatcher ( rer, A, invert, direction )

    The abstract operation CharacterSetMatcher takes arguments rer (a RegExp Record), A (a CharSet), invert
    (a Boolean), and direction (forward or backward) and returns a Matcher. It performs the following steps when
    called:
<<*)
Definition tCharacterSetMatcher (rer: RegExpRecord) (A: CharSet) (invert: bool) (direction: Direction): TMatcher :=
  (*>> 1. Return a new Matcher with parameters (x, c) that captures rer, A, invert, and direction and performs the following steps when called: <<*)
  fun (x: MatchState) (c: TMatcherContinuation) =>
    (*>> a. Assert: x is a MatchState. <<*)
    (*>> b. Assert: c is a MatcherContinuation. <<*)
    (*>> c. Let Input be x's input. <<*)
    let input := MatchState.input x in
    (*>> d. Let e be x's endIndex. <<*)
    let e := MatchState.endIndex x in
    (*>> e. If direction is forward, let f be e + 1. <<*)
    (*>> f. Else, let f be e - 1. <<*)
    let f := if direction == forward
      then (e + 1)%Z
      else (e - 1)%Z
    in
    (*>> g. Let InputLength be the number of elements in Input. <<*)
    let inputLength := Z.of_nat (length input) in
    (*>> h. If f < 0 or f > InputLength, return failure. <<*)
    if (f <? 0)%Z || (f >? inputLength)%Z then
      Success Mismatch
    else
    (*>> i. Let index be min(e, f). <<*)
    let index := Z.min e f in
    (*>> j. Let ch be the character Input[index]. <<*)
    let! chr =<< input[ index ] in
    (*>> k. Let cc be Canonicalize(rer, ch). <<*)
    let cc := Character.canonicalize rer chr in
    (*>> l. If there exists a member a of A such that Canonicalize(rer, a) is cc, let found be true. Otherwise, let found be false. <<*)
    let found := CharSet.exist_canonicalized rer A cc in
    (*>> m. If invert is false and found is false, return failure. <<*)
    if (invert is false) && (found is false) then
      Success Mismatch
    (*>> n. If invert is true and found is true, return failure. <<*)
    else if (invert is true) && (found is true) then
      Success Mismatch
    else
    (*>> o. Let cap be x's captures List. <<*)
    let cap := MatchState.captures x in
    (*>> p. Let y be the MatchState (Input, f, cap). <<*)
    let y := match_state input f cap in
    (*>> q. Return c(y). <<*)
    let! child =<< c y in
    Success (Read chr child).

Fixpoint tCompileSubPattern (self: Regex) (ctx: RegexContext) (rer: RegExpRecord) (direction: Direction): Result TMatcher CompileError :=
match self with
| Disjunction r1 r2 =>
    let! m1 =<< tCompileSubPattern r1 (Disjunction_left r2 :: ctx) rer direction in
    let! m2 =<< tCompileSubPattern r2 (Disjunction_right r1 :: ctx) rer direction in
    Success ((fun (x: MatchState) (tmc: TMatcherContinuation) =>
        let! t1 =<< m1 x tmc in
        let! t2 =<< m2 x tmc in
        Success (Choice t1 t2)): TMatcher)
| Empty =>
    Success (fun x c => c x)
| Seq r1 r2 =>
    (*>> 1. Let m1 be CompileSubpattern of Alternative with arguments rer and direction. <<*)
    let! m1 =<< tCompileSubPattern r1 (Seq_left r2 :: ctx) rer direction in
    (*>> 2. Let m2 be CompileSubpattern of Term with arguments rer and direction. <<*)
    let! m2 =<< tCompileSubPattern r2 (Seq_right r1 :: ctx) rer direction in
    (*>> 3. If direction is forward, then <<*)
    if direction is forward then
      (*>> a. Return a new Matcher with parameters (x, c) that captures m1 and m2 and performs the following steps when called: <<*)
      Success ((fun (s: MatchState) (c: TMatcherContinuation) =>
        (*>> i. Assert: x is a MatchState. <<*)
        (*>> ii. Assert: c is a MatcherContinuation. <<*)
        (*>> iii. Let d be a new MatcherContinuation with parameters (y) that captures c and m2 and performs the following steps when called: <<*)
        let d: TMatcherContinuation := fun (s: MatchState) => 
          (*>> 1. Assert: y is a MatchState. <<*)
          (*>> 2. Return m2(y, c). <<*)
          m2 s c
        in
        (*>> iv. Return m1(x, d). <<*)
        m1 s d): TMatcher)
    (*>> 4. Else, <<*)
    else
      (*>> a. Assert: direction is backward. <<*)
      (*>> b. Return a new Matcher with parameters (x, c) that captures m1 and m2 and performs the following steps when called: <<*)
      Success ((fun (s: MatchState) (c: TMatcherContinuation) =>
        (*>> i. Assert: x is a MatchState. <<*)
        (*>> ii. Assert: c is a MatcherContinuation. <<*)
        (*>> iii. Let d be a new MatcherContinuation with parameters (y) that captures c and m1 and performs the following steps when called: <<*)
        let d: TMatcherContinuation := fun (s: MatchState) =>
          (*>> 1. Assert: y is a MatchState. <<*)
          (*>> 2. Return m1(y, c). <<*)
          m1 s c 
        in
        (*>> iv. Return m2(x, d). <<*)
        m2 s d): TMatcher)
| Quantified r qu =>
    (*>> 1. Let m be CompileAtom of Atom with arguments rer and direction. <<*)
    let! m =<< tCompileSubPattern r  (Quantified_inner qu :: ctx) rer direction in
    (*>> 2. Let q be CompileQuantifier of Quantifier. <<*)
    let q := Semantics.compileQuantifier qu in
    (*>> 3. Assert: q.[[Min]] ≤ q.[[Max]]. <<*)
    assert! (Semantics.CompiledQuantifier_min q <=? Semantics.CompiledQuantifier_max q)%NoI;
    (*>> 4. Let parenIndex be CountLeftCapturingParensBefore(Term). <<*)
    let parenIndex := StaticSemantics.countLeftCapturingParensBefore r ctx in
    (*>> 5. Let parenCount be CountLeftCapturingParensWithin(Atom). <<*)
    let parenCount := StaticSemantics.countLeftCapturingParensWithin r (Quantified_inner qu :: ctx) in
    (*>> 6. Return a new Matcher with parameters (x, c) that captures m, q, parenIndex, and parenCount and performs the following steps when called: <<*)
    Success ((fun (x: MatchState) (c: TMatcherContinuation) =>
    (*>> a. Assert: x is a MatchState. <<*)
    (*>> b. Assert: c is a MatcherContinuation. <<*)
    (*>> c. Return RepeatMatcher(m, q.[[Min]], q.[[Max]], q.[[Greedy]], x, c, parenIndex, parenCount). <<*)
        tRepeatMatcher m (Semantics.CompiledQuantifier_min q) (Semantics.CompiledQuantifier_max q) (Semantics.CompiledQuantifier_greedy q) x c parenIndex parenCount): TMatcher)
(** >> Atom :: PatternCharacter <<*)
| Char c =>
  (*>> 1. Let ch be the character matched by PatternCharacter. <<*)
  let ch := c in
  (*>> 2. Let A be a one-element CharSet containing the character ch. <<*)
  let A := CharSet.singleton c in
  (*>> 3. Return CharacterSetMatcher(rer, A, false, direction). <<*)
  Success (tCharacterSetMatcher rer A false direction)

(** >> Atom :: . <<*)
| Dot =>
  (*>> 1. Let A be the CharSet of all characters. <<*)
  let A := Characters.all in
  (*>> 2. If rer.[[DotAll]] is not true, then <<*)
  let A := if RegExpRecord.dotAll rer is not true
    (*>> a. Remove from A all characters corresponding to a code point on the right-hand side of the LineTerminator production. <<*)
    then CharSet.remove_all A Characters.line_terminators
    else A
  in
  (*>> 3. Return CharacterSetMatcher(rer, A, false, direction). <<*)
  Success (tCharacterSetMatcher rer A false direction)


(** >> Atom :: ( GroupSpecifier_opt Disjunction ) <<*)
| Group id r =>
    (*>> 1. Let m be CompileSubpattern of Disjunction with arguments rer and direction. <<*)
    let! m =<< tCompileSubPattern r (Group_inner id :: ctx) rer direction in
    (*>> 2. Let parenIndex be CountLeftCapturingParensBefore(Atom). <<*)
    let parenIndex := StaticSemantics.countLeftCapturingParensBefore self ctx in
    (*>> 3. Return a new Matcher with parameters (x, c) that captures direction, m, and parenIndex and performs the following steps when called: <<*)
    Success ((fun (x: MatchState) (c: TMatcherContinuation) =>
      (*>> a. Assert: x is a MatchState. <<*)
      (*>> b. Assert: c is a MatcherContinuation. <<*)
      (*>> c. Let d be a new MatcherContinuation with parameters (y) that captures x, c, direction, and parenIndex and performs the following steps when called: <<*)
      let d: TMatcherContinuation := fun (y: MatchState) =>
        (*>> i. Assert: y is a MatchState. <<*)
        (*>> ii. Let cap be a copy of y's captures List. <<*)
        let cap := MatchState.captures y in
        (*>> iii. Let Input be x's input. <<*)
        let input := MatchState.input x in
        (*>> iv. Let xe be x's endIndex. <<*)
        let xe := MatchState.endIndex x in
        (*>> v. Let ye be y's endIndex. <<*)
        let ye := MatchState.endIndex y in
        let! r =<<
          (*>> vi. If direction is forward, then <<*)
          if direction == forward then
            (*>> 1. Assert: xe ≤ ye. <<*)
            assert! (xe <=? ye)%Z ;
            (*>> 2. Let r be the CaptureRange (xe, ye). <<*)
            capture_range xe ye
          (*>> vii. Else, <<*)
          else
            (*>> 1. Assert: direction is backward. <<*)
            (*>> 2. Assert: ye ≤ xe. <<*)
            assert! (ye <=? xe)%Z ;
            (*>> 3. Let r be the CaptureRange (ye, xe). <<*)
            capture_range ye xe
        in
        (*>> viii. Set cap[parenIndex + 1] to r. <<*)
        set cap[parenIndex + 1] := r in
        (*>> ix. Let z be the MatchState (Input, ye, cap). <<*)
        let z := match_state input ye cap in
        (*>> x. Return c(z). <<*)
        let! subtree =<< c z in
        Success (GroupAction (Close (parenIndex + 1)) subtree)
      in
      (*>> d. Return m(x, d). <<*)
      let! subtree =<< m x d in
      Success (GroupAction (Open (parenIndex + 1)) subtree)): TMatcher)
| _ => Error CompileError.AssertionFailed
end.

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