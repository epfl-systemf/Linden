From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List Program.Wf.
From Warblre Require Import RegExpRecord Tactics Focus Result Base Patterns Errors StaticSemantics Node Notation List Typeclasses Semantics.

Import Result.Notations.
Import Result.Notations.Boolean.
Import Coercions.
Local Open Scope result_flow.

Import Patterns.
Import Notation.

From Linden Require Import Chars Regex Semantics Tree Groups.
From Linden Require Import LindenParameters.

Inductive ms_matches_inp: MatchState -> input -> Prop :=
| Ms_matches_inp: forall (s: string) (end_ind: nat) cap (next pref: string),
    List.length pref = end_ind -> List.rev pref ++ next = s ->
    ms_matches_inp {| MatchState.input := s; MatchState.endIndex := Z.of_nat end_ind;
        MatchState.captures := cap |} (Input next pref).

Definition closegroup_nextstate (x: MatchState) (direction: Direction) (parenIndex: non_neg_integer) (y: MatchState) :=
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
    Success z.

Definition closegroup_matcher (x: MatchState) (direction: Direction) (parenIndex: non_neg_integer) (y: MatchState) (c: MatcherContinuation) :=
    let! z =<< closegroup_nextstate x direction parenIndex y in
    c z.

Definition disj_matcher (m1 m2: Matcher) (x: MatchState) (c: MatcherContinuation) :=
  (*>> a. Assert: x is a MatchState. <<*)
  (*>> b. Assert: c is a MatcherContinuation. <<*)
  (*>> c. Let r be m1(x, c). <<*)
  let! r =<< m1 x c in
  (*>> d. If r is not failure, return r. <<*)
  if r != failure then
    r
  else
  (*>> e. Return m2(x, c). <<*)
  m2 x c.

Definition seq_matcher (m1 m2: Matcher) (direction: Direction): Matcher :=
  (*>> 3. If direction is forward, then <<*)
  if direction is forward then
    (*>> a. Return a new Matcher with parameters (x, c) that captures m1 and m2 and performs the following steps when called: <<*)
    (fun (s: MatchState) (c: MatcherContinuation) =>
      (*>> i. Assert: x is a MatchState. <<*)
      (*>> ii. Assert: c is a MatcherContinuation. <<*)
      (*>> iii. Let d be a new MatcherContinuation with parameters (y) that captures c and m2 and performs the following steps when called: <<*)
      let d: MatcherContinuation := fun (s: MatchState) => 
        (*>> 1. Assert: y is a MatchState. <<*)
        (*>> 2. Return m2(y, c). <<*)
        m2 s c
      in
      (*>> iv. Return m1(x, d). <<*)
      m1 s d): Matcher
  (*>> 4. Else, <<*)
  else
    (*>> a. Assert: direction is backward. <<*)
    (*>> b. Return a new Matcher with parameters (x, c) that captures m1 and m2 and performs the following steps when called: <<*)
    (fun (s: MatchState) (c: MatcherContinuation) =>
      (*>> i. Assert: x is a MatchState. <<*)
      (*>> ii. Assert: c is a MatcherContinuation. <<*)
      (*>> iii. Let d be a new MatcherContinuation with parameters (y) that captures c and m1 and performs the following steps when called: <<*)
      let d: MatcherContinuation := fun (s: MatchState) =>
        (*>> 1. Assert: y is a MatchState. <<*)
        (*>> 2. Return m1(y, c). <<*)
        m1 s c 
      in
      (*>> iv. Return m2(x, d). <<*)
      m2 s d).

Definition char_matcher (c: Char) (direction: Direction) (rer: RegExpRecord) :=
  (*>> 1. Let ch be the character matched by PatternCharacter. <<*)
  let ch := c in
  (*>> 2. Let A be a one-element CharSet containing the character ch. <<*)
  let A := CharSet.singleton c in
  (*>> 3. Return CharacterSetMatcher(rer, A, false, direction). <<*)
  Semantics.characterSetMatcher rer A false direction.

Inductive matcher_tree: Matcher -> MatchState -> MatcherContinuation -> regex -> continuation -> input -> tree -> Prop :=
| mtree_epsilon: forall m: Matcher,
    (forall s c, m s c = c s) ->
    forall mstate inp, ms_matches_inp mstate inp ->
    matcher_tree m mstate (fun x => Success (Some x)) Epsilon nil inp Match
| mtree_pop_reg: forall m: Matcher,
    (forall s c, m s c = c s) ->
    forall m' s c' reg tailcont inp t, ms_matches_inp s inp ->
    matcher_tree m' s c' reg tailcont inp t ->
    matcher_tree m s (fun s0 => m' s0 c') Epsilon (Areg reg::tailcont) inp t
| mtree_pop_close: forall (m: Matcher) (gid: group_id) (y: MatchState) (dir: Direction),
    (forall s c, m s c = closegroup_matcher y dir (gid-1) s c) ->
    forall m' s c' tailcont inp t z, ms_matches_inp s inp ->
    matcher_tree m' z c' Epsilon tailcont inp t ->
    closegroup_nextstate y dir (gid-1) s = Success z -> matcher_tree m s (fun s0 => m' s0 c') Epsilon (Aclose gid::tailcont) inp t
| mtree_disj:
    forall m m1 m2: Matcher, (forall s c, m s c = disj_matcher m1 m2 s c) ->
    forall s c r1 r2 inp cont t1 t2,
    ms_matches_inp s inp ->
    matcher_tree m1 s c r1 cont inp t1 ->
    matcher_tree m2 s c r2 cont inp t2 ->
    matcher_tree m s c (Disjunction r1 r2) cont inp (Choice t1 t2)
| mtree_seq:
    forall (m m1 m2: Matcher) (dir: Direction), (forall s c, m s c = seq_matcher m1 m2 dir s c) ->
    forall s c r1 r2 cont inp t,
    matcher_tree m1 s (fun s0 => m2 s0 c) r1 (Areg r2::cont) inp t ->
    matcher_tree m s c (Sequence r1 r2) cont inp t
. (* TODO? *)