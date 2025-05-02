From Warblre Require Import Patterns Semantics RegExpRecord Notation Result Base Node Errors.
From Linden Require Import LindenParameters Regex.
Import Notation.
Import Result.Notations.
Import Patterns.
From Coq Require Import List.
Import ListNotations.

Local Open Scope result_flow.
Local Open Scope bool_scope.

(* We factorize lookarounds as a pair of a Direction and a boolean (positivity). *)

Definition lkCtx (lkdir: Direction) (pos: bool) :=
  match lkdir, pos with
  | forward, true => Lookahead_inner
  | forward, false => NegativeLookahead_inner
  | backward, true => Lookbehind_inner
  | backward, false => NegativeLookbehind_inner
  end.

Definition to_lookaround (lkdir: Direction) (pos: bool) :=
  match lkdir, pos with
  | forward, true => LookAhead
  | forward, false => NegLookAhead
  | backward, true => LookBehind
  | backward, false => NegLookBehind
  end.

Definition to_warblre_lookaround (dir: Direction) (pos: bool) :=
  match dir, pos with
  | forward, true => Patterns.Lookahead
  | forward, false => Patterns.NegativeLookahead
  | backward, true => Patterns.Lookbehind
  | backward, false => Patterns.NegativeLookbehind
  end.

Lemma lkdir_to_lookaround:
  forall lkdir pos, lk_dir (to_lookaround lkdir pos) = lkdir.
Proof.
  now intros [] [].
Qed.

Lemma positivity_to_lookaround:
  forall lkdir pos, positivity (to_lookaround lkdir pos) = pos.
Proof.
  now intros [] [].
Qed.


(* Factorization of cases of Semantics.compileSubPattern corresponding to lookarounds. *)
Definition lookaroundMatcher (compileSubPattern: Regex -> RegexContext -> RegExpRecord -> Direction -> Result Matcher CompileError) (lkdir: Direction) (pos: bool) (lkreg: Regex) (ctx: RegexContext) (rer: RegExpRecord) (direction: Direction): Result Matcher CompileError :=
  let! m =<< compileSubPattern lkreg (lkCtx lkdir pos :: ctx) rer lkdir in
  Success ((fun (x: MatchState) (c: MatcherContinuation) =>
    let d: MatcherContinuation := fun (y: MatchState) => Success (Some y) in
    let! r =<< m x d in
    if (pos && r == None) || (negb pos && r != None) then
      Success None
    else if pos then
      destruct! (Some y) <- r in
      let cap := MatchState.captures y in
      let input := MatchState.input x in
      let xe := MatchState.endIndex x in
      let z := match_state input xe cap in
      c z
    else
      c x): Matcher).

(* This is indeed a factorization of said cases. *)
Lemma lookaroundMatcher_fact:
  forall lkdir pos lkreg ctx rer dir c x,
    (match Semantics.compileSubPattern ((to_warblre_lookaround lkdir pos) lkreg) ctx rer dir with
     | Success m => Success (m x c)
     | Error e => Error e
     end) =
      (match lookaroundMatcher Semantics.compileSubPattern lkdir pos lkreg ctx rer dir with
       | Success m => Success (m x c)
       | Error e => Error e
       end).
Proof.
  intros [|] [|] lkreg ctx rer dir c x; unfold lookaroundMatcher; simpl; destruct Semantics.compileSubPattern as [msub|]; simpl; try reflexivity.
  - destruct msub; simpl; auto. rewrite Bool.orb_false_r. reflexivity.
  - destruct msub; simpl; auto. rewrite Bool.orb_false_r. reflexivity.
Qed.
