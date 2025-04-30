From Linden Require Import Chars TMatching TreeMSInterp Tree LindenParameters.
From Warblre Require Import Notation Result Errors Parameters Base.
Import Notation.

(** * Definition of the equivalence of Matchers and TMatchers *)
(* and of TMatcherContinuations and MatcherContinuations, and of
   TMatchResults and MatchResults *)


(* Expresses the equivalence between the first branch of a sub-backtracking tree
   with its corresponding extended match state on the one hand, with a
   MatchResult on the other hand.
   The direction argument is needed to interpret the tree correctly (i.e. to advance the end indices in the right directions).
   This simply unwraps the error monad; we currently do not say anything
   when either match result is an error (any error is equivalent to anything
   in both directions). *)
Inductive equiv_results: TMatchResult -> MatchState -> open_groups -> Direction -> MatchResult -> Prop :=
| Equiv_results:
  forall (t: tree) (ms: MatchState) (open_gl: open_groups) (dir: Direction) (res: option MatchState),
    res = tree_res' t ms open_gl dir ->
    equiv_results (Success t) ms open_gl dir (Success res)
| Equiv_results_errl:
  forall errl ms open_gl dir res', equiv_results (Error errl) ms open_gl dir res'
| Equiv_results_errr:
  forall t' ms open_gl dir errr, equiv_results t' ms open_gl dir (Error errr).


(* A continuation is always called at a fixed position in the regexp, so with a
   fixed list of groups that are currently open, as well as a fixed direction.
   We say that a MatcherContinuation mc and a TMatcherContinuation tmc are
   equivalent under a given input string str0, the list of open groups
   open_gl and direction dir when given any MatchState ms compatible with the string str0 being
   matched, the sub-backtree (tmc ms) with extended match state (ms, open_gl) interpreted in direction dir is
   equivalent to the MatchResult (mc ms). *)
Definition equiv_tree_mcont
  (str0: string) (mc: MatcherContinuation) (tmc: TMatcherContinuation)
  (gl: open_groups) (dir: Direction) :=
  forall s: MatchState, MatchState.input s = str0 -> equiv_results (tmc s) s gl dir (mc s).

(* A (T)Matcher matches a regexp in some direction, then calls a continuation after matching
   the said regexp.
   We say that a Matcher m and a TMatcher tm of direction dir are equivalent under the input
   string str0 when given equivalent continuations of direction dir, we obtain back equivalent
   continuations of direction dir. Indeed, we never flip the direction of a continuation
   plugged into a Matcher. *)
Definition equiv_tree_matcher (str0: string) (m: Matcher) (tm: TMatcher) (dir: Direction) :=
  forall mc tmc gl,
    equiv_tree_mcont str0 mc tmc gl dir ->
    equiv_tree_mcont str0 (fun s => m s mc) (fun s => tm s tmc) gl dir.

