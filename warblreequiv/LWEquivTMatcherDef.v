From Linden Require Import Chars TMatching TreeMSInterp Tree LindenParameters.
From Warblre Require Import Notation Result Errors Parameters.
Import Notation.

(* Expresses the equivalence between the first branch of a sub-backtracking tree
   with its corresponding extended match state on the one hand, with a
   MatchResult on the other hand.
   This simply unwraps the error monad; we currently do not say anything
   when either match result is an error (any error is equivalent to anything
   in both directions). *)
Inductive equiv_results: TMatchResult -> MatchState -> open_groups -> MatchResult -> Prop :=
| Equiv_results:
  forall (t: tree) (ms: MatchState) (open_gl: open_groups) (res: option MatchState),
    res = tree_res' t ms open_gl ->
    equiv_results (Success t) ms open_gl (Success res)
| Equiv_results_errl:
  forall errl ms open_gl res', equiv_results (Error errl) ms open_gl res'
| Equiv_results_errr:
  forall t' ms open_gl errr, equiv_results t' ms open_gl (Error errr).


(* A continuation is always called at a fixed position in the regexp, so with a *)
(* fixed list of groups that are currently open. *)
(* We say that a MatcherContinuation mc and a TMatcherContinuation tmc are *)
(* equivalent under a given input string str0 and the list of open groups *)
(* open_gl when given any MatchState ms compatible with the string str0 being *)
(* matched, the sub-backtree (tmc s) with extended match state (s, open_gl) is *)
(* equivalent to the MatchResult (mc s). *)
Definition equiv_tree_mcont
  (str0: string) (mc: MatcherContinuation) (tmc: TMatcherContinuation)
  (gl: open_groups) :=
  forall s: MatchState, MatchState.input s = str0 -> equiv_results (tmc s) s gl (mc s).

(* A (T)Matcher matches a regexp, then calls a continuation after matching
   the said regexp.
   We say that a Matcher m and a TMatcher tm are equivalent under the input
   string str0 when given equivalent continuations, we obtain back equivalent
   continuations. *)
Definition equiv_tree_matcher (str0: string) (m: Matcher) (tm: TMatcher) :=
  forall mc tmc gl,
    equiv_tree_mcont str0 mc tmc gl ->
    equiv_tree_mcont str0 (fun s => m s mc) (fun s => tm s tmc) gl.

