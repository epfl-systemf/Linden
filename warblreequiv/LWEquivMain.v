From Warblre Require Import Semantics Frontend Result Errors Base List RegExpRecord Notation Patterns Match.
From Linden Require Import LindenParameters RegexpTranslation Regex Chars Tree Groups Semantics Utils TMatching LWEquivTMatcherDef LWEquivTMatcher LWEquivTree Tactics.
From Coq Require Import List ZArith Lia.
Import ListNotations.
Import Notation.
Import Result.
Import Result.Notations.
Import Coercions.
Import Match.

Local Open Scope result_flow.

(** * Main equivalence theorem *)


(* The main theorem *)
Theorem linden_warblre_equiv:
  forall (wreg: Patterns.Regex) (lreg: regex) (str: string) (rer: RegExpRecord)
    (matcher: string -> non_neg_integer -> MatchResult)
    (tmatcher: string -> non_neg_integer -> TMatchResult)
    (res: MatchResult) (tres: TMatchResult) (t: tree),
    RegExpRecord.ignoreCase rer = false ->
    RegExpRecord.multiline rer = false ->
    RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wreg [] ->
    (* For all pairs of equivalent Warblre and Linden regexes wreg and lreg, *)
    equiv_regex wreg lreg ->
    (* if the compilations of these regexes both succeed, *)
    Semantics.compilePattern wreg rer = Success matcher ->
    tCompilePattern wreg rer = Success tmatcher ->
    (* letting res and tres be the respective results of these matchers on some input string str, *)
    res = matcher str 0 -> tres = tmatcher str 0 ->
    (* these results define the same capture groups if both matchings succeed and *)
    LWEquivTMatcherDef.equiv_results tres (MatchState.init rer str 0) [] forward res /\
      (* in this case, the backtree of the tree matcher respects the relational semantics. *)
      (tres = Success t -> is_tree lreg [] (init_input str) forward t).
Proof.
  intros wreg lreg str rer matcher tmatcher res tres t Hcasesenst Hnomultiline Hcapcount Hequiv.
  unfold Semantics.compilePattern, tCompilePattern.
  
  pose proof compile_tcompile wreg [] rer as Hcompile_tcompile.
  pose proof tmatcher_bt rer lreg wreg Hcasesenst Hnomultiline Hequiv wreg lreg [] as Hbt.
  specialize_prove Hbt by constructor. specialize (Hbt Hequiv).
  
  destruct Semantics.compileSubPattern as [m|] eqn:Heqm; simpl. 2: discriminate.
  destruct tCompileSubPattern as [tm|] eqn:Heqtm; simpl. 2: discriminate.
  specialize (Hcompile_tcompile m tm forward Heqm Heqtm str).
  specialize (Hbt tm forward Heqtm).
  intros Heqmatcher Heqtmatcher. injection Heqmatcher as <-. injection Heqtmatcher as <-.
  intros Heqres Heqtres. subst res tres.
  destruct negb. (* Negative length! *) 1: { split. - constructor. - discriminate. }
  split.
  - apply Hcompile_tcompile. + apply id_equiv. + reflexivity.
  - specialize (Hbt id_tmcont [] str (id_tmcont_valid rer str forward)).
    specialize (Hbt (init_input str) (MSInput.init_input_compat str)).
    set (ms := match_state str 0 _). specialize (Hbt ms t).
    specialize_prove Hbt by apply MSInput.init_ms_matches_inp. simpl in Hbt.
    intro Hsucctm. specialize (Hbt Hsucctm). now inversion Hbt.
Qed.
