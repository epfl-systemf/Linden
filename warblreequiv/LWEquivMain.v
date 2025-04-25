From Warblre Require Import Semantics Frontend Result Errors Base List RegExpRecord Notation Patterns.
From Linden Require Import LindenParameters RegexpTranslation Regex Chars Tree Groups Semantics Utils TMatching LWEquivTMatcherDef LWEquivTree.
From Coq Require Import List ZArith.
Import ListNotations.
Import Notation.
Import Result.
Import Result.Notations.
Import Coercions.

Local Open Scope result_flow.

(** * Frontend equivalence theorem *)


(* Initial match state given a string and a RegExpRecord *)
Definition init_match_state (str: string) (rer: RegExpRecord): MatchState :=
  let cap := List.repeat undefined (RegExpRecord.capturingGroupsCount rer) in
  match_state str 0%Z cap.


(* The main theorem *)
Theorem linden_warblre_equiv:
  forall (wreg: Patterns.Regex) (lreg: regex) (str: string) (rer: RegExpRecord)
    (matcher: string -> non_neg_integer -> MatchResult)
    (tmatcher: string -> non_neg_integer -> TMatchResult)
    (res: MatchResult) (tres: TMatchResult) (t: tree),
    RegExpRecord.ignoreCase rer = false ->
    RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wreg [] ->
    equiv_regex wreg lreg ->
    Semantics.compilePattern wreg rer = Success matcher ->
    tCompilePattern wreg rer = Success tmatcher ->
    res = matcher str 0 -> tres = tmatcher str 0 ->
    LWEquivTMatcherDef.equiv_results tres (init_match_state str rer) [] res /\
      (tres = Success t -> is_tree lreg [] (init_input str) t).
Proof.

Admitted.
