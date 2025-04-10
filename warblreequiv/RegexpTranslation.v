From Warblre Require Import Patterns Result Errors Coercions Notation Base.
From Linden Require Import Regex CharsWarblre LindenParameters.
Import Notation.
Import Result.
Import Result.Notations.
Local Open Scope result_flow.

Fixpoint to_warblre_regex (r: regex): Result Patterns.Regex CompileError :=
  match r with
  | Epsilon => Success Patterns.Empty
  | Character cd => char_descr_to_regex cd
  | Disjunction r1 r2 =>
    let! wr1 =<< to_warblre_regex r1 in
    let! wr2 =<< to_warblre_regex r2 in
    Success (Patterns.Disjunction wr1 wr2)
  | Sequence r1 r2 =>
    let! wr1 =<< to_warblre_regex r1 in
    let! wr2 =<< to_warblre_regex r2 in
    Success (Patterns.Seq wr1 wr2)
  | Star greedy r1 =>
    let! wr1 =<< to_warblre_regex r1 in
    Success (Patterns.Quantified wr1 (if greedy then Patterns.Greedy Patterns.Star else Patterns.Lazy Patterns.Star))
  | Group id r =>
    let! wr =<< to_warblre_regex r in
    Success (Patterns.Group None wr)
  end.