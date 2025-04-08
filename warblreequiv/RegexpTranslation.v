From Warblre Require Import Patterns.
From Linden Require Import Regex CharsWarblre LindenParameters.


Fixpoint to_warblre_regex (r: regex) :=
  match r with
  | Epsilon => Patterns.Empty
  | Character cd => char_descr_to_regex cd
  | Disjunction r1 r2 => Patterns.Disjunction (to_warblre_regex r1) (to_warblre_regex r2)
  | Sequence r1 r2 => Patterns.Seq (to_warblre_regex r1) (to_warblre_regex r2)
  | Star greedy r1 => Patterns.Quantified (to_warblre_regex r1) (if greedy then Patterns.Greedy Patterns.Star else Patterns.Lazy Patterns.Star)
  | Group id r => Patterns.Group None (to_warblre_regex r)
  end.