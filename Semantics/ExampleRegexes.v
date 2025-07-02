From Linden Require Import Regex Chars Parameters.

Section ExampleRegexes.
  Context {params: LindenParameters}.

  Definition fail_regex := Sequence
    (Lookaround NegLookAhead (Character CdDot))
    (Character CdDot).
End ExampleRegexes.