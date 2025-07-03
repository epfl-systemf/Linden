From Linden Require Import Regex Chars Parameters.

Section ExampleRegexes.
  Context {params: LindenParameters}.

  (* TODO Possibly broken *)
  Definition fail_regex := Sequence
    (Lookaround NegLookAhead (Character CdDot))
    (Character CdDot).
End ExampleRegexes.