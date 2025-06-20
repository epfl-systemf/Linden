From Linden Require Import Regex Chars.

Section ExampleRegexes.
  Context {char: Parameters.Character.class}.

  Definition fail_regex := Sequence
    (Lookaround NegLookAhead (Character CdDot))
    (Character CdDot).
End ExampleRegexes.