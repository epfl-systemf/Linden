From Linden Require Import Regex Chars.

Section ExampleRegexes.
  Context {char: Parameters.Character.class}.
  Context {unicodeProp: Parameters.Property.class Parameters.Character}.

  Definition fail_regex := Sequence
    (Lookaround NegLookAhead (Character CdDot))
    (Character CdDot).
End ExampleRegexes.