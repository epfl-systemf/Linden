From Coq Require Export List Lia.
From Warblre Require Export Base.
From Linden Require Export Regex Chars Groups Tree Semantics FunctionalSemantics FunctionalUtils ComputeIsTree.
From Linden.Rewriting Require Export Equivalence.

Export ListNotations.
Coercion nat_to_N (n: nat) := NoI.N n.
