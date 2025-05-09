Linden
======

# Repository structure

Files at the root:
- Chars.v: characters, character descriptors, strings
- Groups.v: axiomatized group maps
- NumericLemmas.v: lemmas about `non_neg_integer_or_inf` (NoI)
- Regex.v: definition of regexes
- Semantics.v: tree semantics
- Tree.v: definition of priority trees, computing the highest priority result of a tree using axiomatized group maps
- Utils.v: utility lemmas (currently only boolean version of belonging to a list)

Folders:
- Engine: formalization and proofs of matching engines (PikeVM, NFA simulation)
- warblreequiv: proof of equivalence of semantics with the Warblre semantics

For a description of the files inside the folders, see the README.md files in these folders.
