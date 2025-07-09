Equivalence between Warblre and Linden semantics
================================================

This part of the repository proves the equivalence between [the Warblre semantics](https://github.com/epfl-systemf/Warblre) and the semantics of this repository, for a subset of JavaScript regexes.

# Development structure

The development is organized as follows:

## Theorem files

TODO

## Other important files

- RegexpTranslation.v: defining when a Warblre regex and a Linden regex are equivalent

## Auxiliary files

- CharDescrCharSet.v: equivalence between character descriptors and CharSets
- CharSet.v: Warblre's axiomatized CharSets, but with more axioms
- LindenParameters.v: we instantiate the Warblre typeclasses (https://github.com/epfl-systemf/Warblre/blob/main/mechanization/spec/Parameters.v ) to be able to use the character axiomatization of Linden in Warblre.
- ListLemmas.v, WarblreLemmas.v: lemmas used in proofs
- LKFactorization.v: factorization of lookaround cases of regexp compilation in Warblre
- MSInput.v: linking Warblre MatchStates and Linden inputs
- NumericLemmas.v: lemmas about `non_neg_integer_or_inf` (NoI)
- Tactics.v: custom tactics used in the proofs
- Utils.v: utility lemmas (currently only boolean version of belonging to a list)

