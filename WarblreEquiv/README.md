Equivalence between Warblre and Linden semantics
================================================

This part of the repository proves the equivalence between [the Warblre semantics](https://github.com/epfl-systemf/Warblre) and the semantics of this repository, for all valid JavaScript regexes.

# Development structure

The development is organized as follows:

## Theorem files

- Equiv.v: core equivalence proof
- EquivDef.v: equivalence definitions
- EquivMain.v: main equivalence theorems
- EquivLemmas.v: lemmas used in equivalence proof

## Other important files

- RegexpTranslation.v: defining when a Warblre regex and a Linden regex are equivalent, translating Warblre regexes into Linden regexes

## Auxiliary files

- CharDescrCharSet.v: equivalence between character descriptors and CharSets
- CharSet.v: Warblre's axiomatized CharSets, but with more axioms
- GroupMapLemmas.v: lemmas about group maps
- GroupMapMS.v: equivalence between Linden group maps and Warblre MatchStates (and lists of open groups)
- ListLemmas.v, WarblreLemmas.v: lemmas used in proofs
- LKFactorization.v: factorization of lookaround cases of regexp compilation in Warblre
- LWParameters.v: instantiation of all Warblre typeclasses (https://github.com/epfl-systemf/Warblre/blob/main/mechanization/spec/Parameters.v ) except Character and UnicodeProperty
- MSInput.v: linking Warblre MatchStates and Linden inputs
- NumericLemmas.v: lemmas about `non_neg_integer_or_inf` (NoI)
- ResultTranslation.v: going back from a Linden result to a Warblre result
- Tactics.v: custom tactics used in the proofs
- Utils.v: utility lemmas (currently only boolean version of belonging to a list)

