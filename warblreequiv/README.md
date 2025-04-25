Equivalence between Warblre and Linden semantics
================================================

This part of the repository proves the equivalence between [the Warblre semantics](https://github.com/epfl-systemf/Warblre) and the semantics of this repository, for a subset of JavaScript regexes.

The proof is done as follows:
- We create analogues of the [compileSubPattern](https://github.com/epfl-systemf/Warblre/blob/c88bceb3dbf4bca1f4c479736822b6ecace518bc/mechanization/spec/Semantics.v#L543) function and its auxiliary functions that return a priority tree instead of a matching result with capture groups. (TMatching.v)
- We prove that the capture groups of the matchers returned by Warblre correspond to the first branch of the trees returned by the corresponding tree matchers. (LWEquivTMatcher.v)
- We finally prove that the trees produced by the tree matchers respect the semantics set out in this repository. (LWEquivTree.v)

# Development structure

The development is organized as follows:

## Theorem files

- LWEquivTMatcher.v: first part of the proof, where we prove that a Matcher and its corresponding tree matcher yield equivalent results, in the sense that the capture groups returned by the Matcher are the same as those resulting from the interpretation of the tree returned by the tree matcher.
  - LWEquivTMatcherDef.v: definition of tree matchers, tree matcher continuations and tree match results, and definition of the equivalence of Matchers and tree matchers
  - LWEquivTMatcherLemmas.v: lemmas used (exclusively) for proving the theorems in this part

- LWEquivTree.v: second part of the proof, where we prove that the trees returned by the tree matchers follow the semantics set out in this repository.
  - LWEquivTreeLemmas.v: lemmas used (exclusively) for proving the theorems in this part
  
- LWEquivFrontend.v: an end-to-end theorem expressing that for any regex and input, the two semantics yield the same results.

## Other important files

- TMatching.v: defining the tree matchers (adaptation of the Warblre semantics)
- RegexpTranslation.v: defining when a Warblre regex and a Linden regex are equivalent
- TreeMSInterp.v: defining the first branch of a Linden tree, but using an extended Warblre MatchState instead of the axiomatized group maps defined in this repository

## Auxiliary files

- LindenParameters.v: we instantiate the Warblre typeclasses (https://github.com/epfl-systemf/Warblre/blob/main/mechanization/spec/Parameters.v ) to be able to use the character axiomatization of Linden in Warblre.
- ListLemmas.v, WarblreLemmas.v: lemmas used in proofs
- MSInput.v: linking Warblre MatchStates and Linden inputs
- Tactics.v: custom tactics used in the proofs
