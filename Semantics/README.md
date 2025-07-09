Core definitions: regexes and semantics
=======================================

Files:
- Chars.v: inputs, character descriptors
- ComputeIsTree.v: proof that the functional version of the is_tree predicate produces trees that verify the is_tree predicate
- FunctionalSemantics.v: functional version of the is_tree predicate
- FunctionalUtils.v: utilities related to functional version of is_tree predicate
- Groups.v: group maps
- Parameters.v: a typeclass containing all required parameters (characters, Unicode properties, character sets, two axioms)
- Regex.v: definition of regexes
- Semantics.v: tree semantics
- StrictSuffix.v: definition of when an input is a strict suffix of another, and facts about this
- Tree.v: definition of priority trees, computing all the results and the highest priority result of a tree