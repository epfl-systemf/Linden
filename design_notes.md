# What should be recorded in the tree?

The backtrackng tree holds some information (characters that have been read, the exact type of anchor that has been read...), but not everything we could record.
For instance, the `tree` type itself does not contain the current state of the input, the character descriptor that was used, the index of the backreference...

Here, we list a few reasons for chosing what information sould or should not be recorded in the tree.
In some cases, it does not matter much.
In some cases, some superfluous information (like the exact character that was matched) is recorded so that the trees in the development correspond exactly to the trees given as examples in the paper. For the characters read, it makes it easier to understand which branch of the tree correspond to which part of the regex.

## Progress checks
In the `Progress` nodes of the tree, we do not record the input at the time the progress check was issued.
In the `is_tree` semantics, the `action` that corresponds to a progress check does record that input: it is then used in rule `tree_check` to make sure some progress has been done: we could then also record it in the tree.

But not recording it has an advantage for proving automata-based engines:
two threads at the same NFA state and with the same input position will correspond to the exact same tree, regardless of how they arrived in that state.
In other words, the backtracking tree correspondig to a thread is entirely determined by the NFA state, the progress boolean and the input position.

For instance, in the regex (a|aa)* on the string "aa".
At position 2 in the string, there are two threads that reach the end of the quantifier at the same time.
One has done two iterations, and will now pass the progress check that was generated at position 1.
Another has done a single iteration, and will now pass the progress check that was generated at position 0.
Without the string in the tree, these two threads correspond to the exact same tree.

## Mismatch nodes
We could have diferent mismatch nodes in the tree: one for a failed anchor, one for a failed read...
We can simplify multiple functions that manipulate trees by simply having a single Mismatch node.

There is one exception for failed lookarounds, `LKFail`.
We expect that always recording the tree of the lookaround (successful or not), could lead to better invariants when proving the correctness of a linear-time lookaround algorithm that computes a table of positions where the lookarounds hold, but this proof remains to be done.

## String/Group map in the tree
Our current `tree` type does not record the current string at each node in the tree. Similarly, it does not compute the current `group_map`.
Recording the current string and group map could facilitate the function `tree_leaves` that computes the leaves: we could simply read what leaf is at the `Match` nodes, without stepping through the input.
But so far, other definitions and proofs do not require this extra information, and trees are simpler without it.


# Progress Check Semantic Rules

In the rule `tree_check` of `is_tree` semantics, we require that the current input is a strict suffix of the input at which the progress check was issued.
An alternative way would be to require the two inputs to be different, but not necessarily a strict suffix.

This current strict suffix definition allows for an easier definition of the fuel for the functional version of the semantics, `compute_tree`. If we know that a successful progress is a strict suffix, then we can know for sure that in the worst case it is equal to the next input after the original input, and the fuel definition, `actions_fuel` relies on that observation.
