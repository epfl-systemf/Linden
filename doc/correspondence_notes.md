The file `correspondence_table.pdf` provides a correspondence between the paper definitions and their Rocq counterparts.

# Notes on the correspondence table

Some simplifications were made in the paper compared to the Rocq development to improve readability and understandability. This file describes the simplifications and in general all non-exact correspondences between the paper and the Rocq development.

- Figure 3, `Semantics/Tree.v`, `tree`:
  - BackrefPass in the paper corresponds to `ReadBackRef` in the code.
  - The constructors Open, Close and Reset in the paper are grouped in one constructor GroupAction which takes a parameter of type `groupaction`. This type is defined in `Semantics/Groups.v`.
  - LKMismatch in the paper corresponds to `LKFail` in the code.
- Figure 4, `Semantics/Semantics.v`, `is_tree`:
  - Rule Read in the paper corresponds to constructor `tree_char` in the code.
  - The rules SeqForward and SeqBackward in the paper are merged into one constructor (`tree_sequence`) in the code. The function `seq_list` distinguishes the two directions.
  - The rules Greedy and Lazy in the paper are merged into one constructor (`tree_quant_free`) in the code. The function `greedy_choice` distinguishes the greedy case from the lazy case.
- worst(lk, i), `Semantics/FunctionalSemantics.v`, `worst_input`: worst_input takes a direction instead of a lookaround type in the code
- ⇃r_w⇂, `WarblreEquiv/RegexpTranslation.v`, `warblre_to_linden`: the Rocq function takes more arguments than just a regex, namely a group index and a name map. The group index is used to indicate the number of left capturing parentheses before the current regex, whereas the name map stores the correspondence between group names and group IDs.
- ↿res↾, `WarblreEquiv/ResultTranslation.v`, `to_MatchState`: the Rocq function takes a number of groups as well, to be able to create a capture list with the right number of capture groups.
- Theorem 4, `WarblreEquiv/EquivMain.v`, `equiv_main_reconstruct`: the Rocq theorem takes into account the two previous points, specifying group index 0 and the right name map for `warblre_to_linden` and the right number of capture groups for `to_MatchState`.
- Sometimes, for convenience, we don't use ⇃r_w⇂ to refer to the Linden version of Warblre regex r_w, but instead use an inductive syntactic equivalence relation $r_w \sim r_l$. For instance, the intermediate lemma of Section 4 does not relate to $r_w$ but to an equivalent regex.  
We proved that the lowering function ⇃r_w⇂ verifies $r_w \sim \downharpoonleft r_w \downharpoonright$ ([../WarblreEquiv/RegexpTranslation.v](WarblreEquiv/RegexpTranslation.v), theorem `warblre_to_linden_sound_root`).
- Regex equivalence (rewriting) is defined in terms of the is_tree predicate, not in terms of compute_tree or compute_tr; the two are equivalent (theorem `tree_equiv_compute_dir_iff` in [../Rewriting/Equivalence.v](Rewriting/Equivalence.v)).
- Quantifier merging: we didn't prove the theorems relating to quantifiers of the form {0, Δ, p} with both p = ⊤ and p = ⊥. Instead we argue that the missing theorems are immediate corollaries of the proved theorems and forced_equiv.
- Figure 10, `Engine/NFA.v`, `bytecode`:
  - Jump in the paper corresponds to Jmp in the code.
  - RegOpen in the paper corresponds to SetRegOpen in the code.
  - RegClose in the paper corresponds to SetRegClose in the code.
  - KillThread in the code is an instruction that kills a thread when it corresponds to a feature that is not supported by PikeVM.
- Figure 11, `Engine/NFA.v`, `compile`:
  - The Rocq function has an extra argument, `fresh`, to get fresh labels.
  - The two cases for quantifiers (greedy and lazy) are combined into one match case, thanks to the `greedy_fork` function that generates the right `Fork` instruction corresponding to the greediness of the quantifier.
  - Unsupported regexes are compiled into the `KillThread` instruction.
- invariant_preservation: we need as a hyothesis that the code is well-formed (`(STWF: stutter_wf code)`); we have proved that this is the case for any compiled code ([../Engine/PikeEquiv.v](Engine/PikeEquiv.v), theorem `compilation_stutter_wf`).
