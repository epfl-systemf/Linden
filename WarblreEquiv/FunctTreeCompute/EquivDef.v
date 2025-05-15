From Linden Require Import Semantics Tree Groups Regex Chars.
From Linden Require Import GroupMapMS MSInput.
From Warblre Require Import Parameters Notation Base Result.
Import Notation.

Section EquivDef.
  Context `{characterClass: Character.class}.

  Definition equiv_cont (mc: MatcherContinuation) (gl: open_groups) (act: actions) (dir: Direction): Prop :=
    forall (gm: group_map) (ms: MatchState) (inp: input) (res: option MatchState) (t: tree),
      equiv_groupmap_ms gm ms -> group_map_equiv_open_groups gm gl ->
      ms_matches_inp ms inp ->
      mc ms = Success res ->
      compute_tree act inp gm dir = Some t ->
      equiv_groupmap_ms_opt (tree_res t gm (idx inp) dir) res.

  Definition equiv_matcher (m: Matcher) (reg: regex) (dir: Direction): Prop :=
    forall (mc: MatcherContinuation) (gl: open_groups) (act: actions),
    equiv_cont mc gl act dir ->
    open_groups_disjoint gl (def_groups reg) ->
    equiv_cont (fun ms => m ms mc) gl (Areg reg :: act)%list dir.

End EquivDef.
