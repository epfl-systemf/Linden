From Linden Require Import Semantics Tree Groups Regex Chars.
From Linden Require Import GroupMapMS MSInput.
From Warblre Require Import Parameters Notation Base Result.
Import Notation.

Section EquivDef.
  Context `{characterClass: Character.class}.

  (* Definition of when a MatcherContinuation performs a given list of actions. *)
  (* A MatcherContinuation mc, working on input string str0 and with the open group list gl,
  performs the actions described in act in the direction dir when: *)
  Definition equiv_cont (mc: MatcherContinuation) (gl: open_groups) (act: actions) (dir: Direction) (str0: string): Prop :=
    forall (gm: group_map) (ms: MatchState) (inp: input) (res: option MatchState) (fuel: nat) (t: tree),
      (* for all corresponding tuples of a MatchState ms, an input inp, a group map gm 
      and a list of open groups gl that use the input string str0, *)
      input_compat inp str0 ->
      equiv_groupmap_ms gm ms -> group_map_equiv_open_groups gm gl ->
      ms_matches_inp ms inp ->
      (* if the continuation mc called on ms yields the result res, *)
      mc ms = Success res ->
      (* then letting t be the tree corresponding to the actions in act on the input inp with group map gm and direction dir, *)
      compute_tree' act inp gm dir fuel = Some t ->
      (* the first branch of t is equivalent to the result res. *)
      equiv_groupmap_ms_opt (tree_res t gm (idx inp) dir) res.

  Definition equiv_matcher (m: Matcher) (reg: regex) (dir: Direction): Prop :=
    forall (str0: string) (mc: MatcherContinuation) (gl: open_groups) (act: actions),
    equiv_cont mc gl act dir str0 ->
    open_groups_disjoint gl (def_groups reg) ->
    equiv_cont (fun ms => m ms mc) gl (Areg reg :: act)%list dir str0.

End EquivDef.
