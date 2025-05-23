From Linden Require Import Semantics FunctionalSemantics Tree Groups Regex Chars.
From Linden Require Import GroupMapMS MSInput.
From Linden Require Import Utils.
From Warblre Require Import Parameters Notation Base Result.
Import Notation.

Section EquivDef.
  Context `{characterClass: Character.class}.

  (* Groups that we want to forbid from being defined before matching a regex. *)
  Definition forbidden_groups (reg: regex): list group_id :=
    match reg with
    | Quantified _ _ _ _ => nil
    | _ => def_groups reg
    end.

  (* Definition of when a MatcherContinuation performs a given list of actions. *)
  (* A MatcherContinuation mc, working on input string str0 and with the open group list gl,
  performs the actions described in act in the direction dir when: *)
  Definition equiv_cont (mc: MatcherContinuation) (gl: open_groups) (forbgroups: list group_id) (act: actions) (dir: Direction) (str0: string): Prop :=
    forall (gm: group_map) (ms: MatchState) (inp: input) (res: option MatchState) (fuel: nat) (t: tree),
      (* for all corresponding tuples of a MatchState ms, an input inp, a group map gm 
      and a list of open groups gl that use the input string str0, *)
      input_compat inp str0 ->
      equiv_groupmap_ms gm ms -> group_map_equiv_open_groups gm gl ->
      ms_matches_inp ms inp ->
      (* such that gm does not define any of the groups in the forbidden groups, *)
      no_forbidden_groups gm forbgroups ->
      (* if the continuation mc called on ms yields the result res, *)
      mc ms = Success res ->
      (* then letting t be the tree corresponding to the actions in act on the input inp with group map gm and direction dir, *)
      compute_tree act inp gm dir fuel = Some t ->
      (* the first branch of t is equivalent to the result res. *)
      equiv_groupmap_ms_opt (tree_res t gm (idx inp) dir) res.

  (* Definition of when a Matcher recognizes a regex in a given direction. *)
  (* A Matcher m is said to recognize a regex reg in direction dir when: *)
  Definition equiv_matcher (m: Matcher) (reg: regex) (dir: Direction): Prop :=
    (* for any input string str0, *)
    forall (str0: string) (mc: MatcherContinuation) (gl: open_groups) (forbgroups: list group_id) (act: actions),
    (* for any MatcherContinuation mc working with the list of open groups gl on the string str0 performing the actions act, *)
    equiv_cont mc gl forbgroups act dir str0 ->
    (* if the open groups do not contain any of the groups defined by reg, *)
    open_groups_disjoint gl (def_groups reg) ->
    (* and the continuation does not forbid defining any group defined by the regex, *)
    List.Disjoint (def_groups reg) forbgroups ->
    (* plugging the continuation mc into the matcher m yields a continuation that performs the actions Areg reg :: act. *)
    equiv_cont (fun ms => m ms mc) gl (forbidden_groups reg ++ forbgroups) (Areg reg :: act)%list dir str0.

End EquivDef.
