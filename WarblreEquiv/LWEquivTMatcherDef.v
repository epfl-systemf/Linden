From Coq Require Import ZArith List.
From Linden Require Import Chars TMatching Groups Tree LindenParameters.
From Warblre Require Import Notation Result Errors Parameters Base.
Import Notation.

(** * Definition of the equivalence of Matchers and TMatchers *)
(* and of TMatcherContinuations and MatcherContinuations, and of
   TMatchResults and MatchResults *)

Section LWEquivTMatcherDef.
  Context `{characterClass: Character.class}.

  (* Expresses equivalence of a GroupMap.range and a CaptureRange. *)
  Inductive equiv_ranges: GroupMap.range -> CaptureRange -> Prop :=
  | Equiv_ranges:
      forall startIdx endIdx: nat,
      equiv_ranges (GroupMap.Range startIdx (Some endIdx)) (capture_range (Z.of_nat startIdx) (Z.of_nat endIdx)).
  (* Lifting above relation to option *)
  (* We also say that an unclosed group in the Linden sense is equivalent to an undefined range in the Warblre sense. *)
  Inductive equiv_ranges_opt: option GroupMap.range -> option CaptureRange -> Prop :=
  | Equiv_ranges_None: equiv_ranges_opt None None
  | Equiv_ranges_unclosed: forall idx, equiv_ranges_opt (Some (GroupMap.Range idx None)) None
  | Equiv_ranges_Some: forall lrange wrange, equiv_ranges lrange wrange -> equiv_ranges_opt (Some lrange) (Some wrange).
  

  (* A group map and a MatchState are said to be equivalent when they define the same capture groups. *)
  Definition equiv_groupmap_ms (gm: GroupMap.t) (ms: MatchState): Prop :=
    forall gid_prec: nat, equiv_ranges_opt (GroupMap.find (S gid_prec) gm) (List.nth gid_prec (MatchState.captures ms) None).
  (* Lifting above equivalence to option *)
  Inductive equiv_groupmap_ms_opt: option leaf -> option MatchState -> Prop :=
  | Equiv_leaf_ms_None: equiv_groupmap_ms_opt None None
  | Equiv_leaf_ms_Some: forall gm ms, equiv_groupmap_ms gm ms -> equiv_groupmap_ms_opt (Some gm) (Some ms).


  (* Expresses the equivalence between the first branch of a sub-priority tree
     with its corresponding extended match state on the one hand, with a
     MatchResult on the other hand.
     The direction argument is needed to interpret the tree correctly (i.e. to advance the end indices in the right directions).
     This simply unwraps the error monad; we currently do not say anything
     when either match result is an error (any error is equivalent to anything
     in both directions). *)
  Inductive equiv_results: TMatchResult -> GroupMap.t -> nat -> Direction -> MatchResult -> Prop :=
  | Equiv_results:
    forall (t: tree) (gm: GroupMap.t) (idx: nat) (dir: Direction) (wres: option MatchState),
      equiv_groupmap_ms_opt (tree_res t gm idx dir) wres ->
      equiv_results (Success t) gm idx dir (Success wres)
  | Equiv_results_errl:
    forall errl gm idx dir wres, equiv_results (Error errl) gm idx dir wres
  | Equiv_results_errr:
    forall t gm idx dir errr, equiv_results t gm idx dir (Error errr).

  (** * Definition of lists of open groups and equivalence with group maps *)
  (* This is needed to characterize Warblre continuations *)

  (* A list of open groups is a stack of pairs of a group ID and an opening index. *)
  Definition open_groups: Type := list (group_id * nat).

  (* Equivalence with group maps by double inclusion *)
  Definition group_map_equiv_open_groups (gm: GroupMap.t) (gl: open_groups): Prop :=
    forall (gid: group_id) (idx: nat),
      GroupMap.find gid gm = Some (GroupMap.Range idx None) <->
      In (gid, idx) gl.



  (* A continuation is always called at a fixed position in the regexp, so with a
     fixed list of groups that are currently open, as well as a fixed direction.
     We say that a MatcherContinuation mc and a TMatcherContinuation tmc are
     equivalent under a given input string str0, the list of open groups
     gl and direction dir when: *)
  Definition equiv_tree_mcont
    (str0: string) (mc: MatcherContinuation) (tmc: TMatcherContinuation)
    (gl: open_groups) (dir: Direction) :=
    (* for any end index idx, *)
    forall (gm: GroupMap.t) (idx: nat) (ms: MatchState),
    (* for any MatchState ms whose input string is str0 and end index is idx, *)
    MatchState.input ms = str0 ->
    MatchState.endIndex ms = Z.of_nat idx ->
    (* then letting gm be the group map equivalent to the MatchState ms and the open groups gl, *)
    equiv_groupmap_ms gm ms ->
    group_map_equiv_open_groups gm gl ->
    (* the tree returned by the TMatcherContinuation, when interpreted using the group map gm and end index idx, yields a result equivalent to that of the MatcherContinuation. *)
    equiv_results (tmc ms) gm idx dir (mc ms).

  (* A (T)Matcher matches a regexp in some direction, then calls a continuation after matching
     the said regexp.
     We say that a Matcher m and a TMatcher tm of direction dir are equivalent under the input
     string str0 when given equivalent continuations of direction dir, we obtain back equivalent
     continuations of direction dir. Indeed, we never flip the direction of a continuation
     plugged into a Matcher. *)
  Definition equiv_tree_matcher (str0: string) (m: Matcher) (tm: TMatcher) (dir: Direction) :=
    forall mc tmc gl,
      equiv_tree_mcont str0 mc tmc gl dir ->
      equiv_tree_mcont str0 (fun ms => m ms mc) (fun ms => tm ms tmc) gl dir.

End LWEquivTMatcherDef.
