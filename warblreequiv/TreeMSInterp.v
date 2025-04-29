From Coq Require Import List ZArith.
Import ListNotations.
From Warblre Require Import Notation Result Base.
Import Notation.
From Linden Require Import Groups Tree MSInput LindenParameters Regex.

(** * Interpretation of Linden trees using extended Warblre MatchStates instead of Linden group maps *)


(* Reset the given groups (indexed from 1) in the given MatchState *)
Definition reset_groups_ms {F H} `{CharacterMarker H} `{Result.AssertionError F} (gidl: list Groups.group_id) (s: MatchState): MatchState :=
  let '(match_state inp endInd cap) := s in
  let cap' := match List.List.Update.Nat.Batch.update None cap (List.map (fun x => x-1) gidl) with
    | Success cap' => cap'
    | Error _ => cap
  end in
  (match_state inp endInd cap').

(* A list of currently open groups, with for each of them their ID and the position at which they were opened.
   This is needed because we want to be able to express the result of the first branch of a sub-backtracking tree,
   which can close groups that are not opened within this tree and whose opening indices the Matchers and TMatchers
   do not record in the MatchStates passed to subsequent calls.
   *An extended match state is a MatchState with a list of open groups with indices.* It allows to model the capture
   of group opening indices in continuations. *)
Definition open_groups := list (Groups.group_id * integer).


(* Close group id opened in gl at index end_index. If group id was indeed open, returns the new list of open groups
   (where the closed group has been removed) and the capture range of the closed group.
   Otherwise, return a dummy CaptureRange and the original list of open groups. *)
Fixpoint close_group (id: Groups.group_id) (gl: open_groups) end_index: CaptureRange * open_groups :=
  match gl with
  | nil => (capture_range (-1)%Z (-1)%Z, nil)
  | (id', start)::q =>
    if id == id' then
      (capture_range start end_index, q)
    else
      let (range, q') := close_group id q end_index in
      (range, (id', start)::q')
  end.

(* TODO Direction *)
(* Apply the given group action to the extended match state composed of a MatchState and a list of open groups with
   opening indices.
   If we try to close a nonexisting group or clear nonexisting capture ranges, do nothing. *)
Definition group_effect' {F H} `{CharacterMarker H} `{Result.AssertionError F} (g: groupaction) (s: MatchState) (gl: open_groups): MatchState * open_groups :=
  match g with
  | Open gid =>
      (s, (gid, MatchState.endIndex s)::gl)
  | Close gid =>
      let cap := MatchState.captures s in
      let (range, gl') := close_group gid gl (MatchState.endIndex s) in
      let cap' := match Base.update cap gid (Some range) with
        | Success cap' => cap'
        | Error _ => cap
        end
      in
      (match_state (MatchState.input s) (MatchState.endIndex s) cap', gl')
  | Reset gidl =>
      let s' := reset_groups_ms gidl s in
      (s', gl)
  end.

(* We represent a call mc ms to some MatcherContinuation mc with match state ms as a sub-backtracking tree
   together with the match state ms and a list of groups that are open at that stage of matching. *)

(* TODO Direction *)
(* Given a sub-backtracking tree and an extended match state, retrieve the highest priority result represented
   by the subtree. *)
Fixpoint tree_res' {F} `{Result.AssertionError F} (t:tree) (s: MatchState) (gl: open_groups): option MatchState :=
  match t with
  | Mismatch => None
  | Match => Some s
  | Choice t1 t2 =>
      let res1 := tree_res' t1 s gl in
      match res1 with
      | None => tree_res' t2 s gl
      | Some _ => res1
      end
  | Read c t1 =>
    tree_res' t1 (advance_ms s) gl
  | CheckFail _ => None
  | CheckPass _ t1 => tree_res' t1 s gl
  | GroupAction g t1 => 
      let (s', gl') := group_effect' g s gl in tree_res' t1 s' gl'
  | LK lk tlk t =>
      match positivity lk with
      | true =>
          match tree_res' tlk s gl with
          | Some mslk =>
              (* using the captures defined in the first branch of the lookahead; the open groups remain unchanged because the lookaround is well-parenthesized *)
              tree_res' t (match_state (MatchState.input s) (MatchState.endIndex s) (MatchState.captures mslk)) gl
          | None => None
          end
      | false => match tree_res' tlk s gl with
          (* using previous captures *)
          | Some _ => None
          | None => tree_res' t s gl
          end
      end
  | LKFail _ _ => None
  end.
