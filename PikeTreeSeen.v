(** * Pike Tree Seen Algorithm  *)

(* An algorithm that takes a tree as input, and finds the first match *)
(* Its execution is close to the kind of execution the PikeVM is doing on the bytecode *)
(* It explores multiples ordered branches in parallel, synced with their current input position *)
(* This time, compared to PikeTree, it also records in a "seen" set, *)
(* all the trees it has already started to explore *)
(* Non-deterministically, it can decide not to explore a tree it has already seen *)

Require Import List.
Import ListNotations.

Require Import Regex Chars Groups Tree.
Require Import PikeTree.

(** * Seen Sets  *)
Parameter seentrees: Type.
Parameter initial_seentrees: seentrees.
Parameter add_seentrees: seentrees -> tree -> seentrees.
Parameter inseen : seentrees -> tree -> bool.

(** * Pike Tree Seen Small Step Semantics  *)

(* The semantic states of the PikeTree algorithm *)
Inductive pike_tree_seen_state : Type :=
| PTSS (idx:nat) (active: list (tree * group_map)) (best: option leaf) (blocked: list (tree * group_map)) (seen:seentrees)
| PTSS_final (best: option leaf).


(* Small-step semantics for the PikeTree algorithm *)
Inductive pike_tree_seen_step : pike_tree_seen_state -> pike_tree_seen_state -> Prop :=
| ptss_skip:
(* skip an active tree if it has been seen before *)
(* this is non-deterministic, we can also not skip it by using the other rules *)
  forall idx t gm active best blocked seen
    (SEEN: inseen seen t = true),
    pike_tree_seen_step (PTSS idx ((t,gm)::active) best blocked seen) (PTSS idx active best blocked seen)
| ptss_final:
(* moving to a final state when there are no more active or blocked trees *)
  forall idx best seen,
    pike_tree_seen_step (PTSS idx [] best [] seen) (PTSS_final best)
| ptss_nextchar:
  (* when the list of active trees is empty, restart from the blocked ones, proceeding to the next character *)
  forall idx best blocked tgm seen,
    pike_tree_seen_step (PTSS idx [] best (tgm::blocked) seen) (PTSS (idx + 1) (tgm::blocked) best [] seen)
| ptss_active:
  (* generated new active trees: add them in front of the low-priority ones *)
  forall idx t gm active best blocked nextactive seen1 seen2
    (STEP: tree_bfs_step t gm idx = StepActive nextactive)
    (ADD_SEEN: add_seentrees seen1 t = seen2),
    pike_tree_seen_step (PTSS idx ((t,gm)::active) best blocked seen1) (PTSS idx (nextactive++active) best blocked seen2)
| ptss_match:
  (* a match is found, discard remaining low-priority active trees *)
  forall idx t gm active best blocked seen1 seen2
    (STEP: tree_bfs_step t gm idx = StepMatch)
    (ADD_SEEN: add_seentrees seen1 t = seen2),
    pike_tree_seen_step (PTSS idx ((t,gm)::active) best blocked seen1) (PTSS idx [] (Some gm) blocked seen2)
| ptss_blocked:
(* add the new blocked thread after the previous ones *)
  forall idx t gm active best blocked newt seen1 seen2
    (STEP: tree_bfs_step t gm idx = StepBlocked newt)
    (ADD_SEEN: add_seentrees seen1 t = seen2),
    pike_tree_seen_step (PTSS idx ((t,gm)::active) best blocked seen1) (PTSS idx active best (blocked ++ [(newt,gm)]) seen2).

Definition pike_tree_seen_initial_state (t:tree) : pike_tree_seen_state :=
  (PTSS 0 [(t, empty_group_map)] None [] initial_seentrees).
