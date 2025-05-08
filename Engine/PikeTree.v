(** * Pike Tree Algorithm  *)

(* An algorithm that takes a tree as input, and finds the first match *)
(* Its execution is close to the kind of execution the PikeVM is doing on the bytecode *)
(* It explores multiples ordered branches in parallel, synced with their current input position *)

Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Groups Tree.

(** * Pike Tree Small Step Semantics  *)

(* returns three things:
 - the list of active trees to explore next. can be empty. Each has its own group map
 - option leaf: a result found
 - option tree: if the tree is blocked consuming a character *)

Inductive step_result : Type :=
| StepActive: list (tree * group_map) -> step_result (* generated new active threads, possibly 0 *)
| StepMatch: step_result                (* a match was found *)
| StepBlocked: tree -> step_result     (* the thread was blocked *)
.

Definition StepDead := StepActive []. (* the thread died *)

(* this corresponds to an atomic step of a single tree *)
Definition tree_bfs_step (t:tree) (gm:group_map) (idx:nat): step_result :=
  match t with
  | Mismatch => StepDead
  | Match => StepMatch
  | Choice t1 t2 => StepActive [(t1,gm); (t2,gm)]
  | Read c t1 => StepBlocked t1
  | CheckFail _ => StepDead
  | CheckPass _ t1 => StepActive [(t1,gm)]
  | GroupAction a t1 => StepActive [(t1, group_effect a gm idx)]
  end.

(* The semantic states of the PikeTree algorithm *)
Inductive pike_tree_state : Type :=
| PTS (idx:nat) (active: list (tree * group_map)) (best: option leaf) (blocked: list (tree * group_map))
| PTS_final (best: option leaf).

Definition upd_blocked {X:Type} (newblocked: option X) (blocked: list X) :=
  match newblocked with Some b => b::blocked | None => blocked end.

(* Small-step semantics for the PikeTree algorithm *)
Inductive pike_tree_step : pike_tree_state -> pike_tree_state -> Prop :=
| pts_final:
(* moving to a final state when there are no more active or blocked trees *)
  forall idx best,
    pike_tree_step (PTS idx [] best []) (PTS_final best)
| pts_nextchar:
  (* when the list of active trees is empty, restart from the blocked ones, proceeding to the next character *)
  forall idx best blocked tgm,
    pike_tree_step (PTS idx [] best (tgm::blocked)) (PTS (idx + 1) (tgm::blocked) best [])
| pts_active:
  (* generated new active trees: add them in front of the low-priority ones *)
  forall idx t gm active best blocked nextactive
    (STEP: tree_bfs_step t gm idx = StepActive nextactive),
    pike_tree_step (PTS idx ((t,gm)::active) best blocked) (PTS idx (nextactive++active) best blocked)
| pts_match:
  (* a match is found, discard remaining low-priority active trees *)
  forall idx t gm active best blocked
    (STEP: tree_bfs_step t gm idx = StepMatch),
    pike_tree_step (PTS idx ((t,gm)::active) best blocked) (PTS idx [] (Some gm) blocked)
| pts_blocked:
(* add the new blocked thread after the previous ones *)
  forall idx t gm active best blocked newt
    (STEP: tree_bfs_step t gm idx = StepBlocked newt),
    pike_tree_step (PTS idx ((t,gm)::active) best blocked) (PTS idx active best (blocked ++ [(newt,gm)])).

Definition pike_tree_initial_state (t:tree) : pike_tree_state :=
  (PTS 0 [(t, empty_group_map)] None []).


(** * Pike Tree Properties  *)

Theorem pike_tree_determinism:
  forall ptso pts1 pts2
    (STEP1: pike_tree_step ptso pts1)
    (STEP2: pike_tree_step ptso pts2),
    pts1 = pts2.
Proof.
  intros ptso pts1 pts2 STEP1 STEP2. inversion STEP1; subst.
  - inversion STEP2; subst; auto.
  - inversion STEP2; subst; auto.
  - inversion STEP2; rewrite STEP in STEP0; inversion STEP0; subst; auto.
  - inversion STEP2; rewrite STEP in STEP0; inversion STEP0; subst; auto.
  - inversion STEP2; rewrite STEP in STEP0; inversion STEP0; subst; auto.
Qed.

(** * Pike Tree Correction *)
(* we show it's related to the baktracking exploration of the tree *)

Definition list_result (l:list (tree * group_map)) (idx:nat) : option leaf :=
  seqop_list l (fun tgm => tree_res (fst tgm) (snd tgm) idx).

Lemma list_result_cons:
  forall t gm l idx,
    list_result ((t,gm)::l) idx = seqop (tree_res t gm idx) (list_result l idx).
Proof.
  intros. unfold list_result. destruct (tree_res t gm idx) eqn:RES.
  - erewrite seqop_list_head_some; simpl; eauto.
  - erewrite seqop_list_head_none; simpl; eauto.
Qed.

Lemma list_result_app:
  forall l1 l2 idx,
    list_result (l1 ++ l2) idx = seqop (list_result l1 idx) (list_result l2 idx).
Proof.
  intros l1. induction l1; intros; auto.
  destruct a as [t gm]. unfold list_result.
  destruct (tree_res t gm idx) eqn:RES.
  - erewrite seqop_list_head_some; simpl; eauto.
    erewrite seqop_list_head_some; simpl; eauto.
  - erewrite seqop_list_head_none; simpl; eauto.
    erewrite seqop_list_head_none; simpl; eauto.
Qed.  

(* first, see if there is a result in blocked, then active, then take the best *)
(* this is an invariant: after each step, the state result is preserved *)
Definition state_result (pts: pike_tree_state) : option leaf :=
  match pts with
  | (PTS idx active best blocked) =>
      seqop (list_result blocked (idx+1)) (seqop (list_result active idx) best)
  | (PTS_final best) => best
  end.
  

(* the state result is an invariant of the pike step *)
Theorem pts_result_preservation:
  forall pts1 pts2,
    pike_tree_step pts1 pts2 ->
    state_result pts1 = state_result pts2.
Proof.
  intros pts1 pts2 H.
  inversion H; subst.
  - simpl. auto.
  - simpl. auto.
  - destruct t; simpl in STEP; inversion STEP; subst.
    + rewrite app_nil_l. unfold state_result. apply f_equal. unfold list_result. rewrite seqop_list_head_none; auto.
    + unfold state_result. apply f_equal. apply f_equal2; auto.
    + rewrite app_nil_l. unfold state_result. apply f_equal. unfold list_result. rewrite seqop_list_head_none; auto.
    + unfold state_result. apply f_equal. rewrite list_result_cons. simpl. rewrite list_result_cons. auto.
    + unfold state_result. apply f_equal. rewrite list_result_cons. simpl. rewrite list_result_cons. auto.
  - destruct t; simpl in STEP; inversion STEP; subst.
    simpl. apply f_equal. rewrite list_result_cons. auto.
  - destruct t; simpl in STEP; inversion STEP; subst.
    simpl. rewrite list_result_app. rewrite list_result_cons. simpl.
    rewrite <- seqop_assoc with (o3:=best). rewrite seqop_assoc. apply f_equal. auto.
Qed.

(* the invariant is properly initialized: at the beginning, the result of the state is the first result of the tree *)
Lemma pts_result_init:
  forall t,
    state_result (pike_tree_initial_state t) = first_branch t.
Proof.
  intros t. unfold pike_tree_initial_state, first_branch. simpl.
  unfold list_result, seqop_list. simpl. rewrite seqop_none. auto.
Qed.
