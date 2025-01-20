Require Import List.
Import ListNotations.

Require Import Regex.

(** * Chaining optional results  *)
Definition seqop {X:Type} (o1 o2: option X) : option X :=
  match o1 with Some o => o1 | None => o2 end.

Lemma seqop_none:
  forall X (o1:option X), seqop o1 None = o1.
Proof. intros X o1. destruct o1 eqn:O; auto. Qed.

Definition seqop_list {X Y:Type} (l:list X) (f: X -> option Y) : option Y :=
  List.fold_left (fun (y:option Y) (x:X) => seqop y (f x)) l None.

Lemma app_cons:
  forall X (h:X) l, h::l = [h] ++ l.
Proof. intros. simpl. auto. Qed.

Lemma seqop_some:
  forall X Y l f r, List.fold_left (fun (y:option Y) (x:X) => seqop y (f x)) l (Some r) = Some r.
Proof. intros X Y l. induction l; intros; simpl; auto. Qed.


Lemma seqop_list_head_some:
  forall X Y (h:X) l f (r:Y),
    f h = Some r -> 
    seqop_list (h::l) f = Some r.
Proof.
  intros X Y h l f r H. unfold seqop_list.
  rewrite app_cons. rewrite fold_left_app.
  simpl. rewrite H. rewrite seqop_some. auto.
Qed.

Lemma seqop_list_head_none:
  forall X Y (h:X) l (f:X -> option Y),
    f h = None -> 
    seqop_list (h::l) f = seqop_list l f.
Proof. intros. unfold seqop_list. simpl. rewrite H. auto. Qed.


(** * Priority Trees  *)

Inductive tree : Type :=
| Mismatch
| Match (i:input)
| Choice (t1 t2:tree)
| Read (c:Char) (t:tree)
| CheckFail (str:string) (* failed to make progress wrt some string *)
| CheckPass (str:string) (t:tree)
| OpenGroup (g:group_id) (t:tree)
| CloseGroup (g:group_id) (t:tree)
| ResetGroups (gl:list group_id) (t:tree) (* for capture reset *)
.

(** * Greedy and Lazy Choice *)

(* a choice operator which depends on the greediness of some quantifier *)
Definition greedy_choice (greedy:bool) (t1 t2:tree) :=
  if greedy
  then Choice t1 t2
  else Choice t2 t1.

(** * Tree Results  *)

Definition leaf: Type := (input * group_map).

(* returning the highest-priority result *)
(* we also return the corresponding group map *)
Fixpoint tree_res (t:tree) (gm:group_map): option leaf :=
  match t with
  | Mismatch => None
  | Match s => Some (s, gm)
  | Choice t1 t2 =>
      seqop (tree_res t1 gm) (tree_res t2 gm)
  | Read c t1 => tree_res t1 (add_char gm c)
  | CheckFail _ => None
  | CheckPass _ t1 => tree_res t1 gm
  | OpenGroup id t1 => tree_res t1 (open_group gm id)
  | CloseGroup id t1 => tree_res t1 (close_group gm id)
  | ResetGroups idl t1 => tree_res t1 (reset_groups gm idl)
  end.

(* initializing on a the empty group map *)
Definition first_branch (t:tree) : option leaf :=
  tree_res t empty_group_map.

(** * All Tree Results *)

(* returns the ordered list of all results of a tree *)
(* together with the corresponding group map *)
Fixpoint tree_leaves (t:tree) (gm:group_map): list leaf :=
  match t with
  | Mismatch => []
  | Match s => [(s,gm)]
  | Choice t1 t2 =>
      tree_leaves t1 gm ++ tree_leaves t2 gm
  | Read c t1 => tree_leaves t1 (add_char gm c)
  | CheckFail _ => []
  | CheckPass _ t1 => tree_leaves t1 gm
  | OpenGroup id t1 => tree_leaves t1 (open_group gm id)
  | CloseGroup id t1 => tree_leaves t1 (close_group gm id)
  | ResetGroups idl t1 => tree_leaves t1 (reset_groups gm idl)
  end.

(* intermediate lemma about hd_error *)
Lemma hd_error_app:
  forall A (l1 l2:list A),
    hd_error (l1 ++ l2) =
      match (hd_error l1) with
      | Some h => Some h
      | None => hd_error l2
      end.
Proof.
  intros A l1 l2. induction l1; simpl; auto.
Qed.


(* this definition coincides on the first element with the previous definition *)
Theorem first_tree_leaf:
  forall t gm,
    tree_res t gm = hd_error (tree_leaves t gm).
Proof.
  intros t. induction t; intros; simpl; auto.
  - rewrite IHt1. rewrite IHt2. rewrite hd_error_app. unfold seqop.
    destruct (hd_error (tree_leaves t1 gm)) eqn:HD; auto. 
Qed.
      
(** * Group Map irrelevance  *)
(* finding a match does not depend on the initial group map *)
(* we could phrase a stronger theorem about how to relate the two results *)
(* but for no I only need to differentiate when there is no results from when there is one *)

(* warning: actually so far I don't need this theorem *)

Lemma leaves_group_map_indep:
  forall t gm1 gm2,
    tree_leaves t gm1 = [] -> tree_leaves t gm2 = [].
Proof.
  intros t.
  induction t; intros; simpl; auto;
    simpl in H; try solve[inversion H];
    try solve[eapply IHt in H; eauto].
  - apply app_eq_nil in H as [NIL1 NIL2].
    apply IHt1 with (gm2:=gm2) in NIL1. apply IHt2 with (gm2:=gm2) in NIL2.
    rewrite NIL1. rewrite NIL2. auto.
Qed.





(** * Tree BFS  *)
(* Close to the kind of execution the PikeVM is doing on the bytecode *)

(* returns three things:
 - the list of active trees to explore next. can be empty. Each has its own group map
 - option leaf: a result found
 - option tree: if the tree is blocked consuming a character *)

Inductive step_result : Type :=
| StepActive: list (tree * group_map) -> step_result (* generated new active threads, possibly 0 *)
| StepMatch: leaf -> step_result                (* a match was found *)
| StepBlocked: tree -> step_result     (* the thread was blocked *)
.

Definition StepDead := StepActive []. (* the thread died *)

Definition tree_bfs_step (t:tree) (gm:group_map): step_result :=
  match t with
  | Mismatch => StepDead
  | Match i => StepMatch (i, gm)
  | Choice t1 t2 => StepActive [(t1,gm); (t2,gm)]
  | Read c t1 => StepBlocked t1
  | CheckFail _ => StepDead
  | CheckPass _ t1 => StepActive [(t1,gm)]
  | OpenGroup gid t1 => StepActive [(t1,open_group gm gid)]
  | CloseGroup gid t1 => StepActive [(t1, close_group gm gid)]
  | ResetGroups gid t1 => StepActive [(t1, reset_groups gm gid)]
  end.

Definition pike_tree_state : Type :=
  (* active, bestmatch, blocked *)
  list (tree * group_map) * option leaf * list (tree * group_map).

Definition upd_blocked {X:Type} (newblocked: option X) (blocked: list X) :=
  match newblocked with Some b => b::blocked | None => blocked end.

Inductive pike_tree_step : pike_tree_state -> pike_tree_state -> Prop :=
| pts_nextchar:
  (* when the list of active trees is empty, restart from the blocked ones, proceeding to the next character *)
  forall best blocked,
    pike_tree_step ([], best, blocked) (blocked, best, [])
| pts_active:
  (* generated new active trees: add them in front of the low-priority ones *)
  forall t gm active best blocked nextactive
    (STEP: tree_bfs_step t gm = StepActive nextactive),
    pike_tree_step ((t,gm)::active, best, blocked) (nextactive++active, best, blocked)
| pts_match:
  (* a match is found, discard remaining low-priority active trees *)
  forall t gm active best blocked leaf
    (STEP: tree_bfs_step t gm = StepMatch leaf),
    pike_tree_step ((t,gm)::active, best, blocked) ([], Some leaf, blocked)
| pts_blocked:
(* add the new blocked thread after the previous ones *)
  forall t gm active best blocked newt
    (STEP: tree_bfs_step t gm = StepBlocked newt),
    pike_tree_step ((t,gm)::active, best, blocked) (active, best, blocked ++ [(newt,gm)]).

Definition pike_tree_initial_state (t:tree) : pike_tree_state :=
  ([(t, empty_group_map)], None, []).

(** * Tree BFS Correction *)

Definition list_result (l:list (tree * group_map)) : option leaf :=
  seqop_list l (fun tgm => tree_res (fst tgm) (snd tgm)).
      
Lemma list_result_cons:
  forall t gm l,
    list_result ((t,gm)::l) = seqop (tree_res t gm) (list_result l).
Proof.
  intros. unfold list_result, seqop_list. simpl.
Admitted.

Lemma list_result_app:
  forall l1 l2,
    list_result (l1 ++ l2) = seqop (list_result l1) (list_result l2).
Proof.
Admitted.

(* first, see if there is a result in blocked, then active, then take the best *)
Definition state_result (pts: pike_tree_state) : option leaf :=
  match pts with
  | (active, best, blocked) =>
      seqop (list_result blocked) (seqop (list_result active) best)
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
  - destruct t; simpl in STEP; inversion STEP; subst.
    + rewrite app_nil_l. unfold state_result. apply f_equal. unfold list_result. rewrite seqop_list_head_none; auto.
    + unfold state_result. apply f_equal. apply f_equal2; auto.
    + rewrite app_nil_l. unfold state_result. apply f_equal. unfold list_result. rewrite seqop_list_head_none; auto.
    + unfold state_result. apply f_equal. rewrite list_result_cons. simpl. rewrite list_result_cons. auto.
    + unfold state_result. apply f_equal. rewrite list_result_cons. simpl. rewrite list_result_cons. auto.
    + unfold state_result. apply f_equal. rewrite list_result_cons. simpl. rewrite list_result_cons. auto.      
    + unfold state_result. apply f_equal. rewrite list_result_cons. simpl. rewrite list_result_cons. auto.
  - destruct t; simpl in STEP; inversion STEP; subst.
    simpl. apply f_equal. rewrite list_result_cons. auto.
  - destruct t; simpl in STEP; inversion STEP; subst.
    simpl. rewrite list_result_app. rewrite list_result_cons. simpl.
    admit.                      (* an issue with group map that must (or not? if we change group maps) change *)
Admitted.

(* the invariant is properly initialized: at the beginning, the result of the state is the first result of the tree *)
Lemma pts_result_init:
  forall t,
    state_result (pike_tree_initial_state t) = first_branch t.
Proof.
  intros t. unfold pike_tree_initial_state, first_branch. simpl.
  unfold list_result, seqop_list. simpl. rewrite seqop_none. auto.
Qed.
