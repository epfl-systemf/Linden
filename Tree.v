Require Import List.
Import ListNotations.

Require Import Regex.

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
      match tree_res t1 gm with
      | None => tree_res t2 gm
      | Some r => Some r
      end
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
  - rewrite IHt1. rewrite IHt2. rewrite hd_error_app. auto.
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
