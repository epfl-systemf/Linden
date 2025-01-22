Require Import List.
Import ListNotations.

Require Import Regex Chars Groups.


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

Lemma seqop_assoc:
  forall X (o1 o2 o3:option X),
    seqop o1 (seqop o2 o3) = seqop (seqop o1 o2) o3.
Proof. intros. unfold seqop. destruct o1; destruct o2; auto. Qed.

(** * Priority Trees  *)

Inductive tree : Type :=
| Mismatch
| Match
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

Definition leaf: Type := (group_map).

(* returning the highest-priority result *)
(* we also return the corresponding group map *)
Fixpoint tree_res (t:tree) (gm:group_map) (idx:nat): option leaf :=
  match t with
  | Mismatch => None
  | Match => Some gm
  | Choice t1 t2 =>
      seqop (tree_res t1 gm idx) (tree_res t2 gm idx)
  | Read c t1 => tree_res t1 gm (idx + 1)
  | CheckFail _ => None
  | CheckPass _ t1 => tree_res t1 gm idx
  | OpenGroup gid t1 => tree_res t1 (open_group gm gid idx) idx
  | CloseGroup gid t1 => tree_res t1 (close_group gm gid idx) idx
  | ResetGroups gidl t1 => tree_res t1 (reset_groups gm gidl) idx
  end.

(* initializing on a the empty group map *)
Definition first_branch (t:tree) : option leaf :=
  tree_res t empty_group_map 0.

(** * All Tree Results *)

(* returns the ordered list of all results of a tree *)
(* together with the corresponding group map *)
Fixpoint tree_leaves (t:tree) (gm:group_map) (idx:nat): list leaf :=
  match t with
  | Mismatch => []
  | Match => [gm]
  | Choice t1 t2 =>
      tree_leaves t1 gm idx ++ tree_leaves t2 gm idx
  | Read c t1 => tree_leaves t1 gm (idx + 1)
  | CheckFail _ => []
  | CheckPass _ t1 => tree_leaves t1 gm idx
  | OpenGroup gid t1 => tree_leaves t1 (open_group gm gid idx) idx
  | CloseGroup gid t1 => tree_leaves t1 (close_group gm gid idx) idx
  | ResetGroups gidl t1 => tree_leaves t1 (reset_groups gm gidl) idx
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
  forall t gm idx,
    tree_res t gm idx = hd_error (tree_leaves t gm idx).
Proof.
  intros t. induction t; intros; simpl; auto.
  - rewrite IHt1. rewrite IHt2. rewrite hd_error_app. unfold seqop.
    destruct (hd_error (tree_leaves t1 gm idx)) eqn:HD; auto. 
Qed.
      
(** * Group Map irrelevance  *)
(* finding a match does not depend on the initial group map *)
(* we could phrase a stronger theorem about how to relate the two results *)
(* but for no I only need to differentiate when there is no results from when there is one *)

(* warning: actually so far I don't need this theorem *)

Lemma leaves_group_map_indep:
  forall t gm1 gm2 idx1 idx2,
    tree_leaves t gm1 idx1 = [] -> tree_leaves t gm2 idx2 = [].
Proof.
  intros t.
  induction t; intros; simpl; auto;
    simpl in H; try solve[inversion H];
    try solve[eapply IHt in H; eauto].
  - apply app_eq_nil in H as [NIL1 NIL2].
    apply IHt1 with (gm2:=gm2) (idx2:=idx2) in NIL1. apply IHt2 with (gm2:=gm2) (idx2:=idx2) in NIL2.
    rewrite NIL1. rewrite NIL2. auto.
Qed.
