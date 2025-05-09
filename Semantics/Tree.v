Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Coq Require Import PeanoNat.
From Warblre Require Import Typeclasses Parameters.


(* A tree represents all the possible paths that could be explored by a backtracking engine *)
(* Its nodes are made out of actions: manipulating groups, choosing between 2 branches etc *)
(* Branches of the tree are ordered by priority: the leftmost branch is the top priority behavior *)

(** * Chaining optional results  *)
(* in the future, maybe use an option monad *)

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
  simpl. rewrite H.
  rewrite seqop_some. auto.
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



Section Tree.
  Context `{characterClass: Character.class}.
  
  Inductive tree : Type :=
  | Mismatch
  | Match
  | Choice (t1 t2:tree)
  | Read (c:Character) (t:tree)
  | CheckFail (str:string) (* failed to make progress wrt some string *)
  | CheckPass (str:string) (t:tree)
  | GroupAction (g:groupaction) (t: tree)
  | LK (lk: lookaround) (tlk: tree) (t: tree) (* First tree is the lookaround tree. *)
  | LKFail (lk: lookaround) (tlk: tree)
  | AnchorFail (a: anchor)
  | AnchorPass (a: anchor) (t: tree)
  .

  (** ** Maximum group ID of a tree *)
  (* Maximum group ID of a list of group IDs *)
  Fixpoint max_gid_list (gl: list group_id) :=
    match gl with
    | [] => 0
    | gid::q => max gid (max_gid_list q)
    end.

  (* Maximum group ID of a groupaction *)
  Definition max_gid_groupaction (act: groupaction) :=
    match act with
    | Open gid => gid
    | Close gid => gid
    | Reset gl => max_gid_list gl
    end.

  (* Maximum group ID of a tree *)
  Fixpoint max_gid_tree (t: tree) :=
    match t with
    | Mismatch | Match | CheckFail _ => 0
    | Choice t1 t2 => max (max_gid_tree t1) (max_gid_tree t2)
    | Read _ t | CheckPass _ t => max_gid_tree t
    | GroupAction act t => max (max_gid_groupaction act) (max_gid_tree t)
    | LK _ tlk t => max (max_gid_tree tlk) (max_gid_tree t)
    | LKFail _ tlk => max_gid_tree tlk
    | AnchorFail _ => 0
    | AnchorPass _ t => max_gid_tree t
    end.


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
    | GroupAction g t1 => tree_res t1 (GroupMap.update idx g gm) idx
    | LK lk tlk t1 =>
        match (positivity lk) with
        | true => 
            match tree_res tlk gm idx with
            | None => None
            (* using the captures defined in the first branch of the lookahead *)
            | Some gm' => tree_res t1 gm' idx
            end
        | false =>
            match tree_res tlk gm idx with
            (* using previous captures *)
            | None => tree_res t1 gm idx
            | Some _ => None
            end
        end
    | LKFail _ _ => None
    | AnchorFail _ => None
    | AnchorPass _ t => tree_res t gm idx
    end.

  (* initializing on a the empty group map *)
  Definition first_branch (t:tree) : option leaf :=
    tree_res t GroupMap.empty 0.

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
    | GroupAction g t1 => tree_leaves t1 (GroupMap.update idx g gm) idx
    | LK lk tlk t1 =>
        match (positivity lk) with (* Do we want to explore all the branches of the lookahead tree that succeed? *)
        | true =>
            match (tree_leaves tlk gm idx) with
            | [] => []             (* should not happen *)
            (* using the captures defined in the first branch of the lookaround *)
            | gm'::_ => tree_leaves t1 gm' idx
            end
        | false =>
            match (tree_leaves tlk gm idx) with
            (* using previous captures *)
            | [] => tree_leaves t1 gm idx
            | _ => []              (* should not happen *)
            end
        end
    | LKFail _ _ => []
    | AnchorFail _ => []
    | AnchorPass _ t => tree_leaves t gm idx
    end.


  (* Property that this definition coincides on the first element with the previous definition given a tree. *)
  Definition first_tree_leaf_prop (t: tree): Prop :=
    forall gm idx, tree_res t gm idx = hd_error (tree_leaves t gm idx).


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

  (* Intermediate lemma for positive lookarounds *)
  Lemma first_tree_leaf_poslk:
    forall lk tlk t1,
      positivity lk = true -> first_tree_leaf_prop tlk -> first_tree_leaf_prop t1 ->
      first_tree_leaf_prop (LK lk tlk t1).
  Proof.
    intros lk tlk t1 Hpos IHtlk IHt1.
    unfold first_tree_leaf_prop in *. intros gm idx. simpl. rewrite Hpos.
    specialize (IHtlk gm idx). destruct (tree_res tlk gm idx); destruct (tree_leaves tlk gm idx); try discriminate; simpl in *. 2: reflexivity.
    injection IHtlk as <-; auto.
  Qed.

  (* Intermediate lemma for negative lookarounds *)
  Lemma first_tree_leaf_neglk:
    forall lk tlk t1,
      positivity lk = false -> first_tree_leaf_prop tlk -> first_tree_leaf_prop t1 ->
      first_tree_leaf_prop (LK lk tlk t1).
  Proof.
    intros lk tlk t1 Hpos IHtlk IHt1.
    unfold first_tree_leaf_prop in *. intros gm idx. simpl. rewrite Hpos.
    specialize (IHtlk gm idx). destruct (tree_res tlk gm idx); destruct (tree_leaves tlk gm idx); try discriminate; auto.
  Qed.


  (* this definition coincides on the first element with the previous definition *)
  Theorem first_tree_leaf:
    forall t gm idx,
      tree_res t gm idx = hd_error (tree_leaves t gm idx).
  Proof.
    intros t. induction t; intros. 1-7,9-11: simpl; auto.
    - rewrite IHt1. rewrite IHt2. rewrite hd_error_app. unfold seqop.
      destruct (hd_error (tree_leaves t1 gm idx)) eqn:HD; auto.
    - destruct (positivity lk) eqn:Hlkpos. + now apply first_tree_leaf_poslk. + now apply first_tree_leaf_neglk.
  Qed.

  (** * Group Map irrelevance  *)
  (* finding a match does not depend on the initial group map *)
  (* we could phrase a stronger theorem about how to relate the two results *)
  (* but for now I only need to differentiate when there is no results from when there is one *)

  (* warning: actually so far I don't need this theorem *)

  (* Group map irrelevance property for a given tree. *)
  Definition leaves_group_map_indep_prop (t: tree): Prop :=
    forall gm1 gm2 idx1 idx2,
      tree_leaves t gm1 idx1 = [] -> tree_leaves t gm2 idx2 = [].

  (* Intermediate lemma for positive lookarounds *)
  Lemma leaves_group_map_indep_poslk:
    forall lk tlk t1,
      positivity lk = true -> leaves_group_map_indep_prop tlk -> leaves_group_map_indep_prop t1 ->
      leaves_group_map_indep_prop (LK lk tlk t1).
  Proof.
    intros lk tlk t1 Hposlk IHtlk IHt1; unfold leaves_group_map_indep_prop in *; simpl.
    rewrite Hposlk. intros gm1 gm2 idx1 idx2 Hnil1.
    specialize (IHtlk gm1 gm2 idx1 idx2). destruct (tree_leaves tlk gm1 idx1) as [|gm' q]; simpl in *.
    1: { specialize (IHtlk eq_refl). now rewrite IHtlk. }
    destruct (tree_leaves tlk gm2 idx2) as [|gm'0 q0]; simpl in *. 1: reflexivity.
    eapply IHt1; eauto.
  Qed.

  (* Intermediate lemma for negative lookarounds *)
  Lemma leaves_group_map_indep_neglk:
    forall lk tlk t1,
      positivity lk = false -> leaves_group_map_indep_prop tlk -> leaves_group_map_indep_prop t1 ->
      leaves_group_map_indep_prop (LK lk tlk t1).
  Proof.
    intros lk tlk t1 Hposlk IHtlk IHt1; unfold leaves_group_map_indep_prop in *; simpl.
    rewrite Hposlk. intros gm1 gm2 idx1 idx2 Hnil1.
    destruct (tree_leaves tlk gm1 idx1) as [|gm' q] eqn:Hnilsub1; simpl in *.
    1: { specialize (IHtlk gm1 gm2 idx1 idx2 Hnilsub1). rewrite IHtlk. eapply IHt1; eauto. }
    destruct (tree_leaves tlk gm2 idx2) as [|gm'0 q0] eqn:Hnilsub2; simpl in *. 2: reflexivity.
    exfalso. apply IHtlk with (gm2 := gm1) (idx2 := idx1) in Hnilsub2. congruence.
  Qed.


  Lemma leaves_group_map_indep:
    forall t gm1 gm2 idx1 idx2,
      tree_leaves t gm1 idx1 = [] -> tree_leaves t gm2 idx2 = [].
  Proof.
    intros t.
    induction t; intros. 1-7,9-11: simpl; auto;
      simpl in H; try solve[inversion H];
      try solve[eapply IHt in H; eauto].
    - apply app_eq_nil in H as [NIL1 NIL2].
      apply IHt1 with (gm2:=gm2) (idx2:=idx2) in NIL1. apply IHt2 with (gm2:=gm2) (idx2:=idx2) in NIL2.
      rewrite NIL1. rewrite NIL2. auto.
    - destruct (positivity lk) eqn:Hlkpos. + eapply leaves_group_map_indep_poslk; eauto. + eapply leaves_group_map_indep_neglk; eauto.
  Qed.
End Tree.
