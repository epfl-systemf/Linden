(** * Pike Tree Seen Algorithm  *)

(* An algorithm that takes a tree as input, and finds the first match *)
(* Its execution is close to the kind of execution the PikeVM is doing on the bytecode *)
(* It explores multiples ordered branches in parallel, synced with their current input position *)
(* This time, compared to PikeTree, it also records in a "seen" set, *)
(* all the trees it has already started to explore *)
(* Non-deterministically, it can decide not to explore a tree it has already seen *)

Require Import List.
Import ListNotations.
Require Import Lia.

From Linden Require Import Regex Chars Groups Tree.
From Linden Require Import PikeTree PikeSubset.
From Warblre Require Import Base.

(** * Seen Sets  *)
Parameter seentrees: Type.
Parameter initial_seentrees: seentrees.
Parameter add_seentrees: seentrees -> tree -> seentrees.
Parameter inseen : seentrees -> tree -> bool.

Axiom in_add:
  forall seen t1 t2,
    inseen (add_seentrees seen t2) t1 = true <->
    t1 = t2 \/ inseen seen t1 = true.

Axiom initial_nothing:
  forall t, inseen initial_seentrees t = false.


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
  (* resetting the seen trees *)
  forall idx best blocked tgm seen,
    pike_tree_seen_step (PTSS idx [] best (tgm::blocked) seen) (PTSS (idx + 1) (tgm::blocked) best [] initial_seentrees)
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
  (PTSS 0 [(t, GroupMap.empty)] None [] initial_seentrees).


(** * Pike Tree Seen Correction  *)


(** * Non-deterministic tree results *)
(* any possible result after skipping or not any sub-tree in the seen set *)
Inductive tree_nd: tree -> group_map -> nat -> seentrees -> option leaf -> Prop :=
| tr_skip:
  forall seen t gm idx
    (SEEN: inseen seen t = true),
    tree_nd t gm idx seen None
| tr_mismatch:
  forall gm idx seen, tree_nd Mismatch gm idx seen None
| tr_match:
  forall gm idx seen, tree_nd Match gm idx seen (Some gm)
| tr_choice:
  forall t1 t2 gm idx l1 l2 seen
    (TR1: tree_nd t1 gm idx seen l1)
    (TR2: tree_nd t2 gm idx seen l2),
    tree_nd (Choice t1 t2) gm idx seen (seqop l1 l2)
| tr_read:
  forall t cd gm idx l seen
    (TR: tree_nd t gm (idx+1) seen l),
    tree_nd (Read cd t) gm idx seen l
| tr_progress:
  forall t str gm idx l seen
    (TR: tree_nd t gm idx seen l),
    tree_nd (Progress str t) gm idx seen l
| tr_groupaction:
  forall t act gm idx l seen
    (TR: tree_nd t (GroupMap.update idx act gm) idx seen l),
    tree_nd (GroupAction act t) gm idx seen l.
(* To keep this relation as simple as possible, it does not compute
the results of a tree which does not corespond to the regexes
supported by the engine. We could support them, but we won't need them
and it would require adding a direction as argument *)



(* the normal result, obtained with function tree_res without skipping anything, is a possible result *)
Lemma tree_res_nd:
  forall t gm idx seen,
    pike_subtree t -> 
    tree_nd t gm idx seen (tree_res t gm idx forward).
Proof.
  intros t. induction t; intros; simpl; try solve[inversion H]; try solve[pike_subset; constructor; auto].
Qed.

(* when there is nothing in seen, there is only one possible result *)
Lemma tree_nd_initial:
  forall t gm idx res,
    pike_subtree t ->
    tree_nd t gm idx initial_seentrees res ->
    res = tree_res t gm idx forward.
Proof.
  intros t gm idx res PIKE H.
  remember initial_seentrees as init.
  induction H; simpl; pike_subset; auto.
  - subst. rewrite initial_nothing in SEEN. inversion SEEN.
  - pike_subset. specialize (IHtree_nd1 H3 (@eq_refl _ _)).
    specialize (IHtree_nd2 H4 (@eq_refl _ _)). subst. auto.
Qed.

Inductive list_nd: list (tree * group_map) -> nat -> seentrees -> option leaf -> Prop :=
| tlr_nil:
  forall idx seen, list_nd [] idx seen None
| tlr_cons:
  forall t gm active idx seen l1 l2 l3
    (TR: tree_nd t gm idx seen l1)
    (TLR: list_nd active idx seen l2)
    (SEQ: l3 = seqop l1 l2),
    list_nd ((t,gm)::active) idx seen l3.

(* the normal result for a list, without skipping anything, is a possible result *)
Lemma list_result_nd:
  forall active idx seen,
    pike_list active -> 
    list_nd active idx seen (list_result active idx).
Proof.
  intros active. induction active; try destruct a as [t gm]; intros; pike_subset; try constructor.
  rewrite list_result_cons.
  econstructor; eauto. apply tree_res_nd. auto.
Qed.

(* when there is nothing in seen, there is only one possible result *)
Lemma list_nd_initial:
  forall l idx res,
    pike_list l ->
    list_nd l idx initial_seentrees res ->
    res = list_result l idx.
Proof.
  intros l idx res PIKE H.
  remember initial_seentrees as init.
  induction H; simpl; auto; pike_subset.
  rewrite list_result_cons. specialize (IHlist_nd H1 (eq_refl _)). subst.
  apply tree_nd_initial in TR; subst; auto.
Qed.


Inductive state_nd: nat -> list (tree*group_map) -> option leaf -> list (tree*group_map) -> seentrees -> option leaf -> Prop :=
| sr:
  forall blocked active best idx seen r1 r2 rseq
    (BLOCKED: list_result blocked (idx+1) = r1)
    (ACTIVE: list_nd active idx seen r2)
    (SEQ: rseq = seqop r1 (seqop r2 best)),
    state_nd idx active best blocked seen rseq.

(* Invariant of the PikeTreeSeen execution *)
(* at any moment, all the possibles results of the current state are all equal (equal to the first result of the original tree) *)
Inductive piketreeinv: pike_tree_seen_state -> option leaf -> Prop :=
| pi:
  forall result blocked active best idx seen
    (SAMERES: forall res, state_nd idx active best blocked seen res -> res = result),
    piketreeinv (PTSS idx active best blocked seen) result
| sr_final:
  forall best,
    piketreeinv (PTSS_final best) best.

(** * Initialization  *)

Lemma init_piketree_inv:
  forall t,
    pike_subtree t -> 
    piketreeinv (pike_tree_seen_initial_state t) (tree_res t GroupMap.empty 0 forward).
Proof.
  intros t. unfold pike_tree_seen_initial_state. constructor.
  intros res STATEND. inversion STATEND; subst.
  simpl. rewrite seqop_none. inversion ACTIVE; subst.
  inversion TLR; subst. rewrite seqop_none.
  apply tree_nd_initial in TR; auto.
Qed.

(** * Non deterministic results lemmas  *)

(* a tree having no results is independent of the gm and the idx *)
Lemma no_tree_result:
  forall t gm1 gm2 idx1 idx2
    (NORES: tree_res t gm1 idx1 forward = None),
    tree_res t gm2 idx2 forward = None.
Proof.
  intros. rewrite first_tree_leaf. rewrite first_tree_leaf in NORES.
  destruct (tree_leaves t gm1 idx1 forward) eqn:HTL.
  2: { inversion NORES. }
  eapply leaves_group_map_indep in HTL. rewrite HTL. auto.
Qed.    

(* the same is true for a non-deterministic result *)
Lemma no_tree_result_nd:
  forall t seen gm1 gm2 idx1 idx2
    (NORES: tree_nd t gm1 idx1 seen None),
    tree_nd t gm2 idx2 seen None.
Proof.
  intros t. induction t; intros;
    try solve[inversion NORES; subst; try solve[constructor; auto]; try solve [constructor; eapply IHt; eauto]].
  inversion NORES; subst.
  + apply tr_skip. auto.
  + destruct l1; destruct l2; inversion H.
    apply tr_choice; auto.
    * eapply IHt1; eauto.
    * eapply IHt2; eauto.
Qed.

(* skipping over a new tree doesn't change the result if the tree that is being skipped does not have results *)
Lemma add_seen:
  forall t seen tseen gm idx res
    (NORES: tree_res tseen gm idx forward = None)
    (TREEND: tree_nd t gm idx (add_seentrees seen tseen) res)
    (SUBSET: pike_subtree tseen),
    tree_nd t gm idx seen res.
Proof.
  intros t seen tseen gm idx res NORES TREEND SUBSET.
  remember (add_seentrees seen tseen) as add.
  induction TREEND; subst; try solve[constructor; auto];
    try solve [constructor; apply IHTREEND; auto; eapply no_tree_result; eauto].
  apply in_add in SEEN as [EQ | SEEN].
  + subst. rewrite <- NORES. apply tree_res_nd; auto.
  + apply tr_skip. auto.
Qed.

(* same lemma generalizes to lists of trees *)
Lemma list_add_seen:
  forall l seen tseen gm idx res
    (NORES: tree_res tseen gm idx forward = None)
    (LISTND: list_nd l idx (add_seentrees seen tseen) res)
    (SUBSET: pike_subtree tseen),
    list_nd l idx seen res.
Proof.
  intros l seen tseen gm idx res NORES LISTND SUBSET.
  remember (add_seentrees seen tseen) as add.
  induction LISTND; subst; econstructor; eauto.
  eapply add_seen; eauto. eapply no_tree_result; eauto.
Qed.

(* skipping over a new tree doesn't change the result if the tree that is being skipped can produce a None result *)
Lemma add_seen_nd:
  forall t seen tseen gm idx res
    (NORES: tree_nd tseen gm idx seen None)
    (TREEND: tree_nd t gm idx (add_seentrees seen tseen) res),
    tree_nd t gm idx seen res.
Proof.
  intros t seen tseen gm idx res NORES TREEND.
  remember (add_seentrees seen tseen) as add.
  induction TREEND; subst; try solve[constructor; auto];
    try solve [constructor; apply IHTREEND; auto; eapply no_tree_result_nd; eauto].
  - apply in_add in SEEN as [EQ | SEEN].
    + subst. apply NORES.
    + apply tr_skip. auto.
Qed.

(* same lemma generalizes to lists of trees *)
Lemma list_add_seen_nd:
  forall l seen tseen gm idx res
    (NORES: tree_nd tseen gm idx seen None)
    (LISTND: list_nd l idx (add_seentrees seen tseen) res),
    list_nd l idx seen res.
Proof.
  intros l seen tseen gm idx res NORES LISTND.
  remember (add_seentrees seen tseen) as add.
  induction LISTND; subst; econstructor; eauto.
  eapply add_seen_nd; eauto. eapply no_tree_result_nd; eauto.
Qed.


(* using the size of the tree will help us make sure that whenever a tree generates active subtrees, *)
(* none of these subtrees can contain the parent tree that generated them *)
Fixpoint size (t:tree) : nat :=
  match t with
  | Mismatch | Match | LKFail _ _ => O
  | Read _ t1 | Progress _ t1 | GroupAction _ t1 | AnchorPass _ t1 | ReadBackRef _ t1 => 1 + size t1
  | Choice t1 t2 => size t1 + size t2 + 1
  | LK _ tlk t1 => 1 + size t1
  end.

(* skipping over a new tree does not change the result of another tree if we know that the newly *)
(* skipped over tree cannot appear in the tree we compute the result of *)
Lemma add_parent_tree:
  forall tseen t res seen gm idx
    (SIZE: size t < size tseen)
    (TREEND: tree_nd t gm idx (add_seentrees seen tseen) res),
    tree_nd t gm idx seen res.
Proof.
  intros tseen t res seen gm idx SIZE TREEND.
  remember (add_seentrees seen tseen) as add.
  induction TREEND; subst; simpl in SIZE;
    try solve [constructor; apply IHTREEND; auto; lia].
  - apply in_add in SEEN as [EQ | SEEN].
    + subst. exfalso. eapply PeanoNat.Nat.lt_irrefl. eauto.
    + apply tr_skip. auto.
  - constructor.
    + apply IHTREEND1; auto. lia.
    + apply IHTREEND2; auto. lia.
Qed.


(** * Invariant Preservation  *)

Theorem ptss_preservation:
  forall pts1 pts2 res
    (PSTEP: pike_tree_seen_step pts1 pts2)
    (INVARIANT: piketreeinv pts1 res),
    piketreeinv pts2 res.
Proof.
  intros pts1 pts2 res PSTEP INVARIANT.
  destruct INVARIANT.
  2: { inversion PSTEP. }
  inversion PSTEP; subst; [| | |destruct t; inversion STEP; subst| |].
  (* skipping *)
  - constructor. intros res STATEND.
    apply SAMERES. inversion STATEND; subst.
    econstructor; eauto. replace r2 with (seqop None r2) by (simpl; auto).
    eapply tlr_cons; eauto. apply tr_skip. auto.
  (* final *)
  - assert (best = result).
    { apply SAMERES. econstructor; econstructor. }
    subst. constructor.
  (* nextchar *)
  - constructor. intros res STATEND. inversion STATEND; subst.
    apply list_nd_initial in ACTIVE.
    simpl. subst. specialize (SAMERES (seqop (list_result (tgm::blocked0) (idx+1)) (seqop None best))).
    simpl in SAMERES. apply SAMERES. econstructor; constructor.
  (* mismatch *)
  - simpl. constructor. intros res STATEND. inversion STATEND; subst. apply SAMERES.
    econstructor; eauto. econstructor; eauto. 
    + eapply tr_mismatch.
    + eapply list_add_seen with (gm:=gm) in ACTIVE; eauto.
    + auto.
  (* choice *)
  - simpl. constructor. intros res STATEND. inversion STATEND; subst.
    inversion ACTIVE; subst. inversion TLR; subst.
    apply SAMERES.
    apply add_parent_tree in TR.
    2: { simpl. lia. }
    apply add_parent_tree in TR0.
    2: { simpl. lia. }
    assert (PARENT: tree_nd (Choice t1 t2) gm idx seen (seqop l1 l0)).
    { apply tr_choice; auto. }
    (* case analysis: did t contribute to the result? *)
    destruct (seqop l1 l0) as [leaf|] eqn:CHOICE.
    + econstructor; eauto. rewrite seqop_assoc.
      eapply tlr_cons; eauto.
      * apply list_result_nd.
      * rewrite CHOICE. simpl. auto.
    (* when the tree did not contribute, adding it to seen does not change the results *)
    + destruct l1; destruct l0; inversion CHOICE.
      econstructor; eauto.
      eapply list_add_seen_nd with (gm:=gm) in TLR; auto.
      eapply list_add_seen_nd with (gm:=gm) in TLR0; auto.
      econstructor; eauto.
  (* checkfail *)
  - simpl. constructor. intros res STATEND. inversion STATEND; subst. apply SAMERES.
    econstructor; eauto. econstructor; eauto.
    + eapply tr_checkfail.
    + eapply list_add_seen with (gm:=gm) in ACTIVE; eauto.
    + auto.
  (* checkpass *)
  - simpl. constructor. intros res STATEND. inversion STATEND; subst.
    inversion ACTIVE; subst.
    apply SAMERES.
    apply add_parent_tree in TR.
    2: { simpl. lia. }
    assert (PARENT: tree_nd (CheckPass str t) gm idx seen l1).
    { apply tr_checkpass; auto. }
    (* case analysis: did t contribute to the result? *)
    destruct l1 as [leaf1|].
    + econstructor; eauto. simpl.
      eapply tlr_cons; eauto.
      apply list_result_nd.
    (* when the tree did not contribute, adding it to seen does not change the results *)
    + econstructor; eauto.
      eapply list_add_seen_nd with (gm:=gm) in TLR; auto.
      econstructor; eauto.
  (* group action *)
  - simpl. constructor. intros res STATEND. inversion STATEND; subst.
    inversion ACTIVE; subst.
    apply SAMERES.
    apply add_parent_tree in TR.
    2: { simpl. lia. }
    assert (PARENT: tree_nd (GroupAction g t) gm idx seen l1).
    { apply tr_groupaction; auto. }
    (* case analysis: did t contribute to the result? *)
    destruct l1 as [leaf1|].
    + econstructor; eauto. simpl.
      eapply tlr_cons; eauto.
      apply list_result_nd.
    (* when the tree did not contribute, adding it to seen does not change the results *)
    + econstructor; eauto.
      eapply list_add_seen_nd with (gm:=gm) in TLR; auto.
      econstructor; eauto.
  (* match *)
  - destruct t; inversion STEP; subst. constructor.
    intros res STATEND. inversion STATEND; subst.
    inversion ACTIVE; subst. simpl. 
    apply SAMERES. eapply sr with (r2:=Some gm); eauto.
    replace (Some gm) with (seqop (Some gm) (list_result active0 idx)) by (simpl; auto).
    econstructor; auto.
    + apply tr_match.
    + apply list_result_nd.
  (* blocked *)
  - destruct t; inversion STEP; subst. constructor.
    intros res STATEND. inversion STATEND; subst.
    apply SAMERES.
    rewrite list_result_app. rewrite list_result_cons.
    replace (list_result [] (idx+1)) with (None:option leaf).
    2: { unfold list_result, seqop_list. simpl. auto. }
    rewrite seqop_none. rewrite <- seqop_assoc. rewrite seqop_assoc with (o3:=best).
    econstructor; eauto.
    destruct (tree_res newt gm (idx+1)) eqn:REST.
    (* if the blocked tree contained a match, then we don't care about the result of active *)
    (* we can simply use the result obtained without skipping anything *)
    + eapply tlr_cons.
      * apply tree_res_nd.
      * apply list_result_nd.
      * simpl. rewrite REST. simpl. auto.
    + eapply tlr_cons.
      (* if the blocked tree did not contain a match, we prove that the adding it to the seen set *)
      (* does not change the skipping of the following active trees, using list_add_seen *)
      * apply tree_res_nd. 
      * eapply list_add_seen in ACTIVE; eauto.
      * simpl. rewrite REST. simpl. auto.
Qed.
