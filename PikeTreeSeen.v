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
  (PTSS 0 [(t, empty_group_map)] None [] initial_seentrees).


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
| tr_checkpass:
  forall t str gm idx l seen
    (TR: tree_nd t gm idx seen l),
    tree_nd (CheckPass str t) gm idx seen l
| tr_checkfail:
  forall str gm idx seen, tree_nd (CheckFail str) gm idx seen None
| tr_open:
  forall t gid gm idx l seen
    (TR: tree_nd t (open_group gm gid idx) idx seen l),
    tree_nd (OpenGroup gid t) gm idx seen l
| tr_close:
  forall t gid gm idx l seen
    (TR: tree_nd t (close_group gm gid idx) idx seen l),
    tree_nd (CloseGroup gid t) gm idx seen l
| tr_reset:
  forall t gidl gm idx l seen
    (TR: tree_nd t (reset_groups gm gidl) idx seen l),
    tree_nd (ResetGroups gidl t) gm idx seen l.

(* the normal result, obtained with function tree_res without skipping anything, is a possible result *)
Lemma tree_res_nd:
  forall t gm idx seen,
    tree_nd t gm idx seen (tree_res t gm idx).
Proof.
  intros t. induction t; intros; simpl; try solve[constructor; auto].
Qed.

(* when there is nothing in seen, there is only one possible result *)
Lemma tree_nd_initial:
  forall t gm idx res,
    tree_nd t gm idx initial_seentrees res ->
    res = tree_res t gm idx.
Proof.
  intros t gm idx res H.
  remember initial_seentrees as init.
  induction H; simpl; auto.
  - subst. rewrite initial_nothing in SEEN. inversion SEEN.
  - specialize (IHtree_nd1 Heqinit). specialize (IHtree_nd2 Heqinit). subst. auto.
Qed.

Inductive list_nd: list (tree * group_map) -> nat -> seentrees -> option leaf -> Prop :=
| tlr_nil:
  forall idx seen, list_nd [] idx seen None
| tlr_cons:
  forall t gm active idx seen l1 l2
    (TR: tree_nd t gm idx seen l1)
    (TLR: list_nd active idx seen l2),
    list_nd ((t,gm)::active) idx seen (seqop l1 l2).

(* the normal result for a list, without skipping anything, is a possible result *)
Lemma list_result_nd:
  forall active idx seen,
    list_nd active idx seen (list_result active idx).
Proof.
  intros active. induction active; intros; try constructor.
  destruct a as [t gm]. rewrite list_result_cons.
  constructor; auto. apply tree_res_nd.
Qed.

(* when there is nothing in seen, there is only one possible result *)
Lemma list_nd_initial:
  forall l idx res,
    list_nd l idx initial_seentrees res ->
    res = list_result l idx.
Proof.
  intros l idx res H.
  remember initial_seentrees as init.
  induction H; simpl; auto.
  subst. rewrite list_result_cons. specialize (IHlist_nd (eq_refl _)). subst.
  apply tree_nd_initial in TR. subst. auto.
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
  inversion PSTEP; subst.
  (* skipping *)
  - constructor. intros res STATEND.
    apply SAMERES. inversion STATEND; subst.
    econstructor; eauto. replace r2 with (seqop None r2) by (simpl; auto).
    apply tlr_cons; auto. apply tr_skip. auto.
  (* final *)
  - assert (best = result).
    { apply SAMERES. econstructor; econstructor. }
    subst. constructor.
  (* nextchar *)
  - constructor. intros res STATEND. inversion STATEND; subst.
    apply list_nd_initial in ACTIVE.
    simpl. subst. specialize (SAMERES (seqop (list_result (tgm::blocked0) (idx+1)) (seqop None best))).
    simpl in SAMERES. apply SAMERES. econstructor; constructor.
  (* active *)
  - admit.
  (* match *)
  - admit.
  (* blocked *)
  - admit.
Admitted.
