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

Definition op_tree (o:option (tree*group_map)) (idx:nat): option leaf :=
  match o with
  | None => None
  | Some (t,gm) => tree_res t gm idx
  end.

(* defines the first result of a sequence of blocked, active and best trees *)
(* the option in the middle is for a tree being currently manipulated *)
(* this simplifies later intermediate theorems *)
Definition result (blocked:list (tree*group_map)) (tmp: option (tree*group_map)) (active:list (tree*group_map)) (best:option leaf)  (idx:nat): option leaf :=
  seqop (list_result blocked (idx+1))
    (seqop (op_tree tmp idx)
       (seqop (list_result active idx)
          best)).

Lemma result_move_active:
  forall blocked active best t gm idx,
    result blocked (Some (t,gm)) active best idx =
      result blocked None ((t,gm)::active) best idx.
Proof.
  intros blocked active best t gm idx. unfold result. apply f_equal. simpl.
  rewrite list_result_cons. rewrite seqop_assoc. auto.
Qed.

Lemma result_move_blocked:
  forall blocked active best idx ch t gm,
    result blocked (Some (Read ch t,gm)) active best idx =
      result (blocked ++ [(t,gm)]) None active best idx.
Proof.
  intros blocked active best idx ch t gm. unfold result. rewrite list_result_app.
  rewrite seqop_assoc. apply f_equal. simpl. auto.
Qed.


(* list_eq_seen seen l1 l2 means that l2 is a sublist of l1 where removed elements were in seen *)
Inductive list_eq_seen (seen:seentrees) : list (tree * group_map) -> list (tree * group_map) -> Prop :=
| les_nil: list_eq_seen seen [] []
| les_cons:
  forall t gm l1 l2
    (LES: list_eq_seen seen l1 l2),
    list_eq_seen seen ((t,gm)::l1) ((t,gm)::l2)
| les_skip:
  forall t gm l1 l2
    (LES: list_eq_seen seen l1 l2)
    (SEEN: inseen seen t = true),
    list_eq_seen seen ((t,gm)::l1) l2.

Lemma les_refl:
  forall seen l,
    list_eq_seen seen l l.
Proof. intros. induction l; try destruct a; try constructor; auto. Qed.

Lemma les_nil_left:
  forall seen l, list_eq_seen seen [] l -> l = [].
Proof. intros seen l H. inversion H. auto. Qed.

Lemma les_empty_seen:
  forall l1 l2, list_eq_seen initial_seentrees l1 l2 -> l1 = l2.
Proof. intros. induction H; subst; auto. rewrite initial_nothing in SEEN. inversion SEEN. Qed.
      
Lemma les_split:
  forall la1 la2 lb seen,
    list_eq_seen seen (la1++la2) lb ->
    exists lb1 lb2, lb = lb1 ++ lb2 /\
                 list_eq_seen seen la1 lb1 /\
                 list_eq_seen seen la2 lb2.
Proof.
  intros la1 la2 lb seen H. remember (la1 ++ la2) as la.
  generalize dependent la1. generalize dependent la2.
  induction H; intros.
  - destruct la1; inversion Heqla. destruct la2; inversion Heqla.
    exists []. exists []. simpl. split; auto. split; apply les_refl.
  -
Admitted.

  

(* res_eq means that for all list equivalent to active according to seeen, we get the same result *)
Definition res_eq (res:option leaf) (seen:seentrees) (blocked:list (tree*group_map)) (tmp:option (tree*group_map)) (active:list (tree*group_map)) (best:option leaf) (idx:nat) : Prop :=
  forall active_skipped
    (LES: list_eq_seen seen active active_skipped),
    result blocked tmp active_skipped best idx = res.

Inductive piketreeinv : option leaf -> pike_tree_seen_state -> Prop :=
| pti:
  forall active best blocked idx seen res
    (RES_EQ: res_eq res seen blocked None active best idx),
    piketreeinv res (PTSS idx active best blocked seen)
| pti_final:
  forall res,
    piketreeinv res (PTSS_final res).

(* whenever we skip a tree, this preserves the result of the entire equivalence class *)
Lemma seen_skip:
  forall seen active best blocked idx t gm res,
    inseen seen t = true ->
    res_eq res seen blocked None ((t,gm)::active) best idx ->
    res_eq res seen blocked None active best idx.
Proof.
  intros seen active best blocked idx t gm res H H0.
  unfold res_eq. intros active_skipped LES.
  assert (S1: list_eq_seen seen ((t,gm)::active) active_skipped).
  { apply les_skip; auto. }
  specialize (H0 active_skipped S1) as H1. rewrite H1.
  assert (S2: list_eq_seen seen ((t,gm)::active) active).
  { apply les_skip. apply les_refl. auto. }
  specialize (H0 active S2) as H2. auto. 
Qed.

(* equivalence with a list (when the head is not a result) implies equivalence with its tail *)
Lemma reseq_remove:
  forall seen active t gm idx best res
    (H: forall active_skipped : list (tree * group_map),
        list_eq_seen seen ((t, gm) :: active) active_skipped -> seqop (list_result active_skipped idx) best = res)
    (NORES: tree_res t gm idx = None),
  (forall skip, list_eq_seen seen active skip -> seqop (list_result skip idx) best = res).
Proof.
  intros seen active t gm idx best res RESEQ NORES skip EQ.
  specialize (RESEQ ((t,gm)::skip)).
  assert (list_eq_seen seen ((t,gm)::active) ((t,gm)::skip)) by (apply les_cons; auto).
  apply RESEQ in H. rewrite list_result_cons in H. rewrite NORES in H. simpl in H. auto.
Qed.

(* having no result does not depend on gm or idx (without backrefs) *)
Lemma no_tree_res:
  forall t gm1 gm2 idx1 idx2,
    tree_res t gm1 idx1 = None ->
    tree_res t gm2 idx2 = None.
Proof.
Admitted.

(* we can add the head of the active list to the seen set and preserve list equivalence *)
Lemma active_strengthen:
  forall seen t gm active blocked best idx res,
    res_eq res seen blocked None ((t,gm)::active) best idx ->
    res_eq res (add_seentrees seen t) blocked (Some (t,gm)) active best idx.
Proof.
  unfold res_eq, result. intros seen t gm active blocked best idx res RESEQ skip LES.
  destruct (list_result blocked (idx+1)) eqn:NOBLOCK.
  { simpl. simpl in RESEQ. apply RESEQ with (active_skipped:=((t,gm)::active)). apply les_refl. }
  simpl. simpl in RESEQ.
  destruct (tree_res t gm idx) eqn:REST.
  { simpl. specialize (RESEQ _ (les_refl seen ((t,gm)::active))).
    rewrite list_result_cons in RESEQ. rewrite REST in RESEQ. simpl in RESEQ. auto. }
  simpl.
  remember (add_seentrees seen t) as add.
  specialize (reseq_remove _ _ _ _ _ _ _ RESEQ REST) as R. clear RESEQ.
  induction LES.
  - simpl. specialize (R _ (les_refl seen [])). simpl in R. auto.
  - rewrite list_result_cons.
    destruct (tree_res t0 gm0 idx) eqn:RES0; simpl.
    + specialize (R _ (les_refl _ _)). rewrite list_result_cons in R.
      rewrite RES0 in R. simpl in R. auto.
    + apply IHLES. intros skip EQ. specialize (R ((t0,gm0)::skip)).
      assert (list_eq_seen seen ((t0,gm0)::l1) ((t0,gm0)::skip)) by (apply les_cons; auto).
      apply R in H. rewrite list_result_cons in H. rewrite RES0 in H. simpl in H. auto.
  - subst. apply in_add in SEEN as ADD. destruct ADD.
    + subst.
      assert (NORES: tree_res t gm0 idx = None) by (eapply no_tree_res; eauto).
      specialize (reseq_remove _ _ _ _ _ _ _ R NORES) as R0. clear R. apply IHLES in R0. auto.
    + destruct (tree_res t0 gm0 idx) eqn:RES0; simpl.
      * apply IHLES. intros skip H0. apply R. apply les_skip; auto.
      * apply IHLES.
        apply reseq_remove with (t:=t0) (gm:=gm0); auto.
Qed.

  
Theorem ptss_preservation:
  forall pts1 pts2 res
    (PSTEP: pike_tree_seen_step pts1 pts2)
    (INVARIANT: piketreeinv res pts1),
    piketreeinv res pts2.
Proof.
  intros pts1 pts2 res PSTEP INVARIANT.
  inversion INVARIANT; subst.
  2: { inversion PSTEP. }
  inversion PSTEP; subst.
  - constructor. eapply seen_skip; eauto.
  - specialize (RES_EQ [] (les_refl seen [])).
    unfold result in RES_EQ. simpl in RES_EQ. subst. constructor.
  - constructor. unfold res_eq. intros active_skipped LES. apply les_empty_seen in LES. subst.
    specialize (RES_EQ [] (les_refl _ [])). unfold result in RES_EQ. simpl in RES_EQ.
    unfold result. simpl. auto.
  - apply active_strengthen in RES_EQ as NEXT_EQ.
    destruct t; simpl in STEP; inversion STEP; subst; constructor.
    + simpl. unfold res_eq in *. intros skip EQ. specialize (NEXT_EQ skip EQ). unfold result in *.
      simpl in NEXT_EQ. simpl. auto.
    + admit.
    + simpl. unfold res_eq in *. intros skip EQ. specialize (NEXT_EQ skip EQ). unfold result in *.
      simpl in NEXT_EQ. simpl. auto.
    + admit.
    + unfold res_eq in *. intros skip EQ.
      apply les_split in EQ as [l1 [l2 [APP [EQ1 EQ2]]]].
      apply NEXT_EQ in EQ2. remember ([(t,open_group gm g idx)]) as active1.
      destruct EQ1; subst; inversion Heqactive1; subst.
      * inversion EQ1. subst. admit. (* should be ok *)
      * inversion EQ1. subst. simpl. apply RES_EQ.
    (* this I cannot prove I think *)
        admit.
    + admit.
    + admit.
  - admit.
  - admit.
Admitted.
