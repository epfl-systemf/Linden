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
Definition res_eq (seen:seentrees) (blocked:list (tree*group_map)) (tmp:option (tree*group_map)) (active:list (tree*group_map)) (best:option leaf) (idx:nat) : Prop :=
  forall active_skipped
    (LES: list_eq_seen seen active active_skipped),
    result blocked tmp active_skipped best idx =
      result blocked tmp active best idx.

Inductive piketreeinv : option leaf -> pike_tree_seen_state -> Prop :=
| pti:
  forall active best blocked idx seen res
    (RES_EQ: res_eq seen blocked None active best idx),
    (* to fix to add the equality to res *)
    piketreeinv res (PTSS idx active best blocked seen)
| pti_final:
  forall res,
    piketreeinv res (PTSS_final res).

(* whenever we skip a tree, this preserves the result of the entire equivalence class *)
Lemma seen_skip:
  forall seen active best blocked idx t gm,
    inseen seen t = true ->
    res_eq seen blocked None ((t,gm)::active) best idx ->
    res_eq seen blocked None active best idx.
Proof.
  intros seen active best blocked idx t gm H H0.
  unfold res_eq. intros active_skipped LES.
  assert (S1: list_eq_seen seen ((t,gm)::active) active_skipped).
  { apply les_skip; auto. }
  specialize (H0 active_skipped S1) as H1. rewrite H1.
  assert (S2: list_eq_seen seen ((t,gm)::active) active).
  { apply les_skip. apply les_refl. auto. }
  specialize (H0 active S2) as H2. rewrite H2. auto.
Qed.

(* adding a tree with no result to the seen set allows us to keep the result of the same list *)
Lemma active_strengthen:
  forall seen t active skipped idx gm
    (SAME_RES: forall skip, list_eq_seen seen active skip -> list_result active idx = list_result skip idx)
    (NORES: tree_res t gm idx = None)
    (LES: list_eq_seen (add_seentrees seen t) active skipped),
    list_result active idx = list_result skipped idx.
Proof.
  intros seen t active skipped idx gm SAME_RES NORES LES.
  remember (add_seentrees seen t) as add.
  induction LES; intros.
  - auto.
  - rewrite list_result_cons. rewrite list_result_cons.
    destruct (tree_res t0 gm0 idx) eqn:RES0.
    { simpl.  auto. }
    simpl. eapply IHLES; eauto.
    intros skip EQ. specialize (SAME_RES ((t0,gm0)::skip)).
    assert (EQ0: list_eq_seen seen ((t0, gm0) :: l1) ((t0, gm0) :: skip)).
    { apply les_cons. auto. }
    apply SAME_RES in EQ0. rewrite list_result_cons in EQ0. rewrite list_result_cons in EQ0.
    rewrite RES0 in EQ0. simpl in EQ0. auto.
  - subst. apply in_add in SEEN as ADD. destruct ADD.
    + subst. rewrite list_result_cons.
      assert (tree_res t gm0 idx = None) by admit.
      (* the existence of a match does not depend on the gm, at least without backrefs *)
      rewrite H. simpl. apply IHLES.
      intros skip EQ. specialize (SAME_RES ((t,gm0)::skip)).
      assert (EQ0: list_eq_seen seen ((t, gm0) :: l1) ((t, gm0) :: skip)).
      { apply les_cons. auto. }
      apply SAME_RES in EQ0. rewrite list_result_cons in EQ0. rewrite list_result_cons in EQ0.
      rewrite H in EQ0. simpl in EQ0. auto.
    (* this really needs to be rewritten *)
    + rewrite list_result_cons.
      destruct (tree_res t0 gm0 idx) eqn:RES0.
      * assert (list_result l1 idx = list_result l2 idx).
        { apply IHLES. intros skip EQ.
          assert (list_result skip idx = Some l).
          { specialize (SAME_RES skip).
            assert (EQ0: list_eq_seen seen ((t0,gm0)::l1) skip).
            { apply les_skip; auto. }
            apply SAME_RES in EQ0. rewrite list_result_cons in EQ0. rewrite RES0 in EQ0.
            simpl in EQ0. auto.
          }
          specialize (SAME_RES l1).
          assert (EQ0: list_eq_seen seen ((t0,gm0)::l1) l1).
          { apply les_skip; auto.  apply les_refl. }
          apply SAME_RES in EQ0. rewrite list_result_cons in EQ0. rewrite RES0 in EQ0.
          simpl in EQ0. rewrite H0. auto.
        }
        rewrite <- H0.
        assert (list_result l1 idx = Some l).
        { specialize (SAME_RES l1).
          assert (list_eq_seen seen ((t0, gm0) :: l1) l1).
          { apply les_skip. apply les_refl. auto. }
          apply SAME_RES in H1. rewrite list_result_cons in H1. rewrite RES0 in H1.
          simpl in H1. auto. }
        simpl. auto.
      * simpl. apply IHLES. intros skip EQ.
        specialize (SAME_RES skip).
        assert (EQ0: list_eq_seen seen ((t0,gm0)::l1) skip).
        { apply les_skip; auto.  }
        apply SAME_RES in EQ0. rewrite list_result_cons in EQ0. rewrite RES0 in EQ0.
        simpl in EQ0. auto.
Admitted.



Theorem seen_accumulate:
  forall seen active best blocked idx t gm,
    res_eq seen blocked None ((t,gm)::active) best idx ->
    res_eq (add_seentrees seen t) blocked (Some (t,gm)) active best idx.
Proof.
  intros seen active best blocked idx t gm RES_EQ.
  unfold res_eq. intros active_skipped LES.
  remember (add_seentrees seen t) as add.
  induction LES; intros.
  - admit.
  - admit.
  - admit.
Admitted.


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
    unfold result in RES_EQ. simpl in RES_EQ. subst. admit.
  - constructor. unfold res_eq. intros active_skipped LES. apply les_empty_seen in LES. subst.
    specialize (RES_EQ [] (les_refl _ [])). unfold result in RES_EQ. simpl in RES_EQ.
    unfold result. simpl. auto.
  - apply seen_accumulate in RES_EQ as NEXT_EQ.
    destruct t; simpl in STEP; inversion STEP; subst; constructor.
    + unfold res_eq. intros. specialize (NEXT_EQ active_skipped LES). subst. unfold result. simpl. auto.
    + unfold res_eq. intros active_skipped LES. apply les_split in LES as [lb1 [lb2 [Hlb [LES1 LES2]]]].
      specialize (NEXT_EQ lb2 LES2). subst. admit.
    + unfold res_eq. intros. specialize (NEXT_EQ active_skipped LES). subst. unfold result. simpl. auto.
    + admit.
    + admit.
    + admit.
    + admit.   
  - destruct t; simpl in STEP; inversion STEP; subst.
    constructor. apply seen_accumulate in RES_EQ.
    unfold res_eq. intros active_skipped LES.
    specialize (RES_EQ active0 (les_refl _ active0)).
    apply les_nil_left in LES. subst.
    unfold result. apply f_equal. simpl. auto.
  - destruct t; simpl in STEP; inversion STEP; subst.
    constructor.
    unfold res_eq. intros active_skipped LES.
    specialize (seen_accumulate _ _ _ _ _ _ _  RES_EQ _ LES) as SEQ.
    rewrite result_move_blocked in SEQ. auto.
Admitted.
