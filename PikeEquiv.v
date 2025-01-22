(* Relating the PikeVM smallstep semantics to the Pike Tree smallstep semantics *)

Require Import List Lia.
Import ListNotations.

Require Import Regex Chars Groups.
Require Import Tree Semantics BooleanSemantics.
Require Import NFA PikeTree PikeVM.

(* a tree and a thread are equivalent when they are about to execute the same thing *)
(* this means when the tree represents a given regex and continuation, *)
(* the thread is at a pc that will execute the nfa of that same regex and continuation *)
Inductive tree_thread (code:code) (inp:input): (tree * group_map) -> thread -> Prop :=
| tt_eq:
  forall tree gm pc b pc_cont pc_end r cont
    (TREE: bool_tree r cont inp b tree)
    (NFA: nfa_rep r code pc pc_cont)
    (CONT: continuation_rep cont code pc_cont pc_end),
    tree_thread code inp (tree, gm) (pc, gm, b).

(* the initial active thread and the initial active tree are related with the invariant *)
Lemma initial_tree_thread:
  forall r code tree inp
    (COMPILE: compilation r = code)
    (TREE: bool_tree r [] inp CanExit tree),
    tree_thread code inp (tree, empty_group_map) (0, empty_group_map, CanExit).
Proof.
  intros r code tree inp COMPILE TREE.
  unfold compilation in COMPILE. destruct (compile r 0) as [c fresh] eqn:COMP.
  apply compile_nfa_rep with (prev := []) in COMP as REP; auto. simpl in REP.
  apply fresh_correct in COMP. simpl in COMP. subst.
  subst. eapply tt_eq with (pc_cont := length c) (pc_end := length c); eauto.
  - simpl in REP. apply nfa_rep_extend. auto.
  - constructor. replace (length c) with (length c + 0) by auto. rewrite get_prefix. auto.
Qed.

(* lifting the equivalence predicate to lists *)
Inductive list_tree_thread (code:code) (inp:input) : list (tree * group_map) -> list thread -> Prop :=
| ltt_nil: list_tree_thread code inp [] []
| ltt_cons:
  forall treelist threadlist tree gm pc b
    (LTT: list_tree_thread code inp treelist threadlist)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b)),
    list_tree_thread code inp ((tree,gm)::treelist) ((pc,gm,b)::threadlist).

Lemma ltt_app:
  forall code inp tl1 tl2 vl1 vl2
    (LTT1: list_tree_thread code inp tl1 vl1)
    (LTT2: list_tree_thread code inp tl2 vl2),
    list_tree_thread code inp (tl1 ++ tl2) (vl1 ++ vl2).
Proof.
  intros. induction LTT1; auto. simpl. constructor; auto.
Qed.

(* lifting the equivalence predicate to pike states *)
Inductive pike_inv (code:code): pike_tree_state -> pike_vm_state -> Prop :=
| pikeinv:
  forall inp idx treeactive treeblocked threadactive threadblocked best
    (ACTIVE: list_tree_thread code inp treeactive threadactive)
    (* below is not correct: they must be equivalent for the next input *)
    (BLOCKED: list_tree_thread code inp treeblocked threadblocked),
    pike_inv code (PTS idx treeactive best treeblocked) (PVS inp idx threadactive best threadblocked).

(* the initial states of both smallstep semantics are related with the invariant *)
Lemma initial_pike_inv:
  forall r inp tree code
    (TREE: bool_tree r [] inp CanExit tree)
    (COMPILE: compilation r = code),
    pike_inv code (pike_tree_initial_state tree) (pike_vm_initial_state inp).
Proof.
  intros r inp tree code TREE COMPILE.
  unfold compilation in COMPILE. destruct (compile r 0) as [c fresh] eqn:COMP.
  apply compile_nfa_rep with (prev := []) in COMP as REP; auto. simpl in REP.
  apply fresh_correct in COMP. simpl in COMP. subst.
  constructor; constructor; try constructor.
  apply tt_eq with (pc_cont:=length c) (pc_end:=length c) (r:=r) (cont:=[]); auto.
  - subst. apply nfa_rep_extend. auto.
  - constructor. replace (length c) with (length c + 0) by auto. rewrite get_prefix. auto.
Qed.


(** * Invariant Preservation  *)

Theorem generate_active:
  forall tree gm idx inp code pc b treeactive
    (TREESTEP: tree_bfs_step tree gm idx = StepActive treeactive)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b)),
  exists threadactive,
    epsilon_step (pc, gm, b) code inp idx = EpsActive threadactive /\
      list_tree_thread code inp treeactive threadactive.
Proof.
Admitted.

Theorem generate_match:
  forall tree gm idx inp code pc b
    (TREESTEP: tree_bfs_step tree gm idx = StepMatch)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b)),
    epsilon_step (pc, gm, b) code inp idx = EpsMatch.
Proof.
  intros tree gm idx inp code pc b TREESTEP TT.
  unfold tree_bfs_step in TREESTEP. destruct tree; inversion TREESTEP. subst.
  inversion TT. subst. inversion TREE; subst.
  - unfold epsilon_step. inversion CONT. subst. inversion NFA. subst.
    rewrite ACCEPT. auto.
  (* issue: there are many ways to obtain a match tree. maybe it's epsilon, maybe epsilon;epsilon ... *)
  (* these all have the same tree. not sure how to proceed for now *)
  - admit.
  - admit.
  - admit.
Admitted.

(* TODO: there is too much info in EpsBlocked, StepMatch etc. Makes the theorem statements no very convenient *)
Theorem generate_blocked:
  forall tree gm idx inp code pc b nexttree
    (TREESTEP: tree_bfs_step tree gm idx = StepBlocked nexttree)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b)),
  exists nextthread,
    epsilon_step (pc, gm, b) code inp idx = EpsBlocked nextthread /\
      tree_thread code inp (nexttree,gm) nextthread.
Proof.
Admitted.


Theorem invariant_preservation:
  forall code pts1 pts2 pvs1
    (INV: pike_inv code pts1 pvs1)
    (TREESTEP: pike_tree_step pts1 pts2),
  exists pvs2,
    pike_vm_step code pvs1 pvs2 /\
      pike_inv code pts2 pvs2.
Proof.
  intros. inversion INV. subst.
  inversion TREESTEP; subst.
  (* pts_nextchar *)
  - inversion ACTIVE. subst.
    (* the pike vm has two different rules for when we reach the end of input or not *)
    destruct (advance_input inp) as [nextinp|] eqn:ADVANCE.
    + exists (PVS nextinp (idx+1) threadblocked best []). split.
      * apply pvs_nextchar. auto.
      * constructor; auto.
        ** admit.               (* we only have the eq for the previous input *)
        ** admit.               (* same. ut for best, maybe we could only export the group_map *)
    + exists (PVS inp idx [] best threadblocked). split.
      * apply pvs_end. auto.
      * admit.                  (* here there is an issue: the pike tree step loops but keeps increasing its index *)
  (* pts_active *)
  - inversion ACTIVE. subst. rename t into tree.
    eapply generate_active in TT as [newthreads [EPS LTT2]]; eauto.
    exists (PVS inp idx (newthreads++threadlist) best threadblocked). split.
    + apply pvs_active. auto.
    + apply pikeinv; auto. apply ltt_app; auto.
  (* pts_match *)
  - inversion ACTIVE. subst. rename t into tree.
    eapply generate_match in TT; eauto.
    exists (PVS inp idx [] (Some gm) threadblocked). split.
    + apply pvs_match. auto.
    + constructor; auto. constructor.
  (* pts_blocked *)
  - inversion ACTIVE. subst. rename t into tree.
    eapply generate_blocked in TT as [nextt [EPS TT2]]; eauto.
    exists (PVS inp idx threadlist best (threadblocked ++ [nextt])). split.
    + apply pvs_blocked. auto.
    + constructor; auto. apply ltt_app; auto.
      inversion TT2. subst. constructor; auto. constructor.
Admitted.
