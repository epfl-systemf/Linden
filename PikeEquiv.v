(* Relating the PikeVM smallstep semantics to the Pike Tree smallstep semantics *)

Require Import List Lia.
Import ListNotations.

Require Import Regex Chars Groups.
Require Import Tree Semantics BooleanSemantics.
Require Import NFA PikeTree PikeVM.

(* a tree and a thread are equivalent when they are about to execute the same thing *)
(* this means when the tree represents a given regex and continuation, *)
(* the thread is at a pc that will execute the nfa of that same regex and continuation *)
Inductive tree_thread (code:code) (inp:input): (tree * group_map) -> LoopBool -> thread -> Prop :=
| tt_eq:
  forall tree gm pc b pc_cont pc_end r cont
    (TREE: bool_tree r cont inp b tree)
    (NFA: nfa_rep r code pc pc_cont)
    (CONT: continuation_rep cont code pc_cont pc_end),
    tree_thread code inp (tree, gm) b (pc, gm, b).

(* the initial active thread and the initial active tree are related with the invariant *)
Lemma initial_tree_thread:
  forall r code tree inp
    (COMPILE: compilation r = code)
    (TREE: bool_tree r [] inp CanExit tree),
    tree_thread code inp (tree, empty_group_map) CanExit (0, empty_group_map, CanExit).
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
    (TT: tree_thread code inp (tree, gm) b (pc, gm, b)),
    list_tree_thread code inp ((tree,gm)::treelist) ((pc,gm,b)::threadlist).

(* relating the best matches *)
Inductive best_eq (inp:input) : option leaf -> option thread -> Prop :=
| best_none: best_eq inp None None
| best_some:
  forall gm pc b, best_eq inp (Some (inp, gm)) (Some (pc, gm, b)).

(* lifting the equivalence predicate to pike states *)
Inductive pike_inv (code:code): pike_tree_state -> pike_vm_state -> Prop :=
| pikeinv:
  forall inp idx treeactive treebest treeblocked threadactive threadbest threadblocked
    (ACTIVE: list_tree_thread code inp treeactive threadactive)
    (BEST: best_eq inp treebest threadbest)
    (BLOCKED: list_tree_thread code inp treeblocked threadblocked),
    pike_inv code (PTS idx treeactive treebest treeblocked) (PVS inp idx threadactive threadbest threadblocked).

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
