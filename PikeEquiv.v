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
    (* blocked threads should be equivalent for the next input *)
    (* nothing to say if there is no next input *)
    (BLOCKED: forall nextinp, advance_input inp = Some nextinp -> list_tree_thread code nextinp treeblocked threadblocked),
    pike_inv code (PTS idx treeactive best treeblocked) (PVS inp idx threadactive best threadblocked)
| pikeinv_final:
  forall best,
    pike_inv code (PTS_final best) (PVS_final best).

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
  eapply pikeinv; constructor; try constructor.
  apply tt_eq with (pc_cont:=length c) (pc_end:=length c) (r:=r) (cont:=[]); auto.
  - subst. apply nfa_rep_extend. auto.
  - constructor. replace (length c) with (length c + 0) by auto. rewrite get_prefix. auto.
Qed.


(** * Invariant Preservation  *)
(* For each possible kind of tree, I show that the PikeTree step over that tree corresponds *)
(* to an equivalent step in the PikeVM. This preserves the invariant. *)

Theorem generate_match:
  forall tree gm idx inp code pc b
    (TREESTEP: tree_bfs_step tree gm idx = StepMatch)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b)),
    epsilon_step (pc, gm, b) code inp idx = EpsMatch.
Proof.
  intros tree gm idx inp code pc b TREESTEP TT.
  unfold tree_bfs_step in TREESTEP. destruct tree; inversion TREESTEP. subst. clear TREESTEP.
  inversion TT. subst. remember Match as TMATCH.
  generalize dependent pc_cont. generalize dependent pc_end.
  (* here we have to proceed by induction because there are many ways to get a Match tree *)
  (* it could be the regex epsilon, it could be a continuation, it could be epsilon followed by epsilon etc *)
  induction TREE; intros; subst; try inversion HeqTMATCH.
  - unfold epsilon_step. inversion CONT. subst. inversion NFA. subst.
    rewrite ACCEPT. auto.
  - inversion CONT. inversion ACTION. inversion NFA. subst. eapply IHTREE; eauto.
  - inversion NFA. subst. eapply IHTREE; eauto.
    econstructor; eauto. constructor. auto.
  - inversion CHOICE.
Qed.


Theorem generate_blocked:
  forall tree gm idx inp code pc b nexttree
    (TREESTEP: tree_bfs_step tree gm idx = StepBlocked nexttree)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b)),
  exists nextthread,
    epsilon_step (pc, gm, b) code inp idx = EpsBlocked nextthread /\
      (forall nextinp, advance_input inp = Some nextinp -> tree_thread code nextinp (nexttree,gm) nextthread).
Proof.
  intros tree gm idx inp code pc b nexttree TREESTEP TT.
  unfold tree_bfs_step in TREESTEP. destruct tree; inversion TREESTEP. subst. clear TREESTEP.
  inversion TT. subst. remember (Read c nexttree) as TREAD.
  generalize dependent pc_cont. generalize dependent pc_end.
  induction TREE; intros; subst; try inversion HeqTREAD; subst.
  - inversion CONT. inversion ACTION. inversion NFA. subst. eapply IHTREE; eauto.
  - assert (H: check_read cd inp = CanRead /\ advance_input inp = Some nextinp) by (apply can_read_correct; eauto).
    destruct H as [CHECK ADVANCE]. 
    inversion NFA. subst. exists (pc + 1, gm, CanExit). split.
    + unfold epsilon_step. rewrite CONSUME.
      rewrite CHECK. unfold block_thread. auto.
    + intros nextinp0 H. rewrite ADVANCE in H. inversion H. subst.
      eapply tt_eq; eauto. replace (S pc) with (pc + 1) by lia.
      constructor.
  - inversion NFA. subst. eapply IHTREE; eauto.
    econstructor; eauto. constructor. auto.
  - inversion CHOICE.
Qed.


Theorem generate_choice:
  forall tree1 tree2 gm idx inp code pc b treeactive
    (TREESTEP: tree_bfs_step (Choice tree1 tree2) gm idx = StepActive treeactive)
    (TT: tree_thread code inp (Choice tree1 tree2, gm) (pc, gm, b)),
  exists threadactive,
    epsilon_step (pc, gm, b) code inp idx = EpsActive threadactive /\
      list_tree_thread code inp treeactive threadactive.
Proof.
  intros tree1 tree2 gm idx inp code pc b treeactive TREESTEP TT.
  unfold tree_bfs_step in TREESTEP. inversion TREESTEP. subst. clear TREESTEP.
  inversion TT. subst. remember (Choice tree1 tree2) as TCHOICE.
  generalize dependent pc_cont. generalize dependent pc_end.
  induction TREE; intros; subst; try inversion HeqTCHOICE; subst.
  - inversion CONT. inversion ACTION. inversion NFA. subst. eapply IHTREE; eauto.
  - inversion NFA. subst. exists [(S pc,gm,b);(S end1,gm,b)]. split.
    + unfold epsilon_step. rewrite FORK. auto.
    + constructor.
      * constructor. constructor.
        apply tt_eq with (pc_cont:=pc_cont) (pc_end:=pc_end) (r:=r2) (cont:=cont); auto.
      * apply tt_eq with (pc_cont:=end1) (pc_end:=pc_end) (r:=r1) (cont:=cont); auto.
        admit.
  (* here I can't do a lockstep: the PikeVM takes one more step than the PikeTree, *)
  (* because there is that extra jump instruction. *)
  (* I must revisit my proof to allow a one-to-many (many being 2 I guess) simulation scheme: *)
  (* whenever PikeTree takes a step, PikeVM takes 1 or 2 equivalent steps  *)
  (* another solution could be o change the representation predicate to allow that extra jump *)
  - inversion NFA. subst. eapply IHTREE; eauto.
    econstructor; eauto. constructor. auto.
  (* when the choice comes from a star *)
  - admit.                      (* TODO *)
Admitted.


Theorem generate_active:
  forall tree gm idx inp code pc b treeactive
    (TREESTEP: tree_bfs_step tree gm idx = StepActive treeactive)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b)),
  exists threadactive,
    epsilon_step (pc, gm, b) code inp idx = EpsActive threadactive /\
      list_tree_thread code inp treeactive threadactive.
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
  intros. inversion INV; subst.
  2: { inversion TREESTEP. }
  inversion TREESTEP; subst.
  (* pts final *)
  - exists (PVS_final best). split.
    + inversion ACTIVE.
      destruct (advance_input inp) eqn:ADVANCE.
      * specialize (BLOCKED i eq_refl). inversion BLOCKED. subst. apply pvs_final.
      * apply pvs_end. auto.
    + apply pikeinv_final.
  (* pts_nextchar *)
  - inversion ACTIVE. subst.
    (* the pike vm has two different rules for when we reach the end of input or not *)
    destruct (advance_input inp) as [nextinp|] eqn:ADVANCE.
    + specialize (BLOCKED nextinp eq_refl).
      inversion BLOCKED. subst.
      exists (PVS nextinp (idx+1) ((pc,gm,b)::threadlist) best []). split.
      * apply pvs_nextchar. auto.
      * constructor; auto. intros. constructor.
    + exists (PVS_final best). split.
      * apply pvs_end. auto.
      * admit. (* it should not be possible for PTS to continue while PVS has reached end of input *)
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
    + constructor; auto. intros nextinp H. specialize (BLOCKED nextinp H).
      apply ltt_app; auto. specialize (TT2 nextinp H).
      inversion TT2. subst. constructor; auto. constructor.
Admitted.
