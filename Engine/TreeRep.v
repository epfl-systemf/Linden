Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeTree PikeVM.
From Linden Require Import PikeTreeSeen PikeVMSeen.
From Linden Require Import PikeEquiv PikeSubset.
From Warblre Require Import Base.


(** * Tree Rep Predicate  *)
(* A predicate showing that a tree is represented at a given point in the code *)
(* For a given input and boolean *)
(* the nat is the number of jumps that may be required to compute the final tree *)

Inductive tree_rep: tree -> code -> label -> input -> LoopBool -> nat -> Prop :=
| tr_match:
  forall code pc inp b
    (ACCEPT: get_pc code pc = Some Accept),
    tree_rep Match code pc inp b 0
| tr_jmp:
  forall code pc nextpc inp b t n
    (JMP: get_pc code pc = Some (Jmp nextpc))
    (TR: tree_rep t code nextpc inp b n),
    tree_rep t code pc inp b (S n)
| tr_begin:
  forall code pc inp b t n
    (BEGIN: get_pc code pc = Some BeginLoop)
    (TR: tree_rep t code (S pc) inp CannotExit n),
    tree_rep t code pc inp b n
| tr_choice:
  forall code pc pc1 pc2 inp b t1 t2 n1 n2
    (FORK: get_pc code pc = Some (Fork pc1 pc2))
    (TR1: tree_rep t1 code pc1 inp b n1)
    (TR2: tree_rep t2 code pc2 inp b n2),
    tree_rep (Choice t1 t2) code pc inp b (n1 + n2)
| tr_read:
  forall code pc inp nextinp b cd c t n
    (CONSUME: get_pc code pc = Some (Consume cd))
    (READ: read_char cd inp forward = Some (c, nextinp))
    (TR: tree_rep t code (S pc) nextinp CanExit n),
    tree_rep (Read c t) code pc inp b n
| tr_progress:
  forall code pc nextpc inp t n
    (ENDLOOP: get_pc code pc = Some (EndLoop nextpc))
    (TR: tree_rep t code nextpc inp CanExit n),
    tree_rep (Progress t) code pc inp CanExit n
| tr_open:
  forall code pc gid inp b t n
    (OPEN: get_pc code pc = Some (SetRegOpen gid))
    (TR: tree_rep t code (S pc) inp b n),
    tree_rep (GroupAction (Open gid) t) code pc inp b n
| tr_close:
  forall code pc gid inp b t n
    (CLOSE: get_pc code pc = Some (SetRegClose gid))
    (TR: tree_rep t code (S pc) inp b n),
    tree_rep (GroupAction (Close gid) t) code pc inp b n
| tr_reset:
  forall code pc gidl inp b t n
    (RESET: get_pc code pc = Some (ResetRegs gidl))
    (TR: tree_rep t code (S pc) inp b n),
    tree_rep (GroupAction (Reset gidl) t) code pc inp b n
| tr_readfail:
  forall code pc inp b cd
    (CONSUME: get_pc code pc = Some (Consume cd))
    (READ: read_char cd inp forward = None),
    tree_rep Mismatch code pc inp b 0
| tr_progressfail:
  forall code pc nextpc inp
    (ENDLOOP: get_pc code pc = Some (EndLoop nextpc)),
    tree_rep Mismatch code pc inp CannotExit 0.


(** * Tree Rep Determinism  *)
(* this is essential to allow memoization *)
(* If we end up on the same pc, we represent the same tree *)
(* meaning that we can safely memoize it and cut the lower priority thread *)

Ltac same_instr :=
  match goal with
  | [ H1 : get_pc ?code ?pc = ?i1, H2: get_pc ?code ?pc = ?i2 |- _ ] => rewrite H1 in H2; inversion H2; subst
  end.                                                                                                       

(* Determinism of the tree representation *)
Theorem tree_rep_determ:
  forall code pc inp b t1 t2 n1 n2,
    tree_rep t1 code pc inp b n1 ->
    tree_rep t2 code pc inp b n2 ->
    t1 = t2 /\ n1 = n2.
Proof.
  intros code pc inp b t1 t2 n1 n2 H H0.
  generalize dependent t2. generalize dependent n2.
  induction H; intros.
  - inversion H0; subst; auto; same_instr.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ _ TR) as [EQT EQN].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
  - inversion H1; subst; auto; same_instr.
    specialize (IHtree_rep1 _ _ TR1) as [EQT1 EQN1].
    specialize (IHtree_rep2 _ _ TR2) as [EQT2 EQN2].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr;
      rewrite READ0 in READ; inversion READ; subst.
    specialize (IHtree_rep _ _ TR) as [EQT EQN].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ _ TR) as [EQT EQN].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ _ TR) as [EQT EQN].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ _ TR) as [EQT EQN].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ _ TR) as [EQT EQN].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    rewrite READ0 in READ. inversion READ.
  - inversion H0; subst; auto; same_instr.
Qed.


(** * Relation to actions_rep  *)

(* Actions rep to tree rep *)

(* NOTE: here the induction on ACT only serves when there are jmps. In the other case, IHACT is never needed *)
Theorem actions_tree_rep:
  forall actions code pc n inp b t
    (SUBSET: pike_actions actions)
    (ACT: actions_rep actions code pc n)
    (TREE: bool_tree actions inp b t),
    tree_rep t code pc inp b n.
Proof.
  intros actions code pc n inp b t SUBSET ACT TREE.
  generalize dependent code. generalize dependent n. generalize dependent pc.
  induction TREE; intros.
  (* Match *)
  - remember [] as emp. induction ACT; inversion Heqemp.
    + constructor. auto.
    + eapply tr_jmp; eauto.
  (* Progress *)
  - remember (Acheck strcheck :: cont) as checkcont.
    induction ACT; inversion Heqcheckcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. eapply tr_progress; eauto.
    eapply IHTREE; eauto. pike_subset.
  (* progress fail *)
  - remember (Acheck strcheck :: cont) as checkcont.
    induction ACT; inversion Heqcheckcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. replace n with 0 by admit.
    eapply tr_progressfail; eauto.
  (* close *)
  - remember (Aclose gid :: cont) as closecont.
    induction ACT; inversion Heqclosecont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. eapply tr_close; eauto.
    eapply IHTREE; eauto. pike_subset.
  (* epsilon *)
  - remember (Areg Epsilon :: cont) as epscont.
    induction ACT; inversion Heqepscont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply IHTREE; eauto. pike_subset.
  (* character *)
  - remember (Areg (Regex.Character cd) :: cont) as charcont.
    induction ACT; inversion Heqcharcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply tr_read; eauto.
    eapply IHTREE; eauto. pike_subset.
  (* read fail *)
  - remember (Areg (Regex.Character cd) :: cont) as charcont.
    induction ACT; inversion Heqcharcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    replace n with 0 by admit.
    eapply tr_readfail; eauto.
  (* disjunction *)
  - remember (Areg (Disjunction r1 r2) :: cont) as disjcont.
    induction ACT; inversion Heqdisjcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    replace n with (S n+n) by admit.
    eapply tr_choice; eauto.
    + eapply IHTREE1. pike_subset.
      eapply cons_bc with (pcmid:=end1); try constructor; eauto.
      eapply jump_bc; eauto.
    + eapply IHTREE2; eauto. pike_subset.
      repeat (econstructor; eauto).
  (* sequence *)
  - remember (Areg (Sequence r1 r2) :: cont) as seqcont.
    induction ACT; inversion Heqseqcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply IHTREE; eauto. pike_subset.
    repeat (econstructor; eauto).
  (* quantified, forced *)
  - pike_subset.
  (* quantified, done *)
  - pike_subset.
  (* quantified, free *)
  - destruct plus.
    { pike_subset. }
    simpl in ACT.
    remember (Areg (Quantified greedy 0 +∞ r1) :: cont) as starcont.
    induction ACT; inversion Heqstarcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    destruct greedy; simpl.
    + replace n with (n+n) by admit.
      eapply tr_choice; eauto.
      * eapply tr_begin; eauto.
        eapply tr_reset; eauto.
        eapply IHTREE1; eauto. pike_subset.
        repeat (econstructor; eauto).
      * eapply IHTREE2; eauto. pike_subset.
    + replace n with (n+n) by admit.
      eapply tr_choice; eauto.
      * eapply IHTREE2; eauto. pike_subset.
      * eapply tr_begin; eauto.
        eapply tr_reset; eauto.
        eapply IHTREE1; eauto. pike_subset.
        repeat (econstructor; eauto).
  (* group *)
  - remember (Areg (Group gid r1) :: cont) as groupcont.
    induction ACT; inversion Heqgroupcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply tr_open; eauto.
    eapply IHTREE; eauto. pike_subset.
    repeat (econstructor; eauto).
  (* anchor *)
  - pike_subset.
  (* anchor fail *)
  - pike_subset.
Admitted.

    
      (* my original attempt *)
Theorem actions_tree_rep':
  forall actions code pc n inp b t
    (SUBSET: pike_actions actions)
    (ACT: actions_rep actions code pc n)
    (TREE: bool_tree actions inp b t),
    tree_rep t code pc inp b n.
Proof.
  intros actions code pc n inp b t SUBSET ACT TREE.
  generalize dependent t. generalize dependent inp. generalize dependent b.
  induction ACT; intros.
  (* empty actions *)
  { inversion TREE; subst.
    constructor; auto. }
  (* jump *)
  2: { eapply tr_jmp; eauto. }
  destruct a.
  (* check action *)
  2: { inversion ACTION; subst. inversion TREE; subst.
       - apply IHACT in TREECONT. eapply tr_progress; eauto. pike_subset.
       - replace n with 0 by admit. eapply tr_progressfail; eauto. }
  (* the admit above is a big issue. What's the n for a failed progress? *)
  (* should I go below and compute the n value IF the progress had succeeded? *)
  (* In general, is my computation of n in tree_rep the right one? *)
  (* Am I computing the number of jumps we'll do in this computation
     or the number of jumps in the representation? *)
  (* what if a jump is in a loop? *)

  (* close action *)
  2: { inversion ACTION; subst. inversion TREE; subst.
       apply IHACT in TREECONT. eapply tr_close; eauto. pike_subset. }

  (* Regex action *)
  generalize dependent b. generalize dependent inp. generalize dependent t.
  generalize dependent pcstart. generalize dependent pcmid. generalize dependent n. generalize dependent cont.
  induction r; intros.
  (* epsilon *)
  - inversion ACTION; subst. inversion NFA; subst.
    2: { in_subset. }
    inversion TREE; subst.
    apply IHACT in ISTREE. auto. pike_subset.
  (* character *)
  - inversion ACTION; subst. inversion NFA; subst.
    2: { in_subset. }
    inversion TREE; subst.
    + apply IHACT in TREECONT. eapply tr_read; eauto. pike_subset.
    + replace n with 0 by admit. (* same issue as the progress fail *)
      eapply tr_readfail; eauto.
  (* disjunction *)
  - inversion ACTION; subst. inversion NFA; subst.
    2: { in_subset. }
    inversion TREE; subst.
    replace n with (S n+n) by admit. (* again, issues with n computation *)
    eapply tr_choice; eauto.
    + eapply IHr1 in ISTREE1; eauto.
      * pike_subset.
      * eapply jump_bc; eauto.
      * intros. eapply tr_jmp; eauto.
      * constructor; auto.
    + eapply IHr2 in ISTREE2; eauto.
      * pike_subset.
      * constructor; auto.
  (* Sequence *)
  - inversion ACTION; subst. inversion NFA; subst.
    2: { in_subset. }
    inversion TREE; subst.
    eapply IHr1 in CONT; eauto.
    * pike_subset.
    * econstructor; eauto. econstructor; eauto.
    * intros. eapply IHr2 in TREE0; eauto.
      constructor; eauto.
    * constructor. auto.
  (* Quantified *)
  - destruct delta; [pike_subset|].
    destruct min; [|pike_subset].
    inversion ACTION; subst. inversion NFA; subst.
    2: { in_subset. }
    (* new version *)
    remember (Areg (Quantified greedy 0 +∞ r)) as star.
    remember (star::cont) as starcont.
    induction TREE; subst; try solve [try inversion Hesqtar; inversion Heqstarcont].
    



    (* original version *)
    inversion TREE; subst.
    destruct plus; inversion H1.
    destruct greedy.
    + simpl. replace n with (n+n) by admit.
      eapply tr_choice; eauto.
      2: { apply IHACT in SKIP; eauto. pike_subset. }
      eapply tr_begin; eauto.
      eapply tr_reset; eauto.
      eapply IHr in ISTREE1; eauto.
      { pike_subset. }
      { repeat (econstructor; eauto). }
      2: { constructor; auto. }
      intros. inversion TREE0; subst.
      2: { replace n with 0 by admit. eapply tr_progressfail; eauto. }
      eapply tr_progress; eauto.
      admit.
      (* here I have an issue. My Induction hypothesis is about r::cont, not r*::cont *)
    + admit.                    (* same but lazy *)
  (* lookaround *)
  - pike_subset.
  (* Group *)
  - inversion ACTION; subst. inversion NFA; subst.
    2: { in_subset. }
    inversion TREE; subst.
    eapply tr_open; eauto.
    eapply IHr in TREECONT; eauto.
    * pike_subset.
    * repeat (econstructor; eauto).
    * intros. inversion TREE0; subst.
      eapply tr_close; eauto. eapply IHACT; eauto. pike_subset.
    * constructor; auto.
  (* anchor *)
  - pike_subset.
  (* backref *)
  - pike_subset.
Admitted.
(* an issue with n:
   in actions_rep, the n counts the number of jumps we might see, but not all
   if you have a jump inside an areg for instance, you won't count it,
   it's only counted if it's in-between your actions
   I have no idea how to represent that same n in tree_rep, since the actions are absent
 *)

(* Here, the n I compute in tree_rep could also serve as a measure
   it's the total number of jumps that will be required to execute the tree
   so when the PikeVM does a jump, the PikeTree algorithm does not execute,
   but the number of total jumps has just decreased

   It's also a measure, but not the same.

   Maybe if the theorem above is true we can replace the measure in the invariant?
   We know we have actions rep and bool_tree, so we know we have tree_rep for a given n,
   and we use that n as a measure?

 *)



(** * Correctness of compilation with regards to tree_rep  *)

(* what I would like to know *)
Theorem initialize_tree_rep:
  forall r inp t c endl,
    compile r 0 = (c, endl) ->
    bool_tree [Areg r] inp CanExit t ->
    exists n, tree_rep t c 0 inp CanExit n.
Abort.

Theorem compile_correct_tree_rep:
  forall r c start endl inp b,
    compile r start = (c, endl) ->
    start = List.length prev ->
    tree_rep t (prev ++ c) start 


      Theorem compile_nfa_rep:
  forall r c start endl prev,
    compile r start = (c, endl) ->
    start = List.length prev ->
    nfa_rep r (prev ++ c) start endl.
