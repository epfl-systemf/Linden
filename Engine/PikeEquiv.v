(* Relating the PikeVM smallstep semantics to the Pike Tree smallstep semantics *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeTree PikeVM PikeSubset.
From Warblre Require Import Base.

(** * Simulation Invariant  *)

(* a tree and a thread are equivalent when they are about to execute the same thing *)
(* this means when the tree represents a given list of actions, *)
(* the thread is at a pc that will execute the nfa of that same list of actions *)
(* the nat is a measure of stuttering steps in the continuation *)
Inductive tree_thread (code:code) (inp:input) : (tree * group_map) -> thread -> nat -> Prop :=
| tt_eq:
  forall tree gm pc b actions n
    (TREE: bool_tree actions inp b tree)
    (CONT: actions_rep actions code pc n)
    (SUBSET: pike_actions actions),
    tree_thread code inp (tree, gm) (pc, gm, b) n
| tt_reset:
  forall tree gm pc b n gidl
    (TT: tree_thread code inp (tree,GroupMap.reset gidl gm) (pc+1,GroupMap.reset gidl gm,b) n)
    (RESET: get_pc code pc = Some (ResetRegs gidl)),
    tree_thread code inp (GroupAction (Reset gidl) tree,gm) (pc,gm,b) n
| tt_begin:
  forall tree gm pc b n
    (TT: tree_thread code inp (tree,gm) (pc+1,gm,CannotExit) n)
    (BEGIN: get_pc code pc = Some BeginLoop),
    tree_thread code inp (tree,gm) (pc,gm,b) (S n).
    

(* the initial active thread and the initial active tree are related with the invariant *)
Lemma initial_tree_thread:
  forall r code tree inp
    (COMPILE: compilation r = code)
    (TREE: bool_tree [Areg r] inp CanExit tree)
    (SUBSET: pike_regex r),
    tree_thread code inp (tree, GroupMap.empty) (0, GroupMap.empty, CanExit) 0.
Proof.
  intros r code tree inp COMPILE TREE SUBSET.
  unfold compilation in COMPILE. destruct (compile r 0) as [c fresh] eqn:COMP.
  apply compile_nfa_rep with (prev := []) in COMP as REP; auto. simpl in REP.
  apply fresh_correct in COMP. simpl in COMP. subst.
  subst. eapply tt_eq; eauto.
  2: { repeat (constructor; auto). }
  apply cons_bc with (pcmid := length c).
  - constructor. apply nfa_rep_extend. auto.
  - constructor. replace (length c) with (length c + 0) by auto. rewrite get_prefix. auto.
Qed.

(* lifting the equivalence predicate to lists *)
(* the list of nat is the measure, contains the number of stuttering steps for each thread *)
Inductive list_tree_thread (code:code) (inp:input) : list (tree * group_map) -> list thread -> list nat -> Prop :=
| ltt_nil: list_tree_thread code inp [] [] []
| ltt_cons:
  forall treelist threadlist tree gm pc b measurelist n
    (LTT: list_tree_thread code inp treelist threadlist measurelist)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b) n),
    list_tree_thread code inp ((tree,gm)::treelist) ((pc,gm,b)::threadlist) (n::measurelist).

Lemma ltt_app:
  forall code inp tl1 tl2 vl1 vl2 ml1 ml2
    (LTT1: list_tree_thread code inp tl1 vl1 ml1)
    (LTT2: list_tree_thread code inp tl2 vl2 ml2),
    list_tree_thread code inp (tl1 ++ tl2) (vl1 ++ vl2) (ml1 ++ ml2).
Proof.
  intros. induction LTT1; auto. simpl. econstructor; eauto.
Qed.


(* lifting the equivalence predicate to pike states, to get the full invariant *)
Inductive pike_inv (code:code): pike_tree_state -> pike_vm_state -> nat -> Prop :=
| pikeinv:
  forall inp treeactive treeblocked threadactive threadblocked best measureactive measureblocked n
    (ACTIVE: list_tree_thread code inp treeactive threadactive measureactive)
    (* blocked threads should be equivalent for the next input *)
    (* nothing to say if there is no next input *)
    (BLOCKED: forall nextinp, advance_input inp forward = Some nextinp -> list_tree_thread code nextinp treeblocked threadblocked measureblocked)
    (* these two properties are needed to ensure the two algorithms stop at he same time *)
    (ENDVM: advance_input inp forward = None -> threadblocked = [])
    (ENDTREE: advance_input inp forward = None -> treeblocked = [])
    (* the measure is simply the measure of the top priority thread *)
    (MEASURE: n = hd 0 (measureactive++measureblocked)),
    pike_inv code (PTS inp treeactive best treeblocked) (PVS inp threadactive best threadblocked) n
| pikeinv_final:
  forall best,
    pike_inv code (PTS_final best) (PVS_final best) 0.

(** * Invariant Initialization  *)

(* the initial states of both smallstep semantics are related with the invariant *)
Lemma initial_pike_inv:
  forall r inp tree code
    (TREE: bool_tree [Areg r] inp CanExit tree)
    (COMPILE: compilation r = code)
    (SUBSET: pike_regex r),
    pike_inv code (pike_tree_initial_state tree inp) (pike_vm_initial_state inp) 0.
Proof.
  intros r inp tree code TREE COMPILE SUBSET.         
  unfold compilation in COMPILE. destruct (compile r 0) as [c fresh] eqn:COMP.
  apply compile_nfa_rep with (prev := []) in COMP as REP; auto. simpl in REP.
  apply fresh_correct in COMP. simpl in COMP. subst.
  eapply pikeinv; econstructor.
  { constructor. }
  apply tt_eq with (actions:=[Areg r]); auto.
  2: { constructor; constructor; auto. }
  apply cons_bc with (pcmid:=length c).
  - constructor. apply nfa_rep_extend. auto. 
  - constructor. replace (length c) with (length c + 0) by auto. rewrite get_prefix. auto.
Qed.


(** * Stuttering  *)
(* There are a few cases where the PikeVM takes more steps than the Pike Tree. *)
(* These are stutter steps. *)
(* They correspond to
   - being at a Jmp instruction, inserted for a disjunction
   - being at a BeginLoop instruction, inserted for a quantifier
 *)

(* With the definitions below, we provide ways to kow when is a state going to stutter *)

(* returns true if that state will stutter *)
(* or if we are at an unsupported feature *)
Definition stutters (pc:label) (code:code) : bool :=
  match get_pc code pc with
  | Some (Jmp _) => true
  | Some BeginLoop => true
  | Some KillThread => true
  | _ => false
  end.

Lemma does_stutter:
  forall pc code, stutters pc code = true ->
             get_pc code pc = Some BeginLoop \/ (exists next, get_pc code pc = Some (Jmp next)) \/ get_pc code pc = Some KillThread.
Proof.
  unfold stutters. intros. destruct (get_pc code pc); try destruct b; inversion H; eauto.
Qed.

Lemma doesnt_stutter_jmp:
  forall pc code next, stutters pc code = false -> get_pc code pc = Some (Jmp next) -> False.
Proof.
  unfold stutters, not. intros. destruct (get_pc code pc); try destruct b; inversion H0. inversion H.
Qed.

Lemma doesnt_stutter_begin:
  forall pc code, stutters pc code = false -> get_pc code pc = Some BeginLoop -> False.
Proof.
  unfold stutters, not. intros. destruct (get_pc code pc); try destruct b; inversion H0. inversion H.
Qed.

Lemma doesnt_stutter_kill:
  forall pc code, stutters pc code = false -> get_pc code pc = Some KillThread -> False.
Proof.
  unfold stutters, not. intros. destruct (get_pc code pc); try destruct b; inversion H0. inversion H.
Qed.

Ltac no_stutter := 
  match goal with
  | [ H : stutters ?pc ?code = false, H1: get_pc ?code ?pc = Some (Jmp _) |- _ ] => exfalso; eapply doesnt_stutter_jmp; eauto
  | [ H : stutters ?pc ?code = false, H1: get_pc ?code ?pc = Some (BeginLoop) |- _ ] => exfalso; eapply doesnt_stutter_begin; eauto
  | [ H : stutters ?pc ?code = false, H1: get_pc ?code ?pc = Some (KillThread) |- _ ] => exfalso; eapply doesnt_stutter_kill; eauto
  end.

Ltac stutter :=
  match goal with
  | [ H : stutters ?pc ?code = true, H1: get_pc ?code ?pc = Some _ |- _ ] =>
      try solve[unfold stutters in H; rewrite H1 in H; inversion H]
  end.

Ltac invert_rep :=
   match goal with
   | [ H : actions_rep (Areg _ :: _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep (Aclose _ :: _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep (Acheck _ :: _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep [] _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep (Areg _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep (Aclose _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep (Acheck _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Epsilon) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Regex.Character _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Disjunction _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Sequence _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Quantified _ _ _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Group _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | _ => try no_stutter
   end.


(** * Invariant Preservation  *)

(* generate lemmas: *)
(* For each possible kind of tree, I show that the PikeTree step over that tree corresponds *)
(* to an equivalent step in the PikeVM. This preserves the invariant. *)
(* These lemmas discard the stuttering steps by preventing the current pc being at a Jmp instruction *)

Theorem generate_match:
  forall tree gm inp code pc b n
    (TREESTEP: tree_bfs_step tree gm (idx inp) = StepMatch)
    (NOSTUTTER: stutters pc code = false)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b) n),
    epsilon_step (pc, gm, b) code inp = EpsMatch.
Proof.
  intros tree gm inp code pc b n TREESTEP NOSTUTTER TT.
  unfold tree_bfs_step in TREESTEP. destruct tree; inversion TREESTEP. subst. clear TREESTEP.
  inversion TT; subst; try no_stutter.
  remember Match as TMATCH.
  (* here we have to proceed by induction because there are many ways to get a Match tree *)
  (* it could be epsilon, it could be epsilon followed by epsilon etc *)
  induction TREE; intros; subst; try inversion HeqTMATCH.
  - simpl. repeat invert_rep.
    rewrite ACCEPT. auto.
  - repeat invert_rep. pike_subset.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    repeat (econstructor; eauto). pike_subset.
  - repeat invert_rep.
  - destruct greedy; inversion CHOICE.
 Qed.


Theorem generate_blocked:
  forall tree gm inp code pc b nexttree n
    (TREESTEP: tree_bfs_step tree gm (idx inp) = StepBlocked nexttree)
    (NOSTUTTER: stutters pc code = false)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b) n),
    epsilon_step (pc,gm,b) code inp = EpsBlocked (pc+1,gm,CanExit) /\
      (forall nextinp, advance_input inp forward = Some nextinp -> tree_thread code nextinp (nexttree,gm) (pc+1,gm,CanExit) n) /\
      exists nextinp, advance_input inp forward = Some nextinp.
Proof.
  intros tree gm inp code pc b nexttree n TREESTEP NOSTUTTER TT.
  unfold tree_bfs_step in TREESTEP. destruct tree; inversion TREESTEP. subst. clear TREESTEP.
  inversion TT; subst; try no_stutter.
  remember (Read c nexttree) as TREAD.
  induction TREE; intros; subst; try inversion HeqTREAD; subst.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
  - assert (CHECK: check_read cd inp forward = CanRead /\ advance_input inp forward = Some nextinp) by (apply can_read_correct; eauto).
    destruct CHECK as [CHECK ADVANCE].
    repeat invert_rep. split; try split; eauto.
    + simpl. rewrite CONSUME. rewrite CHECK. auto.
    + intros. rewrite ADVANCE in H. inversion H. subst.
      eapply tt_eq; eauto.
      2: { pike_subset. }
      replace (pc + 1) with (S pc) by lia. eauto.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    repeat (econstructor; eauto). pike_subset.
  - repeat invert_rep. 
  - destruct greedy; inversion CHOICE.
Qed.


Theorem generate_open:
  forall gid tree gm inp code pc b n
    (TT: tree_thread code inp (GroupAction (Open gid) tree, gm) (pc, gm, b) n)
    (NOSTUTTER: stutters pc code = false),
    epsilon_step (pc, gm, b) code inp = EpsActive [(pc + 1, GroupMap.open (idx inp) gid gm, b)] /\
      tree_thread code inp (tree,GroupMap.open (idx inp) gid gm) (pc + 1, GroupMap.open (idx inp) gid gm, b) n.
Proof.
  intros gid tree gm inp code pc b n TT NOSTUTTER.
  inversion TT; subst; try invert_rep.
  remember (GroupAction (Open gid) tree) as TOPEN.
  induction TREE; intros; subst; try inversion HeqTOPEN; subst.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    repeat (econstructor; eauto). pike_subset.
  - repeat invert_rep.
  - destruct greedy; inversion CHOICE.
  - repeat invert_rep. simpl. rewrite OPEN. split; auto.
    eapply tt_eq; eauto.
    2: { pike_subset. }
    replace (pc+1) with (S pc) by lia. 
    apply cons_bc with (pcmid:=end1); repeat (econstructor; eauto).
Qed.



Theorem generate_close:
  forall gid tree gm inp code pc b n
    (TT: tree_thread code inp (GroupAction (Close gid) tree, gm) (pc, gm, b) n)
    (NOSTUTTER: stutters pc code = false),
    epsilon_step (pc, gm, b) code inp = EpsActive [(pc + 1, GroupMap.close (idx inp) gid gm, b)] /\
      tree_thread code inp (tree,GroupMap.close (idx inp) gid gm) (pc + 1, GroupMap.close (idx inp) gid gm, b) n.
Proof.
  intros gid tree gm inp code pc b n TT NOSTUTTER.
  inversion TT; subst; try no_stutter.
  remember (GroupAction (Close gid) tree) as TCLOSE.
  induction TREE; intros; subst; try inversion HeqTCLOSE; subst.
  - repeat invert_rep. simpl. rewrite CLOSE. pike_subset.
    econstructor; eauto. replace (pc + 1) with (S pc) by lia. eauto.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    repeat (econstructor; eauto). pike_subset.
  - repeat invert_rep.
  - destruct greedy; inversion CHOICE.
Qed.


Theorem no_tree_reset:
  (* A tree corresponding to some actions cannot start with ResetGroups *)
  forall gidl tree inp actions b,
    pike_actions actions ->
    bool_tree actions inp b (GroupAction (Reset gidl) tree) -> False.
Proof.
  intros gidl tree inp actions b PIKE H.
  remember (GroupAction (Reset gidl) tree) as TRESET.
  induction H; inversion HeqTRESET; subst; auto.
  - pike_subset.
  - apply IHbool_tree; auto. pike_subset.
  - pike_subset.
  - apply IHbool_tree; auto. pike_subset.
  - destruct greedy; inversion CHOICE.
Qed.

Corollary generate_reset:  
  forall gidl tree inp code pc b gm n
    (TT: tree_thread code inp (GroupAction (Reset gidl) tree, gm) (pc,gm,b) n)
    (NOSTUTTER: stutters pc code = false),
    epsilon_step (pc,gm,b) code inp = EpsActive [(pc+1, GroupMap.reset gidl gm, b)] /\
      tree_thread code inp (tree,GroupMap.reset gidl gm) (pc+1, GroupMap.reset gidl gm, b) n.
Proof.
  intros.
  inversion TT; subst.
  - exfalso. eapply no_tree_reset; eauto.
  - simpl. rewrite RESET. split; auto.
  - exfalso. eapply doesnt_stutter_begin; eauto.
Qed.

Theorem generate_mismatch:
  forall gm inp code pc b n
    (TT: tree_thread code inp (Mismatch, gm) (pc, gm, b) n)
    (NOSTUTTER: stutters pc code = false),
    epsilon_step (pc, gm, b) code inp = EpsActive [].
Proof.
  intros gm inp code pc b n TT NOSTUTTER.
  inversion TT; subst; try no_stutter.
  remember (Mismatch) as TMIS.
  induction TREE; intros; subst; try inversion HeqTMIS; subst.
  - repeat invert_rep. simpl. rewrite END. auto.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
  - assert (CHECK: check_read cd inp forward = CannotRead) by (apply cannot_read_correct; auto).
    repeat invert_rep. simpl. rewrite CONSUME. rewrite CHECK. auto.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    repeat (econstructor; eauto). pike_subset.
  - pike_subset.
  - destruct greedy; inversion CHOICE.
  - pike_subset.
Qed.

Theorem generate_checkpass:
  forall tree gm inp code pc b n
    (TT: tree_thread code inp (Progress tree, gm) (pc, gm, b) n)
    (NOSTUTTER: stutters pc code = false),
    exists nextpc, epsilon_step (pc, gm, b) code inp = EpsActive [(nextpc,gm,CanExit)] /\
      tree_thread code inp (tree,gm) (nextpc,gm,CanExit) n.
Proof.
  intros tree gm inp code pc b n TT NOSTUTTER.
  inversion TT; subst; try no_stutter.
  remember (Progress tree) as TPASS.
  induction TREE; intros; subst; try inversion HeqTPASS; subst.
  - repeat invert_rep. pike_subset. simpl. exists pcmid.
    rewrite END. split; auto. econstructor; eauto.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    repeat (econstructor; eauto). pike_subset.
  - pike_subset.
  - destruct greedy; inversion CHOICE.
Qed.


Theorem generate_choice:
  forall tree1 tree2 gm inp code pc b treeactive n
    (TREESTEP: tree_bfs_step (Choice tree1 tree2) gm (idx inp) = StepActive treeactive)
    (NOSTUTTER: stutters pc code = false)
    (TT: tree_thread code inp (Choice tree1 tree2, gm) (pc, gm, b) n),
  exists threadactive measure,
    epsilon_step (pc, gm, b) code inp = EpsActive threadactive /\
      list_tree_thread code inp treeactive threadactive measure.
Proof.
  intros tree1 tree2 gm inp code pc b treeactive n TREESTEP NOSTUTTER TT.
  unfold tree_bfs_step in TREESTEP. inversion TREESTEP. subst. clear TREESTEP.
  inversion TT; subst; try no_stutter.
  remember (Choice tree1 tree2) as TCHOICE.
  induction TREE; intros; subst; try inversion HeqTCHOICE; subst.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
  - repeat invert_rep. exists [(S pc,gm,b);(S end1,gm,b)]. exists [S n; n]. split.
  (* here in the first element of the list we introduced an extra stuttering step, hence the (S n) measure *)
    + unfold epsilon_step. rewrite FORK. auto.
    + constructor.
      * constructor. constructor.
        apply tt_eq with (actions:=Areg r2::cont); auto.
        2: { pike_subset. }
        repeat (econstructor; eauto).
      * apply tt_eq with (actions:=Areg r1::cont); auto.
        2: { pike_subset. }
        eapply cons_bc with (pcmid:=end1).
        ** constructor; auto.
        ** eapply jump_bc; eauto.
  - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    repeat (econstructor; eauto). pike_subset.
  - repeat invert_rep.
  - (* when the choice comes from a star *)
    repeat invert_rep. destruct greedy; inversion CHOICE; subst; destruct plus; inversion H1.
    +                           (* greedy star *)
      simpl. rewrite FORK. exists [(S pc, gm, b); (S end1, gm, b)]. exists [S n; n]. split; auto.
      econstructor.
      * econstructor. constructor.
        apply tt_eq with (actions:=cont); auto. pike_subset.
      * apply tt_begin; auto.
        replace (S (S pc)) with (S pc +1) in RESET by lia.
        apply tt_reset; auto.
        apply tt_eq with (actions:=Areg r1 :: Acheck(inp)::Areg(Quantified true 0 +∞ r1)::cont); auto.
        2: { pike_subset. }
        apply cons_bc with (pcmid:=end1).
        { constructor. replace (S pc+1+1) with (S (S (S pc))) by lia. auto. }
        repeat (econstructor; eauto).
        replace (S (S pc)) with (S pc + 1) by lia. auto.
    +                           (* lazy star *)
      simpl. rewrite FORK. exists [(S end1, gm, b); (S pc, gm, b)]. exists [n; S n]. split; auto.
      econstructor.
      * constructor. constructor. apply tt_begin; auto.
        replace (S (S pc)) with (S pc + 1) in RESET by lia.
        apply tt_reset; auto.
        apply tt_eq with (actions:=Areg r1 :: Acheck(inp)::Areg(Quantified false 0 +∞ r1)::cont); auto.
        2: { pike_subset. }
        apply cons_bc with (pcmid:=end1).
        { constructor. replace (S pc+1+1) with (S (S (S pc))) by lia. auto. }
        repeat (econstructor; eauto).
        replace (S (S pc)) with (S pc + 1) by lia. auto.
      * apply tt_eq with (actions:=cont); auto. pike_subset.
Qed.


(* next we combine the generate lemmas together, for the general non-stuttering case *)
Theorem generate_active:
  forall tree gm inp code pc b treeactive n
    (TREESTEP: tree_bfs_step tree gm (idx inp) = StepActive treeactive)
    (NOSTUTTER: stutters pc code = false)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b) n),
  exists threadactive measure,
    epsilon_step (pc, gm, b) code inp = EpsActive threadactive /\
      list_tree_thread code inp treeactive threadactive measure.
Proof.
  intros tree gm inp code pc b treeactive n TREESTEP NOSTUTTER TT.
  destruct tree; simpl in TREESTEP; inversion TREESTEP; subst.
  - eapply generate_mismatch in TT; auto. exists []. exists []. split; eauto. constructor.
  - eapply generate_choice; eauto.
  - inversion TT; subst; try no_stutter.
    eapply subset_semantics in TREE as SUBSETTREE; auto.
    inversion SUBSETTREE.
  - eapply generate_checkpass in TT as [nextpc [STEP EQ]]; auto.
    exists [(nextpc,gm,CanExit)]. exists [n]. split; eauto.
    constructor; auto. constructor.
  - inversion TT; subst; try no_stutter.
    eapply subset_semantics in TREE as SUBSETTREE; auto.
    inversion SUBSETTREE.
  - destruct g.
    + eapply generate_open in TT as [STEP EQ]; auto.
      exists [(pc+1,GroupMap.open (idx inp) g gm,b)]. exists [n]. split; eauto.
      constructor; auto. constructor.
    + eapply generate_close in TT as [STEP EQ]; auto.
      exists [(pc+1,GroupMap.close (idx inp) g gm,b)]. exists [n]. split; eauto.
      constructor; auto. constructor.
    + eapply generate_reset in TT as [STEP EQ]; auto.
      exists [(pc + 1, GroupMap.reset gl gm, b)]. exists [n]. split; eauto.
      constructor; auto. constructor.
  - inversion TT; subst; try no_stutter.
    eapply subset_semantics in TREE as SUBSETTREE; auto.
    inversion SUBSETTREE.
  - inversion TT; subst; try no_stutter.
    eapply subset_semantics in TREE as SUBSETTREE; auto.
    inversion SUBSETTREE.
Qed.

(* TODO: simplify/automate this proof *)
(* in the case where we are at a stuttering step, we show that we still preserve the invariant and decrease the measure *)
Theorem stutter_step:
  forall tree gm inp code pc b n
    (TT: tree_thread code inp (tree,gm) (pc,gm,b) n)
    (STUTTER: stutters pc code = true),
  exists nextpc nextb m,
    epsilon_step (pc,gm,b) code inp = EpsActive [(nextpc,gm,nextb)] /\
      tree_thread code inp (tree,gm) (nextpc,gm,nextb) m /\
      n = S m.
Proof.
  intros tree gm inp code pc b n TT STUTTER.
  inversion TT; subst.
  (* reset is not stuttering *)
  2: { unfold stutters in STUTTER. rewrite RESET in STUTTER. inversion STUTTER. }
  (* at a beginloop instruction *)
  2: { exists (pc + 1). exists CannotExit. exists n0. split; try split; auto.
       simpl. rewrite BEGIN. auto. }
  (* at a jmp instruction *)
  generalize dependent pc. generalize dependent n.
  induction TREE; intros.
  - invert_rep. stutter.
    exists pcstart. exists b. exists n0. split; try split; try lia.
    + simpl. rewrite JMP. auto.
    + apply tt_eq with (actions:=[]); try constructor; auto.
  - invert_rep.
    { invert_rep. stutter. }
    exists pcstart. exists CanExit. exists n0. split; try split; try lia.
    + simpl. rewrite JMP. auto.
    + apply tt_eq with (actions:=Acheck strcheck::cont); try constructor; auto; pike_subset.
  - invert_rep.
    { invert_rep. stutter. }
    exists pcstart. exists CannotExit. exists n0. split; try split; try lia.
    + simpl. rewrite JMP. auto.
    + apply tt_eq with (actions:=Acheck strcheck::cont); try constructor; auto; pike_subset.
  - invert_rep.
    { invert_rep. stutter. }
    exists pcstart. exists b. exists n0. split; try split; try lia.
    + simpl. rewrite JMP. auto.
    + apply tt_eq with (actions:=Aclose gid::cont); try constructor; auto; pike_subset.
  - invert_rep.
    + invert_rep. invert_rep; try in_subset.
      eapply IHTREE; eauto. pike_subset.
    + exists pcstart. exists b. exists n0. split; try split; try lia.
      * simpl. rewrite JMP. auto.
      * apply tt_eq with (actions:=Areg Epsilon :: cont); try constructor; auto; pike_subset.
  - invert_rep.
    { invert_rep. invert_rep; try in_subset; try stutter. }
    exists pcstart. exists b. exists n0. split; try split; try lia.
    + simpl. rewrite JMP. auto.
    + apply tt_eq with (actions:=Areg (Regex.Character cd) :: cont); try constructor; auto; pike_subset.
      eapply tree_char; eauto.
  - invert_rep.
    { invert_rep. invert_rep; try in_subset; try stutter. }
    exists pcstart. exists b. exists n0. split; try split; try lia.
    + simpl. rewrite JMP. auto.
    + apply tt_eq with (actions:=Areg (Regex.Character cd) :: cont); try constructor; auto; pike_subset.
  - invert_rep.
    { invert_rep. invert_rep; try in_subset; try stutter. }
    exists pcstart. exists b. exists n0. split; try split; try lia.
    * simpl. rewrite JMP. auto.
    * apply tt_eq with (actions:=Areg (Disjunction r1 r2) :: cont); try constructor; auto; pike_subset.
  - invert_rep.
    + invert_rep. invert_rep; try in_subset.
      eapply IHTREE; eauto. pike_subset.
      repeat (econstructor; eauto).
    + exists pcstart. exists b. exists n0. split; try split; try lia.
      * simpl. rewrite JMP. auto.
      * apply tt_eq with (actions:=Areg (Sequence r1 r2) :: cont); try constructor; auto; pike_subset.
  - invert_rep.
    { invert_rep. invert_rep; try in_subset; try stutter. }
    exists pcstart. exists b. exists n0. split; try split; try lia.
    * simpl. rewrite JMP. auto.
    * apply tt_eq with (actions:=Areg (Quantified greedy (S min) plus r1) :: cont); try constructor; auto; pike_subset.
  - pike_subset.
  - invert_rep.
    { invert_rep. invert_rep; try in_subset. destruct greedy; stutter. }
    exists pcstart. exists b. exists n0. split; try split; try lia.
    + simpl. rewrite JMP. auto.
    + pike_subset. destruct plus; inversion H3. simpl in CONT0.
      apply tt_eq with (actions:=Areg (Quantified greedy 0 (NoI.N 1 + +∞)%NoI r1) :: cont); try constructor; auto; pike_subset.
      eapply tree_quant_free; eauto.
  - invert_rep.
    { invert_rep. invert_rep; try in_subset; try stutter. }
    exists pcstart. exists b. exists n0. split; try split; try lia.
    * simpl. rewrite JMP. auto.
    * apply tt_eq with (actions:=Areg (Group gid r1):: cont); try constructor; auto; pike_subset.
  - pike_subset.
  - pike_subset.
Qed.


Theorem invariant_preservation:
  forall code pts1 pvs1 n pts2
    (INV: pike_inv code pts1 pvs1 n)
    (TREESTEP: pike_tree_step pts1 pts2),
    (* progress on the PTS side implies progress on the PVS side *)
    (        
      exists pvs2 m,
        pike_vm_step code pvs1 pvs2 /\
          pike_inv code pts2 pvs2 m
    )
    \/
      (* stuttering step on the PVS side *)
      (
        exists pvs2 m,
          pike_vm_step code pvs1 pvs2 /\
            pike_inv code pts1 pvs2 m /\
            m < n
      ).
Proof.
  intros code pts1 pvs1 n pts2 INV TREESTEP.
  inversion INV; subst.
  (* Final states make no step *)
  2: { left. intros. inversion TREESTEP. }
  inversion TREESTEP; subst.
  (* pts_final *)
  - left. exists (PVS_final best). exists 0. split.
    + inversion ACTIVE. subst.
      destruct (advance_input inp) eqn:ADVANCE.
      * specialize (BLOCKED i eq_refl). inversion BLOCKED. subst. apply pvs_final.
      * specialize (ENDVM eq_refl). subst. apply pvs_end. auto.
    + apply pikeinv_final.
  (* pts_nextchar *)
  - left. inversion ACTIVE. subst.
    (* the pike vm has two different rules for when we reach the end of input or not *)
    destruct (advance_input inp) as [nextinp|] eqn:ADVANCE.
    + specialize (BLOCKED nextinp eq_refl).
      inversion BLOCKED. subst.
      exists (PVS nextinp ((pc,gm,b)::threadlist) best []). exists n. split.
      * apply pvs_nextchar. auto.
      * apply advance_next in ADVANCE. subst. eapply pikeinv; eauto. intros. constructor.
    + specialize (ENDTREE eq_refl). inversion ENDTREE.
  (* pts_active *)
  - inversion ACTIVE. subst.
    destruct (stutters pc code) eqn:STUTTERS.
    + right. apply stutter_step in TT as [nextpc [nextb [m [EPSSTEP [TT LESS]]]]]; subst; eauto.
      exists (PVS inp ([(nextpc, gm, nextb)] ++ threadlist) best threadblocked). exists m.
      split; try split; auto.
      * apply pvs_active. auto.
      * simpl. eapply pikeinv with (measureactive:=m::measurelist); eauto. econstructor; eauto.
    + left. inversion ACTIVE. subst. rename t into tree.
      eapply generate_active in TT as [newthreads [measure [EPS LTT2]]]; eauto.
      exists (PVS inp (newthreads++threadlist) best threadblocked). exists (hd 0 ((measure ++ measurelist) ++ measureblocked)). split.
      * apply pvs_active. auto.
      * eapply pikeinv; auto. apply ltt_app; eauto.
  (* pts_match *)
  - inversion ACTIVE. subst.
     destruct (stutters pc code) eqn:STUTTERS.
    + right. apply stutter_step in TT as [nextpc [nextb [m [EPSSTEP [TT LESS]]]]]; subst; eauto.
      exists (PVS inp ([(nextpc, gm, nextb)] ++ threadlist) best threadblocked). exists m.
      split; try split; auto.
      * apply pvs_active. auto.
      * simpl. eapply pikeinv with (measureactive:=m::measurelist); eauto. econstructor; eauto.
    + left. rename t into tree. eapply generate_match in TT; eauto.
      exists (PVS inp [] (Some (inp,gm)) threadblocked). exists (hd 0 measureblocked). split.
      * apply pvs_match. auto.
      * econstructor; auto. constructor. simpl. auto.
  (* pts_blocked *)
  - inversion ACTIVE. subst.
    destruct (stutters pc code) eqn:STUTTERS.
    + right. apply stutter_step in TT as [nextpc [nextb [m [EPSSTEP [TT LESS]]]]]; subst; eauto.
      exists (PVS inp ([(nextpc, gm, nextb)] ++ threadlist) best threadblocked). exists m.
      split; try split; auto.
      * apply pvs_active. auto.
      * simpl. eapply pikeinv with (measureactive:=m::measurelist); eauto. econstructor; eauto.
    + left. rename t into tree.
      specialize (generate_blocked _ _ _ _ _ _ _ _ STEP STUTTERS TT) as [EPS2 [TT2 [nexti ADVANCE]]].
      exists (PVS inp threadlist best (threadblocked ++ [(pc+1,gm,CanExit)])). exists (hd 0 (measurelist ++ measureblocked ++ [n])). split.
      * apply pvs_blocked. auto.
      * econstructor; eauto.
        2: { intros H. rewrite ADVANCE in H. inversion H. }
        2: { intros H. rewrite ADVANCE in H. inversion H. }
        intros nextinp H. specialize (BLOCKED nextinp H).
        apply ltt_app; eauto. specialize (TT2 nextinp H).
        eapply ltt_cons. constructor. auto.
Qed.


(** * Backward Style Invariant Preservation *)
(* Deprecated *)
(* Theorem backward_match: *)
(*   forall tree gm idx inp code pc b n *)
(*     (VMSTEP: epsilon_step (pc,gm,b) code inp idx = EpsMatch) *)
(*     (NOSTUTTER: stutters pc code = false) *)
(*     (TT: tree_thread code inp (tree, gm) (pc, gm, b) n), *)
(*     tree = Match. *)
(* Proof. *)
(*   intros tree gm idx inp code pc b n VMSTEP NOSTUTTER TT. *)
(*   simpl in VMSTEP. *)
(*   (* extracting current instruction *) *)
(*   destruct (get_pc code pc) as [instr|] eqn:CODE. *)
(*   2: { inversion VMSTEP. } *)
(*   destruct instr; try solve [inversion VMSTEP]. *)
(*   2: { destruct (check_read c inp); inversion VMSTEP. } *)
(*   2: { destruct b; inversion VMSTEP. } *)
(*   (* extracting relevant invariant case *) *)
(*   inversion TT; subst. *)
(*   2: { rewrite RESET in CODE. inversion CODE. } *)
(*   2: { rewrite BEGIN in CODE. inversion CODE. } *)
(*   (* there are many ways that we could be at an Accept instruction *) *)
(*   (* we could have r = epsilon, cont = [] *) *)
(*   (* or r = Epsilon;Epsilon, cont = []... *) *)
(* Abort. *)
(* It's really harder to reason from the VM step *)
(* It's much easier to reason from a Pike tree step, ast it allows inductive reasoning on the bool_tree semantics  *)
