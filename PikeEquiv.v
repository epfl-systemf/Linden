(* Relating the PikeVM smallstep semantics to the Pike Tree smallstep semantics *)

Require Import List Lia.
Import ListNotations.

Require Import Regex Chars Groups.
Require Import Tree Semantics BooleanSemantics.
Require Import NFA PikeTree PikeVM.

(* a tree and a thread are equivalent when they are about to execute the same thing *)
(* this means when the tree represents a given regex and continuation, *)
(* the thread is at a pc that will execute the nfa of that same regex and continuation *)
(* the nat is a measure of stuttering steps *)
Inductive tree_thread (code:code) (inp:input) : (tree * group_map) -> thread -> nat -> Prop :=
| tt_eq:
  forall tree gm pc b pc_cont pc_end r cont n
    (TREE: bool_tree r cont inp b tree)
    (NFA: nfa_rep r code pc pc_cont)
    (CONT: continuation_rep cont code pc_cont pc_end n),
    tree_thread code inp (tree, gm) (pc, gm, b) n
| tt_reset:
  forall tree gm pc b n gidl
    (TT: tree_thread code inp (tree,reset_groups gm gidl) (pc+1,reset_groups gm gidl,b) n)
    (RESET: get_pc code pc = Some (ResetRegs gidl)),
    tree_thread code inp (ResetGroups gidl tree,gm) (pc,gm,b) n
| tt_begin:
  forall tree gm pc b n
    (TT: tree_thread code inp (tree,gm) (pc+1,gm,CannotExit) n)
    (BEGIN: get_pc code pc = Some BeginLoop),
    tree_thread code inp (tree,gm) (pc,gm,b) (S n).
    

(* the initial active thread and the initial active tree are related with the invariant *)
Lemma initial_tree_thread:
  forall r code tree inp
    (COMPILE: compilation r = code)
    (TREE: bool_tree r [] inp CanExit tree),
    tree_thread code inp (tree, empty_group_map) (0, empty_group_map, CanExit) 0.
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


(* lifting the equivalence predicate to pike states *)
Inductive pike_inv (code:code): pike_tree_state -> pike_vm_state -> nat -> Prop :=
| pikeinv:
  forall inp idx treeactive treeblocked threadactive threadblocked best measureactive measureblocked n
    (ACTIVE: list_tree_thread code inp treeactive threadactive measureactive)
    (* blocked threads should be equivalent for the next input *)
    (* nothing to say if there is no next input *)
    (BLOCKED: forall nextinp, advance_input inp = Some nextinp -> list_tree_thread code nextinp treeblocked threadblocked measureblocked)
    (* the measure is simply the measure of the top priority thread *)
    (MEASURE: n = hd 0 (measureactive++measureblocked)),
    pike_inv code (PTS idx treeactive best treeblocked) (PVS inp idx threadactive best threadblocked) n
| pikeinv_final:
  forall best,
    pike_inv code (PTS_final best) (PVS_final best) 0.

(* the initial states of both smallstep semantics are related with the invariant *)
Lemma initial_pike_inv:
  forall r inp tree code
    (TREE: bool_tree r [] inp CanExit tree)
    (COMPILE: compilation r = code),
    pike_inv code (pike_tree_initial_state tree) (pike_vm_initial_state inp) 0.
Proof.
  intros r inp tree code TREE COMPILE.
  unfold compilation in COMPILE. destruct (compile r 0) as [c fresh] eqn:COMP.
  apply compile_nfa_rep with (prev := []) in COMP as REP; auto. simpl in REP.
  apply fresh_correct in COMP. simpl in COMP. subst.
  eapply pikeinv; econstructor.
  { constructor. }
  apply tt_eq with (pc_cont:=length c) (pc_end:=length c) (r:=r) (cont:=[]); auto.
  - subst. apply nfa_rep_extend. auto.
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
Definition stutters (pc:label) (code:code) : bool :=
  match get_pc code pc with
  | Some (Jmp _) => true
  | Some BeginLoop => true
  | _ => false
  end.

Lemma does_stutter:
  forall pc code, stutters pc code = true ->
             get_pc code pc = Some BeginLoop \/ exists next, get_pc code pc = Some (Jmp next).
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


(** * Invariant Preservation  *)

(* generate lemmas: *)
(* For each possible kind of tree, I show that the PikeTree step over that tree corresponds *)
(* to an equivalent step in the PikeVM. This preserves the invariant. *)
(* These lemmas discard the stuttering steps by preventing the current pc being at a Jmp instruction *)

Theorem generate_match:
  forall tree gm idx inp code pc b n
    (TREESTEP: tree_bfs_step tree gm idx = StepMatch)
    (NOSTUTTER: stutters pc code = false)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b) n),
    epsilon_step (pc, gm, b) code inp idx = EpsMatch.
Proof.
  intros tree gm idx inp code pc b n TREESTEP NOSTUTTER TT.
  unfold tree_bfs_step in TREESTEP. destruct tree; inversion TREESTEP. subst. clear TREESTEP.
  inversion TT; subst.
  2: { apply doesnt_stutter_begin in NOSTUTTER; auto. contradiction. }
  remember Match as TMATCH.
  generalize dependent pc_cont. generalize dependent pc_end.
  (* here we have to proceed by induction because there are many ways to get a Match tree *)
  (* it could be the regex epsilon, it could be a continuation, it could be epsilon followed by epsilon etc *)
  induction TREE; intros; subst; try inversion HeqTMATCH.
  - unfold epsilon_step. inversion NFA. inversion CONT; subst.
    2: { exfalso. eapply doesnt_stutter_jmp; eauto. }
    rewrite ACCEPT. auto.
  - inversion NFA. inversion CONT; subst.
    2: { exfalso. eapply doesnt_stutter_jmp; eauto. }
    inversion ACTION. subst. eapply IHTREE; eauto. 
  - inversion NFA. subst. eapply IHTREE; eauto.
    econstructor; eauto. constructor. auto.
  - inversion CHOICE.
Qed.


Theorem generate_blocked:
  forall tree gm idx inp code pc b nexttree n
    (TREESTEP: tree_bfs_step tree gm idx = StepBlocked nexttree)
    (NOSTUTTER: stutters pc code = false)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b) n),
  exists nextthread,
    epsilon_step (pc, gm, b) code inp idx = EpsBlocked nextthread /\
      (forall nextinp, advance_input inp = Some nextinp -> tree_thread code nextinp (nexttree,gm) nextthread n).
Proof.
  intros tree gm idx inp code pc b nexttree n TREESTEP NOSTUTTER TT.
  unfold tree_bfs_step in TREESTEP. destruct tree; inversion TREESTEP. subst. clear TREESTEP.
  inversion TT; subst.
  2: { exfalso. eapply doesnt_stutter_begin; eauto. }
  remember (Read c nexttree) as TREAD.
  generalize dependent pc_cont. generalize dependent pc_end.
  induction TREE; intros; subst; try inversion HeqTREAD; subst.
  - inversion NFA. inversion CONT; subst.
    2: { exfalso. eapply doesnt_stutter_jmp; eauto. }
    inversion ACTION. subst. eapply IHTREE; eauto.
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

Theorem generate_open:
  forall gid tree gm idx inp code pc b n
    (TT: tree_thread code inp (OpenGroup gid tree, gm) (pc, gm, b) n)
    (NOSTUTTER: stutters pc code = false),
    epsilon_step (pc, gm, b) code inp idx = EpsActive [(pc + 1, open_group gm gid idx, b)] /\
      tree_thread code inp (tree,open_group gm gid idx) (pc + 1, open_group gm gid idx, b) n.
Proof.
  intros gid tree gm idx inp code pc b n TT NOSTUTTER.
  inversion TT; subst.
  2: { exfalso. eapply doesnt_stutter_begin; eauto. }
  remember (OpenGroup gid tree) as TOPEN.
  generalize dependent pc_cont. generalize dependent pc_end.
  induction TREE; intros; subst; try inversion HeqTOPEN; subst.
  - inversion NFA. inversion CONT; subst.
    2: { exfalso. eapply doesnt_stutter_jmp; eauto. }
    inversion ACTION. subst. eapply IHTREE; eauto.
  - inversion NFA. subst. eapply IHTREE; eauto.
    econstructor; eauto. constructor. auto.
  - inversion CHOICE.
  - inversion NFA. subst. simpl. rewrite OPEN. split; auto.
    replace (pc+1) with (S pc) by lia. eapply tt_eq; eauto.
    apply cons_bc with (pcmid:=S end1); eauto. constructor. auto.
Qed.

Theorem generate_close:
  forall gid tree gm idx inp code pc b n
    (TT: tree_thread code inp (CloseGroup gid tree, gm) (pc, gm, b) n)
    (NOSTUTTER: stutters pc code = false),
    epsilon_step (pc, gm, b) code inp idx = EpsActive [(pc + 1, close_group gm gid idx, b)] /\
      tree_thread code inp (tree,close_group gm gid idx) (pc + 1, close_group gm gid idx, b) n.
Proof.
  intros gid tree gm idx inp code pc b n TT NOSTUTTER.
  inversion TT; subst.
  2: { exfalso. eapply doesnt_stutter_begin; eauto. }
  remember (CloseGroup gid tree) as TCLOSE.
  generalize dependent pc_cont. generalize dependent pc_end.
  induction TREE; intros; subst; try inversion HeqTCLOSE; subst.
  - inversion NFA. inversion CONT; subst.
    2: { exfalso. eapply doesnt_stutter_jmp; eauto. }
    inversion ACTION. subst. eapply IHTREE; eauto.
  - inversion NFA. inversion CONT; subst.
    2: { exfalso. eapply doesnt_stutter_jmp; eauto. }
    inversion ACTION. subst. simpl. rewrite CLOSE.
    split. auto. econstructor; eauto. replace (S pc_cont) with (pc_cont + 1) by lia. constructor.
  - inversion NFA. subst. eapply IHTREE; eauto.
    econstructor; eauto. constructor. auto.
  - inversion CHOICE.
Qed.

Theorem no_tree_reset:
  (* The tree of a regex or a continuation cannot start with ResetGroups *)
  forall gidl tree inp r cont b,
    bool_tree r cont inp b (ResetGroups gidl tree) -> False.
Proof.
  intros gidl tree inp r cont b H.
  remember (ResetGroups gidl tree) as TRESET.
  induction H; inversion HeqTRESET; subst; auto.
  inversion CHOICE.
Qed.

Corollary generate_reset:  
  forall gidl tree inp code pc b gm n idx
    (TT: tree_thread code inp (ResetGroups gidl tree, gm) (pc,gm,b) n)
    (NOSTUTTER: stutters pc code = false),
    epsilon_step (pc,gm,b) code inp idx = EpsActive [(pc+1, reset_groups gm gidl, b)] /\
      tree_thread code inp (tree,reset_groups gm gidl) (pc+1, reset_groups gm gidl, b) n.
Proof.
  intros.
  inversion TT; subst.
  - exfalso. eapply no_tree_reset; eauto.
  - simpl. rewrite RESET. split; auto.
  - exfalso. eapply doesnt_stutter_begin; eauto.
Qed.

Theorem generate_checkfail:
  forall str gm idx inp code pc b n
    (TT: tree_thread code inp (CheckFail str, gm) (pc, gm, b) n)
    (NOSTUTTER: stutters pc code = false),
    epsilon_step (pc, gm, b) code inp idx = EpsActive [].
Proof.
  intros str gm idx inp code pc b n TT NOSTUTTER.
  inversion TT; subst.
  2: { exfalso. eapply doesnt_stutter_begin; eauto. }
  remember (CheckFail str) as TFAIL.
  generalize dependent pc_cont. generalize dependent pc_end.
  induction TREE; intros; subst; try inversion HeqTFAIL; subst.
  - inversion NFA. inversion CONT; subst.
    2: { exfalso. eapply doesnt_stutter_jmp; eauto. }
    inversion ACTION. subst. eapply IHTREE; eauto.
  - inversion NFA. inversion CONT; subst.
    2: { exfalso. eapply doesnt_stutter_jmp; eauto. }
    inversion ACTION. subst. simpl. rewrite END. auto.
  - inversion NFA. subst. eapply IHTREE; eauto.
    econstructor; eauto. constructor. auto.
  - inversion CHOICE.
Qed.

Theorem generate_checkpass:
  forall str tree gm idx inp code pc b n
    (TT: tree_thread code inp (CheckPass str tree, gm) (pc, gm, b) n)
    (NOSTUTTER: stutters pc code = false),
    exists nextpc, epsilon_step (pc, gm, b) code inp idx = EpsActive [(nextpc,gm,CanExit)] /\
      tree_thread code inp (tree,gm) (nextpc,gm,CanExit) n.
Proof.
  intros str tree gm idx inp code pc b n TT NOSTUTTER.
  inversion TT; subst.
  2: { exfalso. eapply doesnt_stutter_begin; eauto. }
  remember (CheckPass str tree) as TPASS.
  generalize dependent pc_cont. generalize dependent pc_end.
  induction TREE; intros; subst; try inversion HeqTPASS; subst.
  - inversion NFA. inversion CONT; subst.
    2: { exfalso. eapply doesnt_stutter_jmp; eauto. }
    inversion ACTION. subst. eapply IHTREE; eauto.
  - inversion NFA. inversion CONT; subst.
    2: { exfalso. eapply doesnt_stutter_jmp; eauto. }
    inversion ACTION. subst. simpl. rewrite END.
    exists pcmid. split; auto. econstructor; eauto. constructor.
  - inversion NFA. subst. eapply IHTREE; eauto.
    econstructor; eauto. constructor. auto.
  - inversion CHOICE.
Qed.

Theorem generate_mismatch:
  forall gm idx inp code pc b n
    (TT: tree_thread code inp (Mismatch, gm) (pc, gm, b) n)
    (NOSTUTTER: stutters pc code = false),
    epsilon_step (pc, gm, b) code inp idx = EpsActive [].
Proof.
  intros gm idx inp code pc b n TT NOSTUTTER.
  inversion TT; subst.
  2: { exfalso. eapply doesnt_stutter_begin; eauto. }
  remember (Mismatch) as TMIS.
  generalize dependent pc_cont. generalize dependent pc_end.
  induction TREE; intros; subst; try inversion HeqTMIS; subst.
  - inversion NFA. inversion CONT; subst.
    2: { exfalso. eapply doesnt_stutter_jmp; eauto. }
    inversion ACTION. subst. eapply IHTREE; eauto.
  - inversion NFA. subst. unfold epsilon_step. rewrite CONSUME.
    rewrite cannot_read_correct in READ. rewrite READ. auto.
  - inversion NFA. subst. eapply IHTREE; eauto.
    econstructor; eauto. constructor. auto.
  - inversion CHOICE.
Qed.


Theorem generate_choice:
  forall tree1 tree2 gm idx inp code pc b treeactive n
    (TREESTEP: tree_bfs_step (Choice tree1 tree2) gm idx = StepActive treeactive)
    (NOSTUTTER: stutters pc code = false)
    (TT: tree_thread code inp (Choice tree1 tree2, gm) (pc, gm, b) n),
  exists threadactive measure,
    epsilon_step (pc, gm, b) code inp idx = EpsActive threadactive /\
      list_tree_thread code inp treeactive threadactive measure.
Proof.
  intros tree1 tree2 gm idx inp code pc b treeactive n TREESTEP NOSTUTTER TT.
  unfold tree_bfs_step in TREESTEP. inversion TREESTEP. subst. clear TREESTEP.
  inversion TT; subst.
  2: { exfalso. eapply doesnt_stutter_begin; eauto. }
  remember (Choice tree1 tree2) as TCHOICE.
  generalize dependent pc_cont. generalize dependent pc_end.
  induction TREE; intros; subst; try inversion HeqTCHOICE; subst.
  - inversion NFA. inversion CONT; subst.
    2: { exfalso. eapply doesnt_stutter_jmp; eauto. }
    inversion ACTION. subst. eapply IHTREE; eauto.
  - inversion NFA. subst. exists [(S pc,gm,b);(S end1,gm,b)]. exists [S n; n]. split.
    (* here in the first element of the list we introduced an extra stuttering step, thus (S n) measure *)
    + unfold epsilon_step. rewrite FORK. auto.
    + constructor.
      * constructor. constructor.
        apply tt_eq with (pc_cont:=pc_cont) (pc_end:=pc_end) (r:=r2) (cont:=cont); auto.
      * apply tt_eq with (pc_cont:=end1) (pc_end:=pc_end) (r:=r1) (cont:=cont); auto.
        replace (S n) with (n + 1) by lia. apply jump_bc with (pcstart := pc_cont); auto.
  - inversion NFA. subst. eapply IHTREE; eauto.
    econstructor; eauto. constructor. auto.
  (* when the choice comes from a star *)
  - inversion NFA. subst. simpl. inversion CHOICE. subst.
    rewrite FORK. exists [(S pc, gm, b); (S end1, gm, b)]. exists [S n; n]. split; auto.
    econstructor.
    + econstructor. constructor.
      apply tt_eq with (pc_cont:=S end1) (pc_end:=pc_end) (r:=Epsilon) (cont:=cont); auto.
      constructor.
    + apply tt_begin; auto.
      replace (S (S pc)) with (S pc + 1) in RESET by lia.
      apply tt_reset; auto.
      apply tt_eq with (pc_cont:=end1) (pc_end:=pc_end) (r:=r1) (cont:=Acheck(current_str inp)::Areg(Star r1)::cont); auto.
      * replace (S pc+1+1) with (S (S (S pc))) by lia. auto.
      * apply cons_bc with (pcmid:=pc).
        { constructor. auto. }
        apply cons_bc with (pcmid:=S end1); try constructor; auto.
Qed.


(* next we combine the generate lemmas together, for the general non-stuttering case *)
Theorem generate_active:
  forall tree gm idx inp code pc b treeactive n
    (TREESTEP: tree_bfs_step tree gm idx = StepActive treeactive)
    (NOSTUTTER: stutters pc code = false)
    (TT: tree_thread code inp (tree, gm) (pc, gm, b) n),
  exists threadactive measure,
    epsilon_step (pc, gm, b) code inp idx = EpsActive threadactive /\
      list_tree_thread code inp treeactive threadactive measure.
Proof.
  intros tree gm idx inp code pc b treeactive n TREESTEP NOSTUTTER TT.
  destruct tree; simpl in TREESTEP; inversion TREESTEP; subst.
  - eapply generate_mismatch in TT; auto. exists []. exists []. split; eauto. constructor.
  - eapply generate_choice; eauto.
  - eapply generate_checkfail in TT; auto. exists []. exists []. split; eauto. constructor.
  - eapply generate_checkpass in TT as [nextpc [STEP EQ]]; auto.
    exists [(nextpc,gm,CanExit)]. exists [n]. split; eauto.
    constructor; auto. constructor.
  - eapply generate_open in TT as [STEP EQ]; auto.
    exists [(pc+1,open_group gm g idx,b)]. exists [n]. split; eauto.
    constructor; auto. constructor.
  - eapply generate_close in TT as [STEP EQ]; auto.
    exists [(pc+1,close_group gm g idx,b)]. exists [n]. split; eauto.
    constructor; auto. constructor.
  - eapply generate_reset in TT as [STEP EQ]; auto.
    exists [(pc + 1, reset_groups gm gl, b)]. exists [n]. split; eauto.
    constructor; auto. constructor. 
Qed.

(* in the case where we are at a stuttering step, we show that we still preserve the invariant and decrease the measure *)
Theorem stutter_step:
  forall tree gm inp code pc b n idx
    (TT: tree_thread code inp (tree,gm) (pc,gm,b) n)
    (STUTTER: stutters pc code = true),
  exists nextpc nextb m,
    epsilon_step (pc,gm,b) code inp idx = EpsActive [(nextpc,gm,nextb)] /\
      tree_thread code inp (tree,gm) (nextpc,gm,nextb) m /\
      n = S m.
Proof.
  intros tree gm inp code pc b n idx TT STUTTER.
  inversion TT; subst.
  (* reset is not stuttering *)
  2: { unfold stutters in STUTTER. rewrite RESET in STUTTER. inversion STUTTER. }
  (* at a beginloop instruction *)
  2: { exists (pc + 1). exists CannotExit. exists n0. split; try split; auto.
       simpl. rewrite BEGIN. auto. }
  (* at a jmp instruction *)
  generalize dependent pc_cont. generalize dependent pc_end.
  induction TREE; intros; inversion NFA; subst.
  - inversion CONT; subst.
    { unfold stutters in STUTTER. rewrite ACCEPT in STUTTER. inversion STUTTER. }
    exists pcstart. exists b. exists n0. split; try split; try lia.
    + simpl. rewrite JMP. auto.
    + apply tt_eq with (pc_cont:=pcstart) (pc_end:=pc_end) (r:=Epsilon) (cont:=[]); try constructor; auto.
  - inversion CONT; subst.
    { inversion ACTION. subst. eapply IHTREE; eauto. }
    exists pcstart. exists b. exists n0. split; try split; try lia.
    + simpl. rewrite JMP. auto.
    + apply tt_eq with (pc_cont:=pcstart) (pc_end:=pc_end) (r:=Epsilon) (cont:=Areg regcont::tailcont);
        try constructor; auto.
  - inversion CONT; subst.
    { inversion ACTION. subst. unfold stutters in STUTTER. rewrite END in STUTTER. inversion STUTTER. }
    exists pcstart. exists CanExit. exists n0. split; try split; try lia.
    + simpl. rewrite JMP. auto.
    + apply tt_eq with (pc_cont:=pcstart) (pc_end:=pc_end) (r:=Epsilon) (cont:=Acheck strcheck::tailcont); try constructor; auto.
  - inversion CONT; subst.
    { inversion ACTION. subst. unfold stutters in STUTTER. rewrite END in STUTTER. inversion STUTTER. }
    exists pcstart. exists CannotExit. exists n0. split; try split; try lia.
    + simpl. rewrite JMP. auto.
    + apply tt_eq with (pc_cont:=pcstart) (pc_end:=pc_end) (r:=Epsilon) (cont:=Acheck strcheck::tailcont); try constructor; auto.
  - inversion CONT; subst.
    { inversion ACTION. subst. unfold stutters in STUTTER. rewrite CLOSE in STUTTER. inversion STUTTER. }
    exists pcstart. exists b. exists n0. split; try split; try lia.
    + simpl. rewrite JMP. auto.
    + apply tt_eq with (pc_cont:=pcstart) (pc_end:=pc_end) (r:=Epsilon) (cont:=Aclose gid::tailcont); try constructor; auto.
  - unfold stutters in STUTTER. rewrite CONSUME in STUTTER. inversion STUTTER.
  - unfold stutters in STUTTER. rewrite CONSUME in STUTTER. inversion STUTTER.
  - unfold stutters in STUTTER. rewrite FORK in STUTTER. inversion STUTTER.
  - eapply IHTREE; eauto. eapply cons_bc; eauto. apply areg_bc. auto.
  - unfold stutters in STUTTER. rewrite FORK in STUTTER. inversion STUTTER.
  - unfold stutters in STUTTER. rewrite OPEN in STUTTER. inversion STUTTER.
Qed.


(* to adapt:
    

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
  (* pts final *)
  - left. exists (PVS_final best). exists 0. split.
    + inversion ACTIVE.
      destruct (advance_input inp) eqn:ADVANCE.
      * specialize (BLOCKED i eq_refl). inversion BLOCKED. subst. apply pvs_final.
      * apply pvs_end. auto.
    + apply pikeinv_final.
  (* pts_nextchar *)
  - left. inversion ACTIVE. subst.
    (* the pike vm has two different rules for when we reach the end of input or not *)
    destruct (advance_input inp) as [nextinp|] eqn:ADVANCE.
    + specialize (BLOCKED nextinp eq_refl).
      inversion BLOCKED. subst.
      exists (PVS nextinp (idx+1) ((pc,gm,b)::threadlist) best []). exists n. split.
      * apply pvs_nextchar. auto.
      * eapply pikeinv; eauto. intros. constructor.
    + exists (PVS_final best). exists 0. split.
      * apply pvs_end. auto.
      * admit. (* it should not be possible for PTS to continue while PVS has reached end of input *)
  (* pts_active *)
  - inversion ACTIVE. subst.
    destruct (stutters pc code) eqn:STUTTERS.
    + right. apply does_stutter in STUTTERS as [next JMP].
      eapply stutter_step in TT as [m [TT LESS]]; subst; eauto.
      exists (PVS inp idx ([(next, gm, b)] ++ threadlist) best threadblocked). exists m.
      split; try split; auto.
      * apply pvs_active. simpl. rewrite JMP. auto.
      * simpl. eapply pikeinv; eauto. econstructor; eauto. simpl. auto.
    + left. inversion ACTIVE. subst. rename t into tree.
      eapply generate_active in TT as [newthreads [measure [EPS LTT2]]]; eauto.
      2: { apply doesnt_stutter. auto. }
      exists (PVS inp idx (newthreads++threadlist) best threadblocked). exists (hd 0 ((measure ++ measurelist) ++ measureblocked)). split.
      * apply pvs_active. auto.
      * eapply pikeinv; auto. apply ltt_app; eauto.
  (* pts_match *)
  - inversion ACTIVE. subst.
     destruct (stutters pc code) eqn:STUTTERS.
    + right. apply does_stutter in STUTTERS as [next JMP].
      eapply stutter_step in TT as [m [TT LESS]]; subst; eauto.
      exists (PVS inp idx ([(next, gm, b)] ++ threadlist) best threadblocked). exists m.
      split; try split; auto.
      * apply pvs_active. simpl. rewrite JMP. auto.
      * simpl. eapply pikeinv; eauto. econstructor; eauto. simpl. auto.
    + left. rename t into tree. eapply generate_match in TT; eauto.
      2: { apply doesnt_stutter. auto. }
      exists (PVS inp idx [] (Some gm) threadblocked). exists (hd 0 measureblocked). split.
      * apply pvs_match. auto.
      * econstructor; auto. constructor. simpl. auto.
  (* pts_blocked *)
  - inversion ACTIVE. subst.
    destruct (stutters pc code) eqn:STUTTERS.
    + right. apply does_stutter in STUTTERS as [next JMP].
      eapply stutter_step in TT as [m [TT LESS]]; subst; eauto.
      exists (PVS inp idx ([(next, gm, b)] ++ threadlist) best threadblocked). exists m.
      split; try split; auto.
      * apply pvs_active. simpl. rewrite JMP. auto.
      * simpl. eapply pikeinv; eauto. econstructor; eauto. simpl. auto.
    + left. rename t into tree.
    eapply generate_blocked in TT as [nextt [EPS TT2]]; eauto.
    2: { apply doesnt_stutter. auto. }
    exists (PVS inp idx threadlist best (threadblocked ++ [nextt])). exists (hd 0 (measurelist ++ measureblocked ++ [n])). split.
      * apply pvs_blocked. auto.
      * econstructor; eauto. intros nextinp H. specialize (BLOCKED nextinp H).
        apply ltt_app; eauto. specialize (TT2 nextinp H).
        inversion TT2; subst.
        2: { admit.  }
        2: { admit. }
        subst. constructor; eauto. constructor.
Admitted.
*)
