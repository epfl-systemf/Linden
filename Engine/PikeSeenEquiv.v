(* Relating the PikeVM smallstep semantics to the Pike Tree smallstep semantics *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeTree PikeVM.
From Linden Require Import PikeTreeSeen PikeVMSeen.
From Linden Require Import PikeEquiv PikeSubset.
From Linden Require Import TreeRep.
From Warblre Require Import Base.

(** * Simulation Invariant  *)

(* This is not, strictly speaking, an inclusion, which explains the second case of this disjunction *)
(* Sometimes, we add seen pcs on the VM side that do not correspond yet to any seen tree on the tree side *)
(* this happens during stuttering steps: such pcs are always stuttering, equivalent to the current active tree, *)
(* but these pcs are not equal to the current pc : they're smaller *)
(* the relation is then indexed by the current pc *)
Definition seen_inclusion (c:code) (inp:input) (treeseen:seentrees) (threadseen:seenpcs) (current:option (tree*group_map)) (currentpc:label): Prop :=
  forall pc b
    (SEEN: inseenpc threadseen pc b = true),
  (exists t gm n,
      inseen treeseen t = true /\
        tree_thread c inp (t, gm) (pc, gm, b) n)
  \/
    (stutters pc c = true /\
       exists m t gm, pc < currentpc /\ current = Some (t,gm) /\
              tree_thread c inp (t,gm) (pc,gm,b) m).

Definition head_pc (threadactive:list thread) : label :=
  match threadactive with
  | [] => 0
  | (pc,_,_)::_ => pc
  end.

Inductive pike_inv (code:code): pike_tree_seen_state -> pike_vm_seen_state -> nat -> Prop :=
| pikeinv:
  forall inp treeactive treeblocked threadactive threadblocked best treeseen threadseen measureactive measureblocked n
    (ACTIVE: list_tree_thread code inp treeactive threadactive measureactive)
    (* blocked threads should be equivalent for the next input *)
    (* nothing to say if there is no next input *)
    (BLOCKED: forall nextinp, advance_input inp forward = Some nextinp -> list_tree_thread code nextinp treeblocked threadblocked measureblocked)
    (* these two properties are needed to ensure the two algorithms stop at he same time *)
    (ENDVM: advance_input inp forward = None -> threadblocked = [])
    (ENDTREE: advance_input inp forward = None -> treeblocked = [])
    (* any pc in threadseen must correspond to a tree in treeseen *)
    (SEEN: seen_inclusion code inp treeseen threadseen (hd_error treeactive) (head_pc threadactive))
    (* the measure is simply the measure of the top priority thread *)
    (MEASURE: n = hd 0 (measureactive++measureblocked)),
    pike_inv code (PTSS inp treeactive best treeblocked treeseen) (PVSS inp threadactive best threadblocked threadseen) n
| pikeinv_final:
  forall best,
    pike_inv code (PTSS_final best) (PVSS_final best) 0.



(** * Representation Unicity lemmas  *)

(* tree-thread equivalence can only happen for a single gm *)
Lemma tt_same_gm:
  forall t gm1 pc gm2 b code inp n,
    tree_thread code inp (t,gm1) (pc,gm2,b) n -> gm1 = gm2.
Proof.
  intros t gm1 pc gm2 b code inp n H. inversion H; auto.
Qed.


(* A representation cannot start with Reset or BeginLoop *)
Inductive start_rep: bytecode -> Prop :=
| start_accept: start_rep Accept
| start_cons: forall cd, start_rep (Consume cd)
| start_jmp: forall lbl, start_rep (Jmp lbl)
| start_fork: forall l1 l2, start_rep (Fork l1 l2)
| start_open: forall gid, start_rep (SetRegOpen gid)
| start_close: forall gid, start_rep (SetRegClose gid)
| start_end: forall lbl, start_rep (EndLoop lbl)
| start_kill: start_rep KillThread.

Lemma nfa_rep_start:
  forall r code pc pcend,
    nfa_rep r code pc pcend ->
    pc = pcend \/
      (exists i, get_pc code pc = Some i /\ start_rep i).
Proof.
  intros r code pc pcend H. induction H;
    try solve[left; simpl; auto];
    try solve[right; eexists; split; eauto; constructor].
  - destruct IHnfa_rep1 as [SAME1 | [i [START1 REP1]]]; subst.
    2: { right. eexists. split; eauto. }
    destruct IHnfa_rep2 as [SAME2 | [i [START2 REP2]]]; subst.
    + left. auto.
    + right. eexists. split; eauto.
  - right. destruct greedy; inversion FORK; eexists; split; eauto; constructor.
Qed.

Lemma action_rep_start:
  forall a code pc pcend,
    action_rep a code pc pcend ->
    pc = pcend \/
      (exists i, get_pc code pc = Some i /\ start_rep i).
Proof.
  intros a code pc pcend H. destruct a.
  - inversion H. subst. apply nfa_rep_start in NFA. auto.
  - inversion H. subst. right. exists (EndLoop pcend). split; auto. constructor.
  - inversion H. subst. right. exists (SetRegClose g). split; auto. constructor.
Qed.

Lemma actions_rep_start:
  forall act code pc n i,
    actions_rep act code pc n ->
    get_pc code pc = Some i ->
    start_rep i.
Proof.
  intros act code pc n i H. induction H; intros GET. 
  - rewrite ACCEPT in GET. inversion GET. constructor.
  - apply action_rep_start in ACTION as [EQ | [instr [GETSTART START]]].
    + subst. apply IHactions_rep. auto.
    + rewrite GETSTART in GET. inversion GET. subst. auto.
  - rewrite JMP in GET. inversion GET. constructor.
Qed.

(* rephrasing the lemma below so that induction handles pairs better *)
Lemma tt_same_interm:
  forall code inp treegm1 treegm2 thread1 thread2 n1 n2
    (TT1: tree_thread code inp treegm1 thread1 n1)
    (TT2: tree_thread code inp treegm2 thread2 n2)
    (SAMEPC: fst (fst thread1) = fst (fst thread2))
    (SAMEB: snd thread1 = snd thread2)
    (SAMEGM1: snd (fst thread1) = snd treegm1)
    (SAMEGM2: snd (fst thread2) = snd treegm2),
    fst treegm1 = fst treegm2.
Proof.
  intros code inp treegm1 treegm2 thread1 thread2 n1 n2 TT1.
  generalize dependent n2. generalize dependent thread2. generalize dependent treegm2.
  induction TT1; intros; subst.
  - inversion TT2; subst;
      simpl in SAMEB; simpl in SAMEPC; simpl in SAMEGM1; simpl in SAMEGM2; subst;
      try solve[eapply actions_rep_start in CONT; eauto; inversion CONT].
    simpl. subst. symmetry. eapply actions_rep_unicity in CONT; eauto.
  - inversion TT2; subst;
      simpl in SAMEB; simpl in SAMEPC; simpl in SAMEGM1; simpl in SAMEGM2; subst;
      try solve[eapply actions_rep_start in CONT; eauto; inversion CONT].
    2: { rewrite BEGIN in RESET. inversion RESET. }
    rewrite RESET in RESET0. inversion RESET0. subst.
    specialize (IHTT1 _ _ _ TT (eq_refl _) (eq_refl _) (eq_refl _) (eq_refl _)).
    simpl in IHTT1. destruct IHTT1. subst. simpl. auto.
  - inversion TT2; subst;
      simpl in SAMEB; simpl in SAMEPC; simpl in SAMEGM1; simpl in SAMEGM2; subst;
      try solve[eapply actions_rep_start in CONT; eauto; inversion CONT].
    { rewrite BEGIN in RESET. inversion RESET. }
    specialize (IHTT1 _ _ _ TT (eq_refl _) (eq_refl _) (eq_refl _) (eq_refl _)).
    simpl in IHTT1. destruct IHTT1. subst. simpl. auto.
Qed.

Lemma tt_same_tree:
  forall code inp t1 gm1 t2 gm2 n1 n2 pc b
    (TT1: tree_thread code inp (t1,gm1) (pc,gm1,b) n1)
    (TT2: tree_thread code inp (t2,gm2) (pc,gm2,b) n2),
    t1 = t2.
Proof.
  intros code inp t1 gm1 t2 gm2 n1 n2 pc b TT1 TT2.
  eapply tt_same_interm in TT1; eauto. simpl in TT1. auto.
Qed.

(** * Seen Lemmas *)


Lemma initial_inclusion:
  forall c inp current currentpc,
    seen_inclusion c inp initial_seentrees initial_seenpcs current currentpc.
Proof.
  intros c inp current currentpc. unfold seen_inclusion. intros pc b SEEN.
  rewrite initial_nothing_pc in SEEN. inversion SEEN.
Qed.

Lemma add_inclusion:
  forall treeseen threadseen c inp t pc gm b n nextcurrent nextpc
    (INCL: seen_inclusion c inp treeseen threadseen (Some (t,gm)) pc)
    (TT: tree_thread c inp (t,gm) (pc,gm,b) n),
    seen_inclusion c inp (add_seentrees treeseen t) (add_thread threadseen (pc, gm, b)) nextcurrent nextpc.
Proof.
  intros treeseen threadseen c inp t pc gm b n nextcurrent nextpc INCL TT.
  unfold seen_inclusion in *.
  intros pc0 b0 SEEN. apply inpc_add in SEEN. destruct SEEN as [EQ|SEEN].
  - inversion EQ. subst. left. exists t. exists gm. exists n. split; auto. apply in_add. left. auto.
  - specialize (INCL pc0 b0 SEEN).      
    destruct INCL as [[ts [gms [ns [SEENs TTs]]]] | [ST [ms [ts [gms [GEQ [EQ TTS]]]]]]].
    + left. exists ts. exists gms. exists ns. split; auto. apply in_add. right; auto.
    + left. exists ts. exists gms. exists ms. split; auto.
      apply in_add. left; auto. inversion EQ. auto.
Qed.

Lemma skip_inclusion:
  forall code inp treeseen threadseen tree gm currentpc
    (INCL: seen_inclusion code inp treeseen threadseen (Some (tree, gm)) currentpc)
    (SEEN: inseen treeseen tree = true),
  forall current nextpc,
    seen_inclusion code inp treeseen threadseen current nextpc.
Proof.
  intros code inp treeseen threadseen tree gm currentpc INCL SEEN current nextpc.
  unfold seen_inclusion in *.
  intros pc b SEENPC.
  specialize (INCL pc b SEENPC).
  destruct INCL as [[ts [gms [ns [SEENs TTs]]]] | [ST [ms [ts [gms [GEQ [EQ TTS]]]]]]].
  - left. exists ts. exists gms. exists ns. split; auto.
  - left. exists ts. exists gms. exists ms. split; auto. inversion EQ. subst. auto.
Qed.

Lemma stutter_inclusion:
  forall code inp treeseen threadseen t gm n pc b nextpc
    (GT: pc < nextpc )
    (INCL: seen_inclusion code inp treeseen threadseen (Some (t, gm)) pc)
    (STUTTERS: stutters pc code = true)
    (TT: tree_thread code inp (t,gm) (pc,gm,b) n),
    seen_inclusion code inp treeseen (add_seenpcs threadseen pc b) (Some (t,gm)) nextpc.
Proof.
  intros code inp treeseen threadseen t gm n pc b nextpc GT INCL STUTTERS TT.
  unfold seen_inclusion in *.
  intros pc0 b0 SEEN.
  apply inpc_add in SEEN. destruct SEEN as [EQ | SEEN].
  { inversion EQ. subst. right. split; auto.
    exists n. exists t. exists gm. split; auto. }
  specialize (INCL pc0 b0 SEEN).
  destruct INCL as [[ts [gms [ns [SEENs TTs]]]] | [ST [ms [ts [gms [GEQ [EQ TTS]]]]]]].
  - left. exists ts. exists gms. exists ns. split; auto.
  - right. split; auto. exists ms. exists ts. exists gms. split; auto. lia.
Qed.

(** * Code Stuttering Well-formedness *)
(* to show that a stuttering step cannot lead the PikeVM to immediately memoize something that was not memoized by the PikeTree, we need to show that stutteing instructions always point to a greater pc *)

Definition stutter_wf (code:code) : Prop :=
  forall pc gm b nextpc nextgm nextb inp,
    stutters pc code = true ->
    epsilon_step (pc,gm,b) code inp = EpsActive[(nextpc,nextgm,nextb)] ->
    pc < nextpc.

Lemma nth_nil:
  forall (A:Type) i, @nth_error A [] i = None.
Proof.
  intros A i. destruct i; simpl; auto.
Qed.

Lemma nfa_rep_incr:
  forall r code start endl,
    nfa_rep r code start endl ->
    start <= endl.
Proof.
  intros r code start endl H. induction H; try lia.
Qed.

(* every jump in the code jumps to a strictly bigger label *)
(* this will help prevent loops of stuttering steps in the PikeVM *)
Lemma compile_jumps:
  forall r code start endl pc next,
    nfa_rep r code start endl ->
    pc >= start ->
    pc < endl ->
    get_pc code pc = Some (Jmp next) ->
    pc < next.
Proof.
  intros r code start endl pc next REP GE LT GET.
  generalize dependent pc. induction REP; intros.
  - lia.
  - assert (pc = lbl) by lia. subst.
    rewrite CONSUME in GET. inversion GET.
  - apply nfa_rep_incr in REP1 as INCR1.
    apply nfa_rep_incr in REP2 as INCR2.
    assert (pc = start \/ pc >= S start) as [ST|H] by lia.
    (* Fork *)
    { subst. rewrite FORK in GET. inversion GET. }
    assert (pc < end1 \/ pc >= end1) as [R1|H1] by lia.
    (* in r1 *)
    { apply IHREP1; auto. }
    assert (pc = end1 \/ pc >= S end1) as [J|H2] by lia.
    (* the jmp *)
    { subst. rewrite JMP in GET. inversion GET. lia. }
    (* in r2 *)
    apply IHREP2; auto.
  - apply nfa_rep_incr in REP1 as INCR1.
    apply nfa_rep_incr in REP2 as INCR2.
    assert (pc < end1 \/ pc >= end1) as [H1|H2] by lia.
    (* in r1 *)
    { apply IHREP1; auto. }
    (* in r2 *)
    apply IHREP2; auto.
  - apply nfa_rep_incr in REP as INC.
    assert (pc = start \/ pc >= S start) as [FOR|H] by lia.
    (* fork *)
    { subst. rewrite FORK in GET. destruct greedy; inversion GET. }
    assert (pc = S start \/ pc >= S (S start)) as [BEG|H1] by lia.
    (* Begin *)
    { subst. rewrite BEGIN in GET. inversion GET. }
    assert (pc = S (S start) \/ pc >= S (S (S start))) as [RES|H2] by lia.
    (* Reset *)
    { subst. rewrite RESET in GET. inversion GET. }
    assert (pc < end1 \/ pc = end1) as [R1|H3] by lia.
    (* in r1 *)
    { apply IHREP; auto. }
    (* endloop *)
    subst. rewrite END in GET. inversion GET.
  - apply nfa_rep_incr in REP as INC.
    assert (pc = start \/ pc >= S start) as [ST|H] by lia.
    (* open *)
    { subst. rewrite OPEN in GET. inversion GET. }
    assert (pc = end1 \/ pc < end1) as [END|H1] by lia.
    (* close *)
    { subst. rewrite CLOSE in GET. inversion GET. }
    (* in r1 *)
    apply IHREP; auto.
  - assert (pc = lbl) by lia. subst.
    rewrite KILL in GET. inversion GET.
Qed.


(* every compiled code is well-formed *)
Lemma compile_stutter_wf:
  forall r code fresh,
    compile r 0 = (code, fresh) ->
    stutter_wf code.
Proof.
  intros r code fresh H.
  eapply compile_nfa_rep with (prev:=[]) in H as REP; simpl; auto.
  simpl in REP. apply fresh_correct in H. simpl in H. subst.
  unfold stutter_wf. unfold stutters. unfold get_pc.
  intros pc gm b nextpc nextgm nextb inp H H0.
  destruct (nth_error code pc) eqn:NTH.
  2: { inversion H. }
  destruct b0; inversion H; simpl in H0; unfold get_pc in H0; rewrite NTH in H0;
    inversion H0; subst; try lia.
  eapply compile_jumps; eauto; try lia.
  apply nth_error_Some. rewrite NTH. intros HI. inversion HI.
Qed.

Theorem compilation_stutter_wf:
  forall r code,
    compilation r = code ->
    stutter_wf code.
Proof.
  unfold compilation. intros r code H.
  destruct (compile r 0) as [r_code fresh] eqn:COMP. subst.
  apply compile_stutter_wf in COMP.
  unfold stutter_wf, stutters, get_pc.
  intros pc gm b nextpc nextgm nextb inp H H0.
  destruct (nth_error (r_code ++ [Accept]) pc) eqn:NTH.
  2: { inversion H. }
  assert (HL: pc < length (r_code ++ [Accept])).
  { eapply nth_error_Some. rewrite NTH. intros HI. inversion HI. }
  rewrite app_length in HL. simpl in HL.
  assert (pc = length (r_code) \/ pc < length (r_code)) as [ACC|H1] by lia.
  (* accept *)
  { subst. assert (get_pc (r_code ++ [Accept]) (length r_code) = get_pc [Accept] 0).
    - apply get_first.
    - unfold get_pc in H1. simpl in H1. rewrite H1 in NTH. inversion NTH. subst.
      inversion H. }
  (* inside the code *)
  assert (get_pc r_code pc = Some b0).
  { rewrite nth_error_app1 in NTH; auto. }
  unfold stutter_wf in COMP.
  assert (epsilon_step (pc,gm,b) r_code inp = EpsActive [(nextpc,nextgm,nextb)]).
  { simpl in H0. unfold get_pc in H0. rewrite NTH in H0.
    simpl. rewrite H2.
    destruct b0; auto. }
  eapply COMP; eauto.
  unfold stutters. rewrite H2. destruct b0; auto.
Qed.

  


(** * Invariant Initialization  *)

(* the initial states of both smallstep semantics are related with the invariant *)
Lemma initial_pike_inv:
  forall r inp tree code
    (TREE: bool_tree [Areg r] inp CanExit tree)
    (COMPILE: compilation r = code)
    (SUBSET: pike_regex r),
    pike_inv code (pike_tree_seen_initial_state tree inp) (pike_vm_seen_initial_state inp) 0.
Proof.
  intros r inp tree code TREE COMPILE SUBSET.
  unfold compilation in COMPILE. destruct (compile r 0) as [c fresh] eqn:COMP.
  apply compile_nfa_rep with (prev := []) in COMP as REP; auto. simpl in REP.
  apply fresh_correct in COMP. simpl in COMP. subst.
  eapply pikeinv; auto.
  - econstructor.
    + constructor.
    + apply tt_eq with (actions:=[Areg r]); auto.
      2: { pike_subset. }
      eapply cons_bc; constructor.
      * apply nfa_rep_extend; eauto.
      * replace (length c) with (length c + 0) by auto.
        rewrite get_prefix. auto.
  - constructor.
  - apply initial_inclusion.
  - simpl. auto.
Qed.

(** * Invariant Preservation  *)

(* identifying states of the VM that are going to take a skip step *)
Definition skip_state (pvs:pike_vm_seen_state) : bool :=
  match pvs with
  | PVSS_final _ => false
  | PVSS inp active best blocked seen =>
      match active with
      | [] => false
      | (pc,gm,b)::active => inseenpc seen pc b
      end
  end.
  

Theorem invariant_preservation:
  forall code pts1 pvs1 n pvs2
    (STWF: stutter_wf code)
    (INV: pike_inv code pts1 pvs1 n)
    (VMSTEP: pike_vm_seen_step code pvs1 pvs2),
    (* either we make a step on both sides, preserving invariant *)
    (
      exists pts2 m,
        pike_tree_seen_step pts1 pts2 /\
          pike_inv code pts2 pvs2 m
    )
    \/
      (* or we make a stuttering step, preserving invariant and reducing measure *)
      (
        exists m,
          pike_inv code pts1 pvs2 m /\
            m < n
      ).
Proof.
  intros code pts1 pvs1 n pvs2 STWF INV VMSTEP.
  inversion INV; subst.
  (* Final states make no step *)
  2: { inversion VMSTEP. }
  destruct (skip_state (PVSS inp threadactive best threadblocked threadseen)) eqn:SKIP.
  (* skip states are performed in lockstep *)
  { left. destruct threadactive as [|[[pc gm] b] active]; simpl in SKIP.
    { inversion SKIP. }
    destruct treeactive as [|[tree gmt] treeactive]; inversion ACTIVE; subst.
    inversion VMSTEP; subst; try simpl in UNSEEN;
      try rewrite UNSEEN in SKIP; inversion SKIP.    
    apply SEEN in SKIP as [[teq [gmeq [neq [SEENEQ TTEQ]]]] | [STUTTER [m [t' [gm' [GEQ [EQ TTS]]]]]]].
    - assert (teq = tree).
      { eapply tt_same_tree; eauto. }
      subst.
      exists (PTSS inp treeactive best treeblocked treeseen).
      exists (hd 0 (measurelist ++ measureblocked)).
      split.
      + apply ptss_skip; auto.
      + eapply pikeinv; eauto.
        simpl in SEEN. eapply skip_inclusion; eauto.
    - simpl in GEQ. lia.
  }
  destruct treeactive as [|[t gm] treeactive].
  {
    (* no more active trees or threads *)
    inversion ACTIVE; subst.
    destruct treeblocked as [|[tblocked gmblocked] treeblocked].
    (* final step *)
    - assert (pvs2 = (PVSS_final best)).
      { eapply pikevm_deterministic; eauto.
        destruct (advance_input inp) eqn:ADV; try solve[constructor; auto].
        specialize (BLOCKED i (eq_refl (Some i))). inversion BLOCKED; subst. constructor. }
      subst. left. exists (PTSS_final best). exists 0. split; constructor.
    (* nextchar *)
    - destruct (advance_input inp) eqn:ADV.
      2: { specialize (ENDTREE (eq_refl None)). inversion ENDTREE. }
      specialize (BLOCKED i (eq_refl (Some i))). inversion BLOCKED; subst.
      assert (pvs2 = PVSS i ((pc,gmblocked,b)::threadlist) best [] initial_seenpcs).
      { eapply pikevm_deterministic; eauto. constructor. auto. }
      subst. left. exists (PTSS i ((tblocked,gmblocked)::treeblocked) best [] initial_seentrees).
      apply advance_next in ADV. subst.
      exists n. split; try econstructor; eauto.
      + intros nextinp H. constructor.
      + apply initial_inclusion.
  }
  (* there is an active tree/thread *)
  destruct threadactive as [|[[pc gm'] b] threadactive]; inversion ACTIVE; subst.
  rename gm' into gm.
  destruct (stutters pc code) eqn:STUTTERS.
  {
    (* stuttering step *)
    right. apply stutter_step in TT as H; auto.
    destruct H as [nextpc [nextb [m [EPSSTEP [TT2 LESS]]]]]; subst.
    exists m. assert (pvs2 = (PVSS inp ([(nextpc, gm, nextb)] ++ threadactive) best threadblocked (add_thread threadseen (pc,gm,b)))).
    { eapply pikevm_deterministic; eauto. eapply pvss_active; eauto. }
    split; subst; simpl; auto. eapply pikeinv with (measureactive:=m::measurelist); simpl; eauto.
    - constructor; eauto.
    - (* Here we use that the code is stutter-well-formed *)
      simpl in SEEN. eapply stutter_inclusion; eauto.
  }
  destruct (tree_bfs_step t gm (idx inp)) eqn:TREESTEP.
  (* active *)
  - left. eapply generate_active in TREESTEP as H; eauto. destruct H as [newthreads [measure [EPS LTT2]]].
    assert (pvs2 = PVSS inp (newthreads ++ threadactive) best threadblocked (add_thread threadseen (pc,gm,b))).
    { eapply pikevm_deterministic; eauto. constructor; auto. }
    subst. exists (PTSS inp (l ++ treeactive) best treeblocked (add_seentrees treeseen t)). exists (hd 0 ((measure ++ measurelist) ++ measureblocked)). split.
    + eapply ptss_active; eauto.
    + eapply pikeinv; try (eapply add_inclusion; eauto); try constructor; eauto.
      apply ltt_app; eauto.
  (* match *)
  - left. eapply generate_match in TREESTEP as THREADSTEP; eauto.
    assert (pvs2 = PVSS inp [] (Some (inp,gm_of (pc,gm,b))) threadblocked (add_thread threadseen (pc,gm,b))).
    { eapply pikevm_deterministic; eauto. constructor; auto. }
    subst. exists (PTSS inp [] (Some (inp,gm)) treeblocked (add_seentrees treeseen t)). exists (hd 0 ([] ++ measureblocked)). split.
    + constructor; auto.
    + eapply pikeinv; try (eapply add_inclusion; eauto); try constructor; eauto.
  (* blocked *)
  - left. specialize (generate_blocked _ _ _ _ _ _ _ _ TREESTEP STUTTERS TT) as [EPS2 [TT2 [nexti ADVANCE]]].
    assert (pvs2 = PVSS inp threadactive best (threadblocked ++ [(pc+1,gm,CanExit)]) (add_thread threadseen (pc,gm,b))).
    { eapply pikevm_deterministic; eauto. constructor; auto. }
    subst. exists (PTSS inp treeactive best (treeblocked ++ [(t0,gm)]) (add_seentrees treeseen t)). exists (hd 0 (measurelist ++ measureblocked ++ [n])). split.
    + eapply ptss_blocked; eauto.
    + eapply pikeinv; try (eapply add_inclusion; eauto); try constructor; eauto.
      2: { intros H. rewrite ADVANCE in H. inversion H. }
      2: { intros H. rewrite ADVANCE in H. inversion H. }
      intros nextinp H. specialize (BLOCKED nextinp H).
      apply ltt_app; eauto. specialize (TT2 nextinp H).
      eapply ltt_cons. constructor. auto.
Qed.
