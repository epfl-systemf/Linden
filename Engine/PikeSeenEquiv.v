(* Relating the PikeVM smallstep semantics to the Pike Tree smallstep semantics *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeTree PikeVM.
From Linden Require Import PikeTreeSeen PikeVMSeen.
From Linden Require Import PikeEquiv PikeSubset.
From Warblre Require Import Base.

(** * Simulation Invariant  *)

(* This is not, strictly speaking, an inclusion, which explains the second case of this disjunction *)
(* Sometimes, we add seen pcs on the VM side that do not corrspond yet to any seen tree on the tree side *)
(* this happens during stuttering steps: such pcs are always stuttering, equivalent to the current active tree, *)
(* and for a measure that's bigger than the current one *)
Definition seen_inclusion (c:code) (inp:input) (treeseen:seentrees) (threadseen:seenpcs) (current:option (tree*group_map)) (n:nat): Prop :=
  forall pc b
    (SEEN: inseenpc threadseen pc b = true),
  (exists t gm n,
      inseen treeseen t = true /\
        tree_thread c inp (t, gm) (pc, gm, b) n)
  \/
    (stutters pc c = true /\
       exists m t gm, m > n /\ current = Some (t,gm) /\
              tree_thread c inp (t,gm) (pc,gm,b) m).


Inductive pike_inv (code:code): pike_tree_seen_state -> pike_vm_seen_state -> nat -> Prop :=
| pikeinv:
  forall inp idx treeactive treeblocked threadactive threadblocked best treeseen threadseen measureactive measureblocked n
    (ACTIVE: list_tree_thread code inp treeactive threadactive measureactive)
    (* blocked threads should be equivalent for the next input *)
    (* nothing to say if there is no next input *)
    (BLOCKED: forall nextinp, advance_input inp forward = Some nextinp -> list_tree_thread code nextinp treeblocked threadblocked measureblocked)
    (* these two properties are needed to ensure the two algorithms stop at he same time *)
    (ENDVM: advance_input inp forward = None -> threadblocked = [])
    (ENDTREE: advance_input inp forward = None -> treeblocked = [])
    (* any pc in threadseen must correspond to a tree in treeseen *)
    (SEEN: seen_inclusion code inp treeseen threadseen (hd_error treeactive) n)
    (* the measure is simply the measure of the top priority thread *)
    (MEASURE: n = hd 0 (measureactive++measureblocked)),
    pike_inv code (PTSS idx treeactive best treeblocked treeseen) (PVSS inp idx threadactive best threadblocked threadseen) n
| pikeinv_final:
  forall best,
    pike_inv code (PTSS_final best) (PVSS_final best) 0.


(** * Seen Lemmas *)

(* tree-thread equivalence can only happen for a single gm *)
Lemma tt_same_gm:
  forall t gm1 pc gm2 b code inp n,
    tree_thread code inp (t,gm1) (pc,gm2,b) n -> gm1 = gm2.
Proof.
  intros t gm1 pc gm2 b code inp n H. inversion H; auto.
Qed.

Lemma initial_inclusion:
  forall c inp current n,
    seen_inclusion c inp initial_seentrees initial_seenpcs current n.
Proof.
  intros c inp current n. unfold seen_inclusion. intros pc b SEEN.
  rewrite initial_nothing_pc in SEEN. inversion SEEN.
Qed.

Lemma add_inclusion:
  forall treeseen threadseen c inp t pc gm b n nextcurrent nextn
    (INCL: seen_inclusion c inp treeseen threadseen (Some (t,gm)) n)
    (TT: tree_thread c inp (t,gm) (pc,gm,b) n),
    seen_inclusion c inp (add_seentrees treeseen t) (add_thread threadseen (pc, gm, b)) nextcurrent nextn.
Proof.
  intros treeseen threadseen c inp t pc gm b n nextcurrent nextn INCL TT.
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
  forall code inp treeseen threadseen tree gm n
    (INCL: seen_inclusion code inp treeseen threadseen (Some (tree, gm)) n)
    (SEEN: inseen treeseen tree = true),
  forall current m,
    seen_inclusion code inp treeseen threadseen current m.
Proof.
  intros code inp treeseen threadseen tree gm n INCL SEEN current m.
  unfold seen_inclusion in *.
  intros pc b SEENPC.
  specialize (INCL pc b SEENPC).
  destruct INCL as [[ts [gms [ns [SEENs TTs]]]] | [ST [ms [ts [gms [GEQ [EQ TTS]]]]]]].
  - left. exists ts. exists gms. exists ns. split; auto.
  - left. exists ts. exists gms. exists ms. split; auto. inversion EQ. subst. auto.
Qed.

Lemma stutter_inclusion:
  forall code inp treeseen threadseen t gm m pc b
    (INCL: seen_inclusion code inp treeseen threadseen (Some (t, gm)) (S m))
    (STUTTERS: stutters pc code = true)
    (TT: tree_thread code inp (t,gm) (pc,gm,b) (S m)),
    seen_inclusion code inp treeseen (add_seenpcs threadseen pc b) (Some (t,gm)) m.
Proof.
  intros code inp treeseen threadseen t gm m pc b INCL STUTTERS TT.
  unfold seen_inclusion in *.
  intros pc0 b0 SEEN.
  apply inpc_add in SEEN. destruct SEEN as [EQ | SEEN].
  { inversion EQ. subst. right. split; auto.
    exists (S m). exists t. exists gm. split; auto. }
  specialize (INCL pc0 b0 SEEN).
  destruct INCL as [[ts [gms [ns [SEENs TTs]]]] | [ST [ms [ts [gms [GEQ [EQ TTS]]]]]]].
  - left. exists ts. exists gms. exists ns. split; auto.
  - right. split; auto. exists ms. exists ts. exists gms. split; auto. lia.
Qed.


(** * Representation Unicity lemmas  *)

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

    

(* even though nfa_rep can hold at the same place for two regexes, they should have the same tree *)
(* the issue with that lemma is that I'm not guaranteed that I will get two list of actions that coincide on the intermediate pcs *)
(* Lemma nfa_rep_unicity: *)
(*   forall r1 r2 code pc pcend t inp b, *)
(*     nfa_rep r1 code pc pcend -> *)
(*     nfa_rep r2 code pc pcend -> *)
(*     bool_tree [Areg r1] inp b t -> *)
(*     bool_tree [Areg r2] inp b t. *)
(* Admitted. *)

(* one possible solution: *)
(* I could show that if I have two actions_rep at the same pc, these list of actions are equivalent *)
(* Equivalence of actions would be up to
   - splitting sequences
   - adding epsilon
 *)
(* Then, I could prove that two equivalent lists of actions give the same tree  *)
(* Would that be easier? Or not? *)

Lemma accept_same_n:
  forall code pc n1 n2,
    actions_rep [] code pc n1 ->
    actions_rep [] code pc n2 ->
    n1 = n2.
Proof.
  intros code pc n1 n2 H H0.
  remember [] as NIL. generalize dependent n2.
  induction H; intros.
  - inversion H0; subst; auto.
    rewrite JMP in ACCEPT. inversion ACCEPT.
  - inversion HeqNIL.
  - subst. destruct n2 as [|n2].
    { inversion H0; subst.
      rewrite ACCEPT in JMP. inversion JMP. }
    inversion H0; subst. rewrite JMP in  JMP0. inversion JMP0. subst.
    simpl. f_equal. apply IHactions_rep; auto.
Qed.
(* is this strong enough? *)
(* it's only when we have the same list of actions, but we could try to match epsilon for instance *)


Lemma accept_same_n':
  forall code pc act n1 n2,
    actions_rep [] code pc n1 ->
    actions_rep act code pc n2 ->
    n1 = n2.
Proof.
  intros code pc act n1 n2 H H0.
  remember [] as NIL. generalize dependent n2. generalize dependent act.
  induction H; intros.
  - induction H0; auto.
    + assert (pcstart = pcmid) by admit.
      (* because we know that we have accept, there should be no way to end somewhere else *)
      subst. apply IHactions_rep. auto.
    + rewrite JMP in ACCEPT. inversion ACCEPT.
  - inversion HeqNIL.
  - induction H0; auto.
    + rewrite ACCEPT in JMP. inversion JMP.
    +                           (* one has jumped, the other represents an action *)
      assert (pcstart0 = pcmid) by admit.
    (* again, we know that we have a jmp at the start, so the representation cannot end somewhere else *)
      subst. eapply IHactions_rep0; eauto.
    + rewrite JMP0 in JMP. inversion JMP. subst. f_equal.
      eapply IHactions_rep; eauto.
Admitted.


Lemma act_rep_same_n:
  forall code pc act1 act2 n1 n2,
    actions_rep act1 code pc n1 ->
    actions_rep act2 code pc n2 ->
    n1 = n2.
Proof.
  intros code pc act1 act2 n1 n2 H H0.
  generalize dependent act2. generalize dependent n2.
  induction H; intros.
  - eapply accept_same_n'; eauto.
    constructor; auto.
  - admit.
  (* should be difficult *)
  (* while the first rep stops at pcmid, we don't know if the other one also stops at pcmid *)
  (* so it will be hard to ever use the induction hypothesis *)
  - induction H0.
    + rewrite ACCEPT in JMP. inversion JMP.
    + assert (pcstart0 = pcmid) by admit.
      (* should be ok *)
      subst. eapply IHactions_rep0; eauto.
    + rewrite JMP0 in JMP. inversion JMP. subst. f_equal.
      eapply IHactions_rep; eauto.
Abort.


Lemma match_unicity:
  forall a1 a2 code pc inp b n,
    actions_rep a1 code pc n ->
    actions_rep a2 code pc n ->
    bool_tree a1 inp b Match ->
    bool_tree a2 inp b Match.
Proof.
  intros a1 a2 code pc inp b n H H0 H1.
  generalize dependent a2. generalize dependent pc.
  remember Match as tmatch.
  induction H1; intros;
    try solve[inversion Heqtmatch].
  - admit.
  - inversion H; subst.
    + apply IHbool_tree in CONT; auto. admit. (* don't think I can conclude *)
    + admit.
Abort.

              


(* (* same for actions *) *)
Lemma actions_rep_unicity:
  forall a1 a2 code pc t inp b n,
    actions_rep a1 code pc n ->
    actions_rep a2 code pc n ->
    bool_tree a1 inp b t ->
    bool_tree a2 inp b t.
Proof.
  intros a1 a2 code pc t inp b n H H0 H1.
  induction H.
  - inversion H1; subst. inversion H0; subst.
    2: { admit.                 (* we could have epsilon:[] *)
         (* this one should be by induction on H1 *)
    }

    (* another induction *)
  (* intros a1 a2 code pc t inp b n H H0 H1. *)
  (* induction H1. *)
  (* -                             (* even this one is an induction on n, or on actions_rep (H) *) *)
  (*   (* since we can have as many jumps before the match *) *)
Admitted.


(* should I prove this one at the same time as the one above? *)
Lemma actions_rep_same_n:
  forall code pc n1 act1 n2 act2
    (AREP1: actions_rep act1 code pc n1)
    (AREP2: actions_rep act2 code pc n2),
    n1 = n2.
Proof.
Admitted.

(* rephrasing the lemma below so that induction handles pairs better *)
Lemma tt_same_interm:
  forall code inp treegm1 treegm2 thread1 thread2 n1 n2
    (TT1: tree_thread code inp treegm1 thread1 n1)
    (TT2: tree_thread code inp treegm2 thread2 n2)
    (SAMEPC: fst (fst thread1) = fst (fst thread2))
    (SAMEB: snd thread1 = snd thread2)
    (SAMEGM1: snd (fst thread1) = snd treegm1)
    (SAMEGM2: snd (fst thread2) = snd treegm2),
    fst treegm1 = fst treegm2 /\ n1 = n2.
Proof.
  intros code inp treegm1 treegm2 thread1 thread2 n1 n2 TT1.
  generalize dependent n2. generalize dependent thread2. generalize dependent treegm2.
  induction TT1; intros; subst.
  - inversion TT2; subst;
      simpl in SAMEB; simpl in SAMEPC; simpl in SAMEGM1; simpl in SAMEGM2; subst;
      try solve[eapply actions_rep_start in CONT; eauto; inversion CONT].
    simpl.
    (* this one is unclear. How do we prevent jumps to ourselves? *)
    (* maybe I need to have the property that all Jumps jump to a strictly higher index *)
    assert (n = n2) by admit.
    subst. split; auto. eapply actions_rep_unicity in CONT; eauto.
    eapply bool_tree_determ; eauto.
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
Admitted.



Lemma tt_same:
  forall code inp t1 t2 gm1 gm2 pc b n1 n2
    (TT1: tree_thread code inp (t1,gm1) (pc,gm1,b) n1)
    (TT2: tree_thread code inp (t2,gm2) (pc,gm2,b) n2),
    t1 = t2 /\ n1 = n2.
Proof.
  intros code inp t1 t2 gm1 gm2 pc b n1 n2 TT1 TT2.
  eapply tt_same_interm in TT1; eauto. simpl in TT1. destruct TT1.
  split; auto.
Qed.


Lemma tt_same_measure:
  forall code inp t gm pc b n1 n2
    (TT1: tree_thread code inp (t,gm) (pc,gm,b) n1)
    (TT2: tree_thread code inp (t,gm) (pc,gm,b) n2),
    n1 = n2.
Proof.
  intros code inp t gm pc b n1 n2 TT1 TT2.
  eapply tt_same in TT1; eauto. destruct TT1. auto.
Qed.


(* would this be easier if we made the tree explicit in the relation? *)
(* note that nfa_rep has no unicity prop: we could represent both epsilon and epsilon:epsilon *)
(* same goes for actions_rep *)
(* but in these cases, even from different actions, the trees are still the same *)
(* could we compute a tree from a pc and an input? compute_tree pc inp *)
(* then show tt code inp (t,gm) (pc,_,_) -> t = compute_tree pc inp *)
(* Another idea is that even though multiple actions could correspond to the same pc *)
(* when they are compiled each pc corresponds to a precise set of actions? *)
(* no, it depends on the input for stars *)
(* But I should be able to use th generate lemmas if my intermediate theorem uses a tree derivation to build another *)
Lemma tt_same_tree:
  forall code inp t1 gm1 t2 gm2 n1 n2 pc b
    (TT1: tree_thread code inp (t1,gm1) (pc,gm1,b) n1)
    (TT2: tree_thread code inp (t2,gm2) (pc,gm2,b) n2),
    t1 = t2.
Proof.
  intros code inp t1 gm1 t2 gm2 n1 n2 pc b TT1 TT2.
  eapply tt_same in TT1; eauto. destruct TT1. auto.
Qed.



(** * Invariant Initialization  *)

(* the initial states of both smallstep semantics are related with the invariant *)
Lemma initial_pike_inv:
  forall r inp tree code
    (TREE: bool_tree [Areg r] inp CanExit tree)
    (COMPILE: compilation r = code)
    (SUBSET: pike_regex r),
    pike_inv code (pike_tree_seen_initial_state tree) (pike_vm_seen_initial_state inp) 0.
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
  | PVSS inp idx active best blocked seen =>
      match active with
      | [] => false
      | (pc,gm,b)::active => inseenpc seen pc b
      end
  end.
  

Theorem invariant_preservation:
  forall code pts1 pvs1 n pvs2
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
  intros code pts1 pvs1 n pvs2 INV VMSTEP.
  inversion INV; subst.
  (* Final states make no step *)
  2: { inversion VMSTEP. }
  destruct (skip_state (PVSS inp idx threadactive best threadblocked threadseen)) eqn:SKIP.
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
      exists (PTSS idx treeactive best treeblocked treeseen).
      exists (hd 0 (measurelist ++ measureblocked)).
      split.
      + apply ptss_skip; auto.
      + eapply pikeinv; eauto.
        simpl in SEEN. eapply skip_inclusion; eauto.
    - simpl in EQ. inversion EQ. subst. simpl in GEQ.
      assert (m = n).
      { eapply tt_same_measure; eauto. }
      subst. exfalso. eapply PeanoNat.Nat.lt_irrefl; eauto.
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
      assert (pvs2 = PVSS i (idx+1) ((pc,gmblocked,b)::threadlist) best [] initial_seenpcs).
      { eapply pikevm_deterministic; eauto. constructor. auto. }
      subst. left. exists (PTSS (idx+1) ((tblocked,gmblocked)::treeblocked) best [] initial_seentrees). exists n. split; econstructor; eauto.
      + intros nextinp H. constructor.
      + apply initial_inclusion.
  }
  (* there is an active tree/thread *)
  destruct threadactive as [|[[pc gm'] b] threadactive]; inversion ACTIVE; subst.
  rename gm' into gm.
  destruct (stutters pc code) eqn:STUTTERS.
  {
    (* stuttering step *)
    right. apply stutter_step with (idx:=idx) in TT as H; auto.
    destruct H as [nextpc [nextb [m [EPSSTEP [TT2 LESS]]]]]; subst.
    exists m. assert (pvs2 = (PVSS inp idx ([(nextpc, gm, nextb)] ++ threadactive) best threadblocked (add_thread threadseen (pc,gm,b)))).
    { eapply pikevm_deterministic; eauto. eapply pvss_active; eauto. }
    split; subst; simpl; auto. eapply pikeinv with (measureactive:=m::measurelist); simpl; eauto.
    - constructor; eauto.
    - simpl in SEEN. apply stutter_inclusion; auto.
  }
  destruct (tree_bfs_step t gm idx) eqn:TREESTEP.
  (* active *)
  - left. eapply generate_active in TREESTEP as H; eauto. destruct H as [newthreads [measure [EPS LTT2]]].
    assert (pvs2 = PVSS inp idx (newthreads ++ threadactive) best threadblocked (add_thread threadseen (pc,gm,b))).
    { eapply pikevm_deterministic; eauto. constructor; auto. }
    subst. exists (PTSS idx (l ++ treeactive) best treeblocked (add_seentrees treeseen t)). exists (hd 0 ((measure ++ measurelist) ++ measureblocked)). split.
    + eapply ptss_active; eauto.
    + eapply pikeinv; try (eapply add_inclusion; eauto); try constructor; eauto.
      apply ltt_app; eauto.
  (* match *)
  - left. eapply generate_match in TREESTEP as THREADSTEP; eauto.
    assert (pvs2 = PVSS inp idx [] (Some (gm_of (pc,gm,b))) threadblocked (add_thread threadseen (pc,gm,b))).
    { eapply pikevm_deterministic; eauto. constructor; auto. }
    subst. exists (PTSS idx [] (Some gm) treeblocked (add_seentrees treeseen t)). exists (hd 0 ([] ++ measureblocked)). split.
    + constructor; auto.
    + eapply pikeinv; try (eapply add_inclusion; eauto); try constructor; eauto.
  (* blocked *)
  - left. specialize (generate_blocked _ _ _ _ _ _ _ _ _ TREESTEP STUTTERS TT) as [EPS2 [TT2 [nexti ADVANCE]]].
    assert (pvs2 = PVSS inp idx threadactive best (threadblocked ++ [(pc+1,gm,CanExit)]) (add_thread threadseen (pc,gm,b))).
    { eapply pikevm_deterministic; eauto. constructor; auto. }
    subst. exists (PTSS idx treeactive best (treeblocked ++ [(t0,gm)]) (add_seentrees treeseen t)). exists (hd 0 (measurelist ++ measureblocked ++ [n])). split.
    + eapply ptss_blocked; eauto.
    + eapply pikeinv; try (eapply add_inclusion; eauto); try constructor; eauto.
      2: { intros H. rewrite ADVANCE in H. inversion H. }
      2: { intros H. rewrite ADVANCE in H. inversion H. }
      intros nextinp H. specialize (BLOCKED nextinp H).
      apply ltt_app; eauto. specialize (TT2 nextinp H).
      eapply ltt_cons. constructor. auto.
Qed.
