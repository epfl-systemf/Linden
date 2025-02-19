(* Relating the PikeVM smallstep semantics to the Pike Tree smallstep semantics *)

Require Import List Lia.
Import ListNotations.

Require Import Regex Chars Groups.
Require Import Tree Semantics BooleanSemantics.
Require Import NFA PikeTree PikeVM.
Require Import PikeTreeSeen PikeVMSeen.
Require Import PikeEquiv.

(** * Simulation Invariant  *)

Definition seen_inclusion (c:code) (inp:input) (treeseen:seentrees) (threadseen:seenpcs) : Prop :=
  forall pc b
    (SEEN: inseenpc threadseen pc b = true),
    (*(stutters pc c = true) \/*)
      exists t gm n,
        inseen treeseen t = true /\
          tree_thread c inp (t, gm) (pc, gm, b) n.
    

Inductive pike_inv (code:code): pike_tree_seen_state -> pike_vm_seen_state -> nat -> Prop :=
| pikeinv:
  forall inp idx treeactive treeblocked threadactive threadblocked best treeseen threadseen measureactive measureblocked n
    (ACTIVE: list_tree_thread code inp treeactive threadactive measureactive)
    (* blocked threads should be equivalent for the next input *)
    (* nothing to say if there is no next input *)
    (BLOCKED: forall nextinp, advance_input inp = Some nextinp -> list_tree_thread code nextinp treeblocked threadblocked measureblocked)
    (* these two properties are needed to ensure the two algorithms stop at he same time *)
    (ENDVM: advance_input inp = None -> threadblocked = [])
    (ENDTREE: advance_input inp = None -> treeblocked = [])
    (* any pc in threadseen must correspond to a tree in treeseen *)
    (SEEN: seen_inclusion code inp treeseen threadseen)
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
  forall c inp,
    seen_inclusion c inp initial_seentrees initial_seenpcs.
Proof.
  intros c inp. unfold seen_inclusion. intros pc b SEEN.
  rewrite initial_nothing_pc in SEEN. inversion SEEN.
Qed.

Lemma add_inclusion:
  forall treeseen threadseen c inp t pc gm b n
    (INCL: seen_inclusion c inp treeseen threadseen)
    (TT: tree_thread c inp (t,gm) (pc,gm,b) n),
    seen_inclusion c inp (add_seentrees treeseen t) (add_thread threadseen (pc, gm, b)).
Proof.
  intros treeseen threadseen c inp t pc gm b n INCL TT. unfold seen_inclusion in *.
  intros pc0 b0 SEEN. apply inpc_add in SEEN. destruct SEEN as [EQ|SEEN].
  - inversion EQ. subst. exists t. exists gm. exists n. split; auto. apply in_add. left. auto.
  - specialize (INCL pc0 b0 SEEN) as [ts [gms [ns [SEENs TTs]]]].
    exists ts. exists gms. exists ns. split; auto. apply in_add. right; auto.
Qed.


Lemma tt_det:
  forall code inp t1 gm1 t2 gm2 n1 n2 pc b,
    tree_thread code inp (t1,gm1) (pc,gm1,b) n1 ->
    tree_thread code inp (t2,gm2) (pc,gm2,b) n2 ->
    t1 = t2 /\ gm1 = gm2.
Proof.
Abort.

(** * Invariant Initialization  *)

(* the initial states of both smallstep semantics are related with the invariant *)
Lemma initial_pike_inv:
  forall r inp tree code
    (TREE: bool_tree r [] inp CanExit tree)
    (COMPILE: compilation r = code),
    pike_inv code (pike_tree_seen_initial_state tree) (pike_vm_seen_initial_state inp) 0.
Proof.
  intros r inp tree code TREE COMPILE.
  unfold compilation in COMPILE. destruct (compile r 0) as [c fresh] eqn:COMP.
  apply compile_nfa_rep with (prev := []) in COMP as REP; auto. simpl in REP.
  apply fresh_correct in COMP. simpl in COMP. subst.
  eapply pikeinv; auto.
  - econstructor.
    + constructor.
    + apply tt_eq with (pc_cont:=length c) (pc_end:=length c) (r:=r) (cont:=[]); auto.
      * apply nfa_rep_extend. auto.
      * constructor. replace (length c) with (length c + 0) by auto.
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
    apply SEEN in SKIP as [teq [gmeq [neq [SEENEQ TTEQ]]]].
    assert (teq = tree).
    { admit. }
    subst.
    exists (PTSS idx treeactive best treeblocked treeseen).
    exists (hd 0 (measurelist ++ measureblocked)).
    split.
    - apply ptss_skip; auto.
    - eapply pikeinv; eauto. }
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
    right. apply stutter_step with (idx:=idx) in TT as [nextpc [nextb [m [EPSSTEP [TT LESS]]]]]; subst; eauto.
    exists m. assert (pvs2 = (PVSS inp idx ([(nextpc, gm, nextb)] ++ threadactive) best threadblocked (add_thread threadseen (pc,gm,b)))).
    { eapply pikevm_deterministic; eauto. eapply pvss_active; eauto. }
    split; subst; simpl; auto. eapply pikeinv with (measureactive:=m::measurelist); simpl; eauto.
    - constructor; eauto.
    - unfold seen_inclusion. intros pc0 b0 SEEN0. rewrite inpc_add in SEEN0.
      destruct SEEN0 as [EQ|INSEEN].
      + admit.
      (* the equivalent tree to the pc being added in threadseen, has not yet been added to treeseen on the tree side *)
      + unfold seen_inclusion in SEEN. specialize (SEEN pc0 b0 INSEEN) as [teq [gmeq [neq [SEENEQ TTEQ]]]].
        exists teq. exists gmeq. exists neq. split; auto.
  }
  destruct (tree_bfs_step t gm idx) eqn:TREESTEP.
  (* active *)
  - left. eapply generate_active in TREESTEP as H; eauto. destruct H as [newthreads [measure [EPS LTT2]]].
    assert (pvs2 = PVSS inp idx (newthreads ++ threadactive) best threadblocked (add_thread threadseen (pc,gm,b))).
    { eapply pikevm_deterministic; eauto. constructor; auto. }
    subst. exists (PTSS idx (l ++ treeactive) best treeblocked (add_seentrees treeseen t)). exists (hd 0 ((measure ++ measurelist) ++ measureblocked)). split.
    + eapply ptss_active; eauto.
    + eapply pikeinv; try constructor; eauto.
      * apply ltt_app; eauto.
      * eapply add_inclusion; eauto.
  (* match *)
  - left. eapply generate_match in TREESTEP as THREADSTEP; eauto.
    assert (pvs2 = PVSS inp idx [] (Some (gm_of (pc,gm,b))) threadblocked (add_thread threadseen (pc,gm,b))).
    { eapply pikevm_deterministic; eauto. constructor; auto. }
    subst. exists (PTSS idx [] (Some gm) treeblocked (add_seentrees treeseen t)). exists (hd 0 ([] ++ measureblocked)). split.
    + constructor; auto.
    + eapply pikeinv; try constructor; eauto. eapply add_inclusion; eauto.
  (* blocked *)
  - left. specialize (generate_blocked _ _ _ _ _ _ _ _ _ TREESTEP STUTTERS TT) as [EPS2 [TT2 [nexti ADVANCE]]].
    assert (pvs2 = PVSS inp idx threadactive best (threadblocked ++ [(pc+1,gm,CanExit)]) (add_thread threadseen (pc,gm,b))).
    { eapply pikevm_deterministic; eauto. constructor; auto. }
    subst. exists (PTSS idx treeactive best (treeblocked ++ [(t0,gm)]) (add_seentrees treeseen t)). exists (hd 0 (measurelist ++ measureblocked ++ [n])). split.
    + eapply ptss_blocked; eauto.
    + eapply pikeinv; try constructor; eauto.
      2: { intros H. rewrite ADVANCE in H. inversion H. }
      2: { intros H. rewrite ADVANCE in H. inversion H. }
      * intros nextinp H. specialize (BLOCKED nextinp H).
        apply ltt_app; eauto. specialize (TT2 nextinp H).
        eapply ltt_cons. constructor. auto.
      * eapply add_inclusion; eauto.
Admitted.
