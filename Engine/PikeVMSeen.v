(* The PikeVm algorithm, expressed as small-step semantics on the bytecode NFA *)
(* This version records the code labels it has already handled to avoid doing work twice *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import PikeVM.
From Warblre Require Import Base.

(** * Sets of seen pcs *)

(* remembering pairs of (pc, loopbool) that has been handled at the current input *)
Parameter seenpcs: Type.
Parameter initial_seenpcs: seenpcs.
Parameter add_seenpcs: seenpcs -> label -> LoopBool -> seenpcs.
Parameter inseenpc : seenpcs -> label -> LoopBool -> bool.

Axiom inpc_add:
  forall seen pc1 b1 pc2 b2,
    inseenpc (add_seenpcs seen pc2 b2) pc1 b1 = true <->
    ((pc1,b1) = (pc2,b2)) \/ inseenpc seen pc1 b1 = true.

Axiom initial_nothing_pc:
  forall pc b, inseenpc initial_seenpcs pc b = false.

Definition seen_thread (seen:seenpcs) (t:thread) :bool :=
  match t with
  | (pc, gm, b) => inseenpc seen pc b
  end.

Definition add_thread (seen:seenpcs) (t:thread) : seenpcs :=
  match t with
  | (pc, gm, b) => add_seenpcs seen pc b
  end.

(** * PikeVM Semantics  *)

(* semantic states of the PikeVM algorithm *)
Inductive pike_vm_seen_state : Type :=
| PVSS (inp:input) (active: list thread) (best: option leaf) (blocked: list thread) (seen: seenpcs)
| PVSS_final (best: option leaf).

Definition pike_vm_seen_initial_state (inp:input) : pike_vm_seen_state :=
  PVSS inp [(0,GroupMap.empty,CanExit)] None [] initial_seenpcs.

(* small-tep semantics for the PikeVM algorithm *)
Inductive pike_vm_seen_step (c:code): pike_vm_seen_state -> pike_vm_seen_state -> Prop :=
| pvss_final:
(* moving to a final state when there are no more active or blocked threads *)
  forall inp best seen,
    pike_vm_seen_step c (PVSS inp [] best [] seen) (PVSS_final best)
| pvss_end:
  (* when the list of active is empty and we've reached the end of string *)
  forall inp best blocked seen
    (ADVANCE: advance_input inp forward = None),
    pike_vm_seen_step c (PVSS inp [] best blocked seen) (PVSS_final best)
| pvss_nextchar:
  (* when the list of active threads is empty (but not blocked), restart from the blocked ones, proceeding to the next character *)
  (* reset the set of seen pcs *)
  forall inp1 inp2 best blocked seen thr
    (ADVANCE: advance_input inp1 forward = Some inp2),
    pike_vm_seen_step c (PVSS inp1 [] best (thr::blocked) seen) (PVSS inp2 (thr::blocked) best [] initial_seenpcs)
| pvss_skip:
  (* when the pc has already been seen at this current index, we skip it entirely *)
  forall inp t active best blocked seen
    (SEEN: seen_thread seen t = true),
    pike_vm_seen_step c (PVSS inp (t::active) best blocked seen) (PVSS inp active best blocked seen)
| pvss_active:
  (* generated new active threads: add them in front of the low-priority ones *)
  forall inp t active best blocked seen nextactive
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c inp = EpsActive nextactive),
    pike_vm_seen_step c (PVSS inp (t::active) best blocked seen) (PVSS inp (nextactive++active) best blocked (add_thread seen t))
| pvss_match:
  (* a match is found, discard remaining low-priority active threads *)
  forall inp t active best blocked seen
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c inp = EpsMatch),
    pike_vm_seen_step c (PVSS inp (t::active) best blocked seen) (PVSS inp [] (Some (inp,gm_of t)) blocked (add_thread seen t))
| pvss_blocked:
  (* add the new blocked thread after the previous ones *)
  forall inp t active best blocked seen newt
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c inp = EpsBlocked newt),
    pike_vm_seen_step c (PVSS inp (t::active) best blocked seen) (PVSS inp active best (blocked ++ [newt]) (add_thread seen t)).

(** * PikeVM properties  *)

Theorem pikevm_deterministic:
  forall c pvso pvs1 pvs2
    (STEP1: pike_vm_seen_step c pvso pvs1)
    (STEP2: pike_vm_seen_step c pvso pvs2),
    pvs1 = pvs2.
Proof.
  intros c pvso pvs1 pvs2 STEP1 STEP2. inversion STEP1; subst.
  - inversion STEP2; subst; auto. 
  - inversion STEP2; subst; auto. rewrite ADVANCE in ADVANCE0; inversion ADVANCE0.
  - inversion STEP2; subst; auto; rewrite ADVANCE in ADVANCE0; inversion ADVANCE0.
    subst. auto.
  - inversion STEP2; subst; auto; rewrite UNSEEN in SEEN; inversion SEEN.
  - inversion STEP2; subst; auto; try (rewrite UNSEEN in SEEN; inversion SEEN);
      rewrite STEP in STEP0; inversion STEP0.
    subst. auto.
  - inversion STEP2; subst; auto; try (rewrite UNSEEN in SEEN; inversion SEEN);
      rewrite STEP in STEP0; inversion STEP0.
  - inversion STEP2; subst; auto; try (rewrite UNSEEN in SEEN; inversion SEEN);
      rewrite STEP in STEP0; inversion STEP0.
    subst. auto.
Qed.

Theorem pikevm_progress:
  forall c inp active best blocked seen,
  exists pvs_next,
    pike_vm_seen_step c (PVSS inp active best blocked seen) pvs_next.
Proof.
  intros c inp active best blocked seen.
  destruct active as [|[[pc gm] b] active].
  - destruct blocked as [|t blocked].
    + eexists. econstructor.
    + destruct (advance_input inp forward) eqn:INP.
      * eexists. apply pvss_nextchar. eauto.
      * eexists. apply pvss_end. eauto.
  - destruct (seen_thread seen (pc,gm,b)) eqn:SEEN.
    { eexists. apply pvss_skip. auto. }
    destruct (epsilon_step (pc,gm,b) c inp) eqn:EPS.
    + eexists. apply pvss_active; eauto.
    + eexists. apply pvss_match; eauto.
    + eexists. apply pvss_blocked; eauto.
Qed.
    
