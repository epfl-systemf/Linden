(* The PikeVm algorithm, expressed as small-step semantics on the bytecode NFA *)
(* This version records the code labels it has already handled to avoid doing work twice *)

Require Import List Lia.
Import ListNotations.

Require Import Regex Chars Groups.
Require Import Tree Semantics NFA.
Require Import BooleanSemantics.
Require Import PikeVM.

(** * Sets of seen pcs *)

Parameter seenpcs: Type.
Parameter initial_seenpcs: seenpcs.
Parameter add_seenpcs: seenpcs -> label -> seenpcs.
Parameter inseenpc : seenpcs -> label -> bool.

Axiom inpc_add:
  forall seen pc1 pc2,
    inseenpc (add_seenpcs seen pc2) pc1 = true <->
    pc1 = pc2 \/ inseenpc seen pc1 = true.

Axiom initial_nothing_pc:
  forall pc, inseenpc initial_seenpcs pc = false.

Definition seen_thread (seen:seenpcs) (t:thread) :bool :=
  match t with
  | (pc, gm, b) => inseenpc seen pc
  end.

Definition add_thread (seen:seenpcs) (t:thread) : seenpcs :=
  match t with
  | (pc, gm, b) => add_seenpcs seen pc
  end.

(** * PikeVM Semantics  *)

(* semantic states of the PikeVM algorithm *)
Inductive pike_vm_seen_state : Type :=
| PVSS (inp:input) (idx:nat) (active: list thread) (best: option leaf) (blocked: list thread) (seen: seenpcs)
| PVSS_final (best: option leaf).

Definition pike_vm_seen_initial_state (inp:input) : pike_vm_seen_state :=
  PVSS inp 0 [(0,empty_group_map,CanExit)] None [] initial_seenpcs.

(* small-tep semantics for the PikeVM algorithm *)
Inductive pike_vm_seen_step (c:code): pike_vm_seen_state -> pike_vm_seen_state -> Prop :=
| pvss_final:
(* moving to a final state when there are no more active or blocked threads *)
  forall inp idx best seen,
    pike_vm_seen_step c (PVSS inp idx [] best [] seen) (PVSS_final best)
| pvss_end:
  (* when the list of active is empty and we've reached the end of string *)
  forall inp idx best blocked seen
    (ADVANCE: advance_input inp = None),
    pike_vm_seen_step c (PVSS inp idx [] best blocked seen) (PVSS_final best)
| pvss_nextchar:
  (* when the list of active threads is empty (but not blocked), restart from the blocked ones, proceeding to the next character *)
  (* reset the set of seen pcs *)
  forall inp1 inp2 idx best blocked seen thr
    (ADVANCE: advance_input inp1 = Some inp2),
    pike_vm_seen_step c (PVSS inp1 idx [] best (thr::blocked) seen) (PVSS inp2 (idx+1) (thr::blocked) best [] initial_seenpcs)
| pvss_skip:
  (* when the pc has already been seen at this current index, we skip it entirely *)
  forall inp idx t active best blocked seen
    (SEEN: seen_thread seen t = true),
    pike_vm_seen_step c (PVSS inp idx (t::active) best blocked seen) (PVSS inp idx active best blocked seen)
| pvss_active:
  (* generated new active threads: add them in front of the low-priority ones *)
  forall inp idx t active best blocked seen nextactive
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c inp idx = EpsActive nextactive),
    pike_vm_seen_step c (PVSS inp idx (t::active) best blocked seen) (PVSS inp idx (nextactive++active) best blocked (add_thread seen t))
| pvss_match:
  (* a match is found, discard remaining low-priority active threads *)
  forall inp idx t active best blocked seen
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c inp idx = EpsMatch),
    pike_vm_seen_step c (PVSS inp idx (t::active) best blocked seen) (PVSS inp idx [] (Some (gm_of t)) blocked (add_thread seen t))
| pvss_blocked:
  (* add the new blocked thread after the previous ones *)
  forall inp idx t active best blocked seen newt
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c inp idx = EpsBlocked newt),
    pike_vm_seen_step c (PVSS inp idx (t::active) best blocked seen) (PVSS inp idx active best (blocked ++ [newt]) (add_thread seen t)).

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
