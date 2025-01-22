(* The PikeVm algorithm, expressed as small-step semantics on the bytecode NFA *)

Require Import List Lia.
Import ListNotations.

Require Import Regex Chars Groups.
Require Import Tree Semantics NFA.
Require Import BooleanSemantics.

(** * PikeVM Semantics  *)
(* exponential for now because we're not tracking the seen set yet *)

Definition thread : Type := (label * group_map * LoopBool).

Definition upd_label (t:thread) (next:label): thread :=
  match t with (l,r,b) => (next,r,b) end.

Definition advance_thread (t:thread) : thread :=
  match t with (l,r,b) => (l+1,r,b) end.

Definition open_thread (t:thread) (gid:group_id) (idx:nat) : thread :=
  match t with (l,r,b) => (l+1, open_group r gid idx, b) end.

Definition close_thread (t:thread) (gid:group_id) (idx:nat) : thread :=
  match t with (l,r,b) => (l+1, close_group r gid idx, b) end.

Definition reset_thread (t:thread) (gidl:list group_id) : thread :=
  match t with (l,r,b) => (l+1, reset_groups r gidl, b) end.

Definition begin_thread (t:thread) : thread :=
  match t with (l,r,b) => (l+1,r,CannotExit) end.



Inductive VM_state : Type :=
| VMS (idx:nat) (input:input) (active: list thread) (best: option leaf) (blocked: list thread).

Inductive epsilon_result : Type :=
| EpsActive: list thread -> epsilon_result
| EpsMatch: epsilon_result
| EpsBlocked: thread -> epsilon_result.

Definition EpsDead : epsilon_result := EpsActive [].

Definition epsilon_step (t:thread) (c:code) (i:input) (idx:nat): epsilon_result :=
  match t with
  | (pc, gm, b) =>
      match get_pc c pc with
      | None => EpsDead
      | Some instr =>
          match instr with
          | Accept => EpsMatch
          | Consume cd => match check_read cd i with
                         | CannotRead => EpsDead
                         | CanRead => EpsBlocked (advance_thread t)
                         end
          | Jmp next => EpsActive [upd_label t next]
          | Fork l1 l2 => EpsActive [upd_label t l1; upd_label t l2]
          | SetRegOpen gid => EpsActive [open_thread t gid idx]
          | SetRegClose gid => EpsActive [close_thread t gid idx]
          | ResetRegs gidl => EpsActive [reset_thread t gidl]
          | BeginLoop => EpsActive [begin_thread t]
          | EndLoop next => match b with
                           | CannotExit => EpsDead
                           | CanExit => EpsActive [upd_label t next]
                           end
          end
      end
  end.


Inductive pike_vm_state : Type :=
| PVS (inp:input) (idx:nat) (active: list thread) (best: option leaf) (blocked: list thread)
| PVS_final (best: option leaf).

Definition pike_vm_initial_state (inp:input) : pike_vm_state :=
  PVS inp 0 [(0,empty_group_map,CanExit)] None [].

Definition gm_of (t:thread) : group_map :=
  match t with (pc,gm,b) => gm end.

Inductive pike_vm_step (c:code): pike_vm_state -> pike_vm_state -> Prop :=
| pvs_final:
(* moving to a final state when there are no more active or blocked threads *)
  forall inp idx best,
    pike_vm_step c (PVS inp idx [] best []) (PVS_final best)
| pvs_end:
  (* when the list of active is empty and we've reached the end of string *)
  forall inp idx best blocked
    (ADVANCE: advance_input inp = None),
    pike_vm_step c (PVS inp idx [] best blocked) (PVS_final best)
| pvs_nextchar:
  (* when the list of active threads is empty (but not blocked), restart from the blocked ones, proceeding to the next character *)
  forall inp1 inp2 idx best blocked thr
    (ADVANCE: advance_input inp1 = Some inp2),
    pike_vm_step c (PVS inp1 idx [] best (thr::blocked)) (PVS inp2 (idx+1) (thr::blocked) best [])
| pvs_active:
  (* generated new active threads: add them in front of the low-priority ones *)
  forall inp idx t active best blocked nextactive
    (STEP: epsilon_step t c inp idx = EpsActive nextactive),
    pike_vm_step c (PVS inp idx (t::active) best blocked) (PVS inp idx (nextactive++active) best blocked)
| pvs_match:
  (* a match is found, discard remaining low-priority active threads *)
  forall inp idx t active best blocked
    (STEP: epsilon_step t c inp idx = EpsMatch),
    pike_vm_step c (PVS inp idx (t::active) best blocked) (PVS inp idx [] (Some (gm_of t)) blocked)
| pvs_blocked:
  (* add the new blocked thread after the previous ones *)
  forall inp idx t active best blocked newt
    (STEP: epsilon_step t c inp idx = EpsBlocked newt),
    pike_vm_step c (PVS inp idx (t::active) best blocked) (PVS inp idx active best (blocked ++ [newt])).

(** * PikeVM properties  *)

Theorem pikevm_deterministic:
  forall c pvso pvs1 pvs2
    (STEP1: pike_vm_step c pvso pvs1)
    (STEP2: pike_vm_step c pvso pvs2),
    pvs1 = pvs2.
Proof.
  intros c pvso pvs1 pvs2 STEP1 STEP2. inversion STEP1; subst.
  - inversion STEP2; subst; auto. 
  - inversion STEP2; subst; auto. rewrite ADVANCE in ADVANCE0. inversion ADVANCE0.
  - inversion STEP2; subst; auto; rewrite ADVANCE in ADVANCE0; inversion ADVANCE0.
    subst. auto.
  - inversion STEP2; subst; auto; rewrite STEP in STEP0; inversion STEP0.
    subst. auto.
  - inversion STEP2; subst; auto; rewrite STEP in STEP0; inversion STEP0.
  - inversion STEP2; subst; auto; rewrite STEP in STEP0; inversion STEP0.
    subst. auto.
Qed.
