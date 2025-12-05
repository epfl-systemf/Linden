(** * PikeVM Algorithm  *)

(* The PikeVM algorithm, expressed as small-step semantics on the bytecode NFA *)
(* It records the code labels it has already handled to avoid doing work twice *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import Parameters SeenSets Prefix.
From Warblre Require Import Base RegExpRecord.


Section PikeVM.
  Context {params: LindenParameters}.
  Context {VMS: VMSeen}.
  Context (rer: RegExpRecord).

(** * PikeVM threads  *)

Definition thread : Type := (label * group_map * LoopBool).

Definition upd_label (t:thread) (next:label): thread :=
  match t with (l,r,b) => (next,r,b) end.

Definition advance_thread (t:thread) : thread :=
  match t with (l,r,b) => (l+1,r,b) end.

(* used after consuming *)
Definition block_thread (t:thread) : thread :=
  match t with (l,r,b) => (l+1,r,CanExit) end.

Definition open_thread (t:thread) (gid:group_id) (idx:nat) : thread :=
  match t with (l,r,b) => (l+1, GroupMap.open idx gid r, b) end.

Definition close_thread (t:thread) (gid:group_id) (idx:nat) : thread :=
  match t with (l,r,b) => (l+1, GroupMap.close idx gid r, b) end.

Definition reset_thread (t:thread) (gidl:list group_id) : thread :=
  match t with (l,r,b) => (l+1, GroupMap.reset gidl r, b) end.

Definition begin_thread (t:thread) : thread :=
  match t with (l,r,b) => (l+1,r,CannotExit) end.

Definition gm_of (t:thread) : group_map :=
  match t with (pc,gm,b) => gm end.

Definition seen_thread (seen:seenpcs) (t:thread) :bool :=
  match t with
  | (pc, gm, b) => inseenpc seen pc b
  end.

Definition add_thread (seen:seenpcs) (t:thread) : seenpcs :=
  match t with
  | (pc, gm, b) => add_seenpcs seen pc b
  end.


(** * NFA epsilon-exploration  *)

(* the result of one step of exploring transitions *)
Inductive epsilon_result : Type :=
| EpsActive: list thread -> epsilon_result
| EpsMatch: epsilon_result
| EpsBlocked: thread -> epsilon_result.

Definition EpsDead : epsilon_result := EpsActive [].

(* an atomic step for a thread *)
Definition epsilon_step (t:thread) (c:code) (i:input): epsilon_result :=
  match t with
  | (pc, gm, b) =>
      match get_pc c pc with
      | None => EpsDead
      | Some instr =>
          match instr with
          | Accept => EpsMatch
          | Consume cd => match check_read rer cd i forward with
                         | CannotRead => EpsDead
                         | CanRead => EpsBlocked (block_thread t)
                         end
          | CheckAnchor a => match anchor_satisfied rer a i with
                            | false => EpsDead
                            | true => EpsActive [advance_thread t]
                            end
          | Jmp next => EpsActive [upd_label t next]
          | Fork l1 l2 => EpsActive [upd_label t l1; upd_label t l2]
          | SetRegOpen gid => EpsActive [open_thread t gid (idx i)]
          | SetRegClose gid => EpsActive [close_thread t gid (idx i)]
          | ResetRegs gidl => EpsActive [reset_thread t gidl]
          | BeginLoop => EpsActive [begin_thread t]
          | EndLoop next => match b with
                           | CannotExit => EpsDead
                           | CanExit => EpsActive [upd_label t next]
                           end
          | KillThread => EpsDead
          end
      end
  end.


(** * PikeVM Semantics  *)

(* semantic states of the PikeVM algorithm *)
Inductive pike_vm_state : Type :=
| PVS (inp:input) (active: list thread) (best: option leaf) (blocked: list thread) (nextprefix: option (nat * literal)) (seen: seenpcs)
| PVS_final (best: option leaf).

Definition next_prefix_counter {strs:StrSearch} (inp: input) (lit: literal) : option (nat * literal) :=
  match advance_input inp forward with
  | None => None
  | Some (Input next pref) =>
      match str_search (prefix lit) next with
      | None => None
      | Some n => Some (n, lit)
      end
  end.

Definition pike_vm_initial_thread : thread := (0, GroupMap.empty, CanExit).
Definition pike_vm_initial_state_lazyprefix {strs:StrSearch} (lit:literal) (inp:input) : pike_vm_state :=
  let nextprefix := next_prefix_counter inp lit in
  PVS inp [pike_vm_initial_thread] None [] nextprefix initial_seenpcs.
Definition pike_vm_initial_state (inp:input) : pike_vm_state :=
  PVS inp [pike_vm_initial_thread] None [] None initial_seenpcs.


(* small-step semantics for the PikeVM algorithm *)
Inductive pike_vm_step {strs:StrSearch} (c:code): pike_vm_state -> pike_vm_state -> Prop :=
| pvs_final:
(* moving to a final state when there are no more active or blocked threads *)
  forall inp best seen,
    pike_vm_step c (PVS inp [] best [] None seen) (PVS_final best)
| pvs_acc:
(* if there are no more active or blocked threads and we know where the next prefix matches, *)
(* we accelerate to that point *)
  forall inp best n lit nextinp seen
    (ADVANCE: advance_input_n inp (S n) forward = nextinp),
    pike_vm_step c (PVS inp [] best [] (Some (n, lit)) seen) (PVS nextinp [pike_vm_initial_thread] best [] (next_prefix_counter nextinp lit) initial_seenpcs)
| pvs_end:
  (* when the list of active is empty and we've reached the end of string *)
  forall inp best thr blocked nextprefix seen
    (ADVANCE: advance_input inp forward = None),
    pike_vm_step c (PVS inp [] best (thr::blocked) nextprefix seen) (PVS_final best)
| pvs_nextchar:
  (* when the list of active threads is empty (but not blocked), restart from the blocked ones, proceeding to the next character *)
  (* reset the set of seen pcs *)
  forall inp1 inp2 best thr blocked seen
    (ADVANCE: advance_input inp1 forward = Some inp2),
    pike_vm_step c (PVS inp1 [] best (thr::blocked) None seen) (PVS inp2 (thr::blocked) best [] None initial_seenpcs)
| pvs_nextchar_generate:
  forall inp1 inp2 best lit thr blocked seen
    (ADVANCE: advance_input inp1 forward = Some inp2),
    pike_vm_step c (PVS inp1 [] best (thr::blocked) (Some (0, lit)) seen) (PVS inp2 ((thr::blocked) ++ [pike_vm_initial_thread]) best [] (next_prefix_counter inp2 lit) initial_seenpcs)
| pvs_nextchar_filter:
  forall inp1 inp2 best n lit thr blocked seen
    (ADVANCE: advance_input inp1 forward = Some inp2),
    pike_vm_step c (PVS inp1 [] best (thr::blocked) (Some (S n, lit)) seen) (PVS inp2 (thr::blocked) best [] (Some (n, lit)) initial_seenpcs)
| pvs_skip:
  (* when the pc has already been seen at this current index, we skip it entirely *)
  forall inp t active best blocked nextprefix seen
    (SEEN: seen_thread seen t = true),
    pike_vm_step c (PVS inp (t::active) best blocked nextprefix seen) (PVS inp active best blocked nextprefix seen)
| pvs_active:
  (* generated new active threads: add them in front of the low-priority ones *)
  forall inp t active best blocked nextprefix seen nextactive
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c inp = EpsActive nextactive),
    pike_vm_step c (PVS inp (t::active) best blocked nextprefix seen) (PVS inp (nextactive++active) best blocked nextprefix (add_thread seen t))
| pvs_match:
  (* a match is found, discard remaining low-priority active threads *)
  forall inp t active best blocked nextprefix seen
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c inp = EpsMatch),
    pike_vm_step c (PVS inp (t::active) best blocked nextprefix seen) (PVS inp [] (Some (inp,gm_of t)) blocked None (add_thread seen t))
| pvs_blocked:
  (* add the new blocked thread after the previous ones *)
  forall inp t active best blocked nextprefix seen newt
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c inp = EpsBlocked newt),
    pike_vm_step c (PVS inp (t::active) best blocked nextprefix seen) (PVS inp active best (blocked ++ [newt]) nextprefix (add_thread seen t)).

(** * PikeVM properties  *)

Theorem pikevm_deterministic {strs:StrSearch}:
  forall c pvso pvs1 pvs2
    (STEP1: pike_vm_step c pvso pvs1)
    (STEP2: pike_vm_step c pvso pvs2),
    pvs1 = pvs2.
Proof.
  intros c pvso pvs1 pvs2 STEP1 STEP2. inversion STEP1; subst.
  - inversion STEP2; subst; auto.
  - inversion STEP2; subst; auto.
  - inversion STEP2; subst; auto; rewrite ADVANCE in ADVANCE0; inversion ADVANCE0.
  - inversion STEP2; subst; auto; rewrite ADVANCE in ADVANCE0; inversion ADVANCE0.
    subst. auto.
  - inversion STEP2; subst; auto; rewrite ADVANCE in ADVANCE0; inversion ADVANCE0; auto.
  - inversion STEP2; subst; auto; rewrite ADVANCE in ADVANCE0; inversion ADVANCE0; auto.
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

Theorem pikevm_progress {strs:StrSearch}:
  forall c inp active best blocked nextprefix seen,
  exists pvs_next,
    pike_vm_step c (PVS inp active best blocked nextprefix seen) pvs_next.
Proof.
  intros c inp active best blocked nextprefix seen.
  destruct active as [|[[pc gm] b] active].
  - destruct blocked as [|t blocked].
    + destruct nextprefix.
      * destruct p. eexists. now apply pvs_acc.
      * eexists. apply pvs_final.
    + destruct (advance_input inp forward) eqn:INP.
      * destruct nextprefix.
        -- destruct p as [n lit], n.
          ++ eexists. apply pvs_nextchar_generate. eauto.
          ++ eexists. apply pvs_nextchar_filter. eauto.
        -- eexists. apply pvs_nextchar. eauto.
      * eexists. apply pvs_end. eauto.
  - destruct (seen_thread seen (pc,gm,b)) eqn:SEEN.
    { eexists. apply pvs_skip. auto. }
    destruct (epsilon_step (pc,gm,b) c inp) eqn:EPS.
    + eexists. apply pvs_active; eauto.
    + eexists. apply pvs_match; eauto.
    + eexists. apply pvs_blocked; eauto.
Qed.

End PikeVM.
