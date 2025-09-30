(** * PikeVM Algorithm  *)

(* The PikeVM algorithm, expressed as small-step semantics on the bytecode NFA *)
(* It records the code labels it has already handled to avoid doing work twice *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Warblre Require Import Base RegExpRecord.

(** * Sets of seen pcs *)

Module Type VMSeen.
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

End VMSeen.

(* one instantiation using lists, but you could use anything else *)
Module VMS <: VMSeen.
  Definition seenpcs: Type := list (label * LoopBool).
  Definition initial_seenpcs : seenpcs := [].
  Definition add_seenpcs (s:seenpcs) (l:label) (b:LoopBool) := (l,b)::s.

  Definition lblbool_eq_dec : forall (l1 l2 : (label*LoopBool)), { l1 = l2 } + { l1 <> l2 }.
  Proof. repeat decide equality. Qed.
  
  Definition lblbool_eqb l1 l2 : bool :=
    match lblbool_eq_dec l1 l2 with | left _ => true | _ => false end.
  Definition inseenpc (s:seenpcs) (l:label) (b:LoopBool) : bool :=
    List.existsb (fun x => lblbool_eqb x (l,b)) s.

  Theorem inpc_add:
    forall seen pc1 b1 pc2 b2,
      inseenpc (add_seenpcs seen pc2 b2) pc1 b1 = true <->
        ((pc1,b1) = (pc2,b2)) \/ inseenpc seen pc1 b1 = true.
  Proof.
    intros seen pc1 b1 pc2 b2. simpl. unfold lblbool_eqb. destruct (lblbool_eq_dec (pc2,b2) (pc1,b1)) as [H1|H2];
      subst; split; intros; auto.
    destruct H as [Heq|Hin]; auto.
  Qed.

  Theorem initial_nothing_pc:
    forall pc b, inseenpc initial_seenpcs pc b = false.
  Proof. auto. Qed.

End VMS.


Section PikeVM.
  Context (rer: RegExpRecord).

(** * Seen set instantiation  *)
Definition seenpcs := VMS.seenpcs.
Definition initial_seenpcs := VMS.initial_seenpcs.
Definition add_seenpcs := VMS.add_seenpcs.
Definition inseenpc := VMS.inseenpc. 
Definition inpc_add := VMS.inpc_add.
Definition initial_nothing_pc := VMS.initial_nothing_pc.
(* Global Opaque seenpcs initial_seenpcs add_seenpcs inseenpc inpc_add initial_nothing_pc. *)

  
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
| PVS (inp:input) (active: list thread) (best: option leaf) (blocked: list thread) (seen: seenpcs)
| PVS_final (best: option leaf).

Definition pike_vm_initial_state (inp:input) : pike_vm_state :=
  PVS inp [(0,GroupMap.empty,CanExit)] None [] initial_seenpcs.

(* small-step semantics for the PikeVM algorithm *)
Inductive pike_vm_step (c:code): pike_vm_state -> pike_vm_state -> Prop :=
| pvs_final:
(* moving to a final state when there are no more active or blocked threads *)
  forall inp best seen,
    pike_vm_step c (PVS inp [] best [] seen) (PVS_final best)
| pvs_end:
  (* when the list of active is empty and we've reached the end of string *)
  forall inp best blocked seen
    (ADVANCE: advance_input inp forward = None),
    pike_vm_step c (PVS inp [] best blocked seen) (PVS_final best)
| pvs_nextchar:
  (* when the list of active threads is empty (but not blocked), restart from the blocked ones, proceeding to the next character *)
  (* reset the set of seen pcs *)
  forall inp1 inp2 best blocked seen thr
    (ADVANCE: advance_input inp1 forward = Some inp2),
    pike_vm_step c (PVS inp1 [] best (thr::blocked) seen) (PVS inp2 (thr::blocked) best [] initial_seenpcs)
| pvs_skip:
  (* when the pc has already been seen at this current index, we skip it entirely *)
  forall inp t active best blocked seen
    (SEEN: seen_thread seen t = true),
    pike_vm_step c (PVS inp (t::active) best blocked seen) (PVS inp active best blocked seen)
| pvs_active:
  (* generated new active threads: add them in front of the low-priority ones *)
  forall inp t active best blocked seen nextactive
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c inp = EpsActive nextactive),
    pike_vm_step c (PVS inp (t::active) best blocked seen) (PVS inp (nextactive++active) best blocked (add_thread seen t))
| pvs_match:
  (* a match is found, discard remaining low-priority active threads *)
  forall inp t active best blocked seen
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c inp = EpsMatch),
    pike_vm_step c (PVS inp (t::active) best blocked seen) (PVS inp [] (Some (inp,gm_of t)) blocked (add_thread seen t))
| pvs_blocked:
  (* add the new blocked thread after the previous ones *)
  forall inp t active best blocked seen newt
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c inp = EpsBlocked newt),
    pike_vm_step c (PVS inp (t::active) best blocked seen) (PVS inp active best (blocked ++ [newt]) (add_thread seen t)).

(** * PikeVM properties  *)

Theorem pikevm_deterministic:
  forall c pvso pvs1 pvs2
    (STEP1: pike_vm_step c pvso pvs1)
    (STEP2: pike_vm_step c pvso pvs2),
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
    pike_vm_step c (PVS inp active best blocked seen) pvs_next.
Proof.
  intros c inp active best blocked seen.
  destruct active as [|[[pc gm] b] active].
  - destruct blocked as [|t blocked].
    + eexists. econstructor.
    + destruct (advance_input inp forward) eqn:INP.
      * eexists. apply pvs_nextchar. eauto.
      * eexists. apply pvs_end. eauto.
  - destruct (seen_thread seen (pc,gm,b)) eqn:SEEN.
    { eexists. apply pvs_skip. auto. }
    destruct (epsilon_step (pc,gm,b) c inp) eqn:EPS.
    + eexists. apply pvs_active; eauto.
    + eexists. apply pvs_match; eauto.
    + eexists. apply pvs_blocked; eauto.
Qed.

End PikeVM.
    
