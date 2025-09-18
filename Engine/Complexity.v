(** * Complexity of the PikeVM algorithm *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeTree PikeVM PikeSubset.
From Linden Require Import PikeTreeSeen PikeVMSeen.
From Linden Require Import Correctness PikeSeenEquiv.
From Warblre Require Import Base RegExpRecord.

(* We prove that there is a natural measure that strictly decreases at each step. *)
(* This provides an upper bound on the number of steps needed to reach a final state. *)
(* This upper bound can be expressed in terms of the size of the regex and the size of the input string. *)

Context (rer: RegExpRecord).

(** * Free slots  *)
(* To define the measure, we need a notion of free slots: how many more states can the PikeVM visit *)

(* well-formedness of a seen set: it was obtained by applying add to the initial seen set *)
(* each element that was added is smaller than some `size` constant (size of the bytecode) *)
(* and `count` is the number of distinct elements  *)
Inductive wf: seenpcs -> nat -> nat -> Prop :=
| wf_init:
  forall size, wf initial_seenpcs size 0
| wf_new:
  forall seen size pc b count
    (RANGE: pc < size)
    (NEW: inseenpc seen pc b = false)
    (WF: wf seen size count),
    wf (add_seenpcs seen pc b) size (S count)
| wf_seen:
  forall seen size pc b count
    (RANGE: pc < size)
    (SEEN: inseenpc seen pc b = true)
    (WF: wf seen size count),
    wf (add_seenpcs seen pc b) size count.


Theorem wf_size:
  forall seen size count,
    wf seen size count -> count <= 2 * size.
Proof.
Admitted.

(* the number of free slots in a seen set *)
(* the total number of slots is 2 times the size of the code: each label can be added with 2 possible LoopBool values *)
(* we remove the number of distinct entries in the seen set *)
Definition free (codesize:nat) (count:nat) : nat :=
  (2 * codesize) - count.

Lemma free_initial:
  forall codesize, free codesize 0 = 2 * codesize.
Proof.
  intros codesize. unfold free. lia.
Qed.

Lemma free_add:
  forall seen size count t,
    wf seen size count ->
    seen_thread seen t = false ->
    fst (fst t) < size ->
    wf (add_thread seen t) size (S count).
Proof.
  intros seen size count [[pc gm] b] WF SEEN SIZE. unfold seen_thread in SEEN.
  constructor; auto.
Qed.

(** * Well Formedness Invariant and Measure of PikeVM states *)

(* we add 1 because we consider that even at the last position, there is work to do to reach the final state *)
Definition inpsize (i:input) : nat :=
  match i with
  | Input next pref => 1 + length next
  end.

Lemma inpsize_strict:
  forall i, inpsize i > 0.
Proof.
  intros [next pref]. simpl. lia.
Qed.

Definition size (c:code) : nat := length c.

(* The number of free slots decreases at most steps *)
(* In some cases (a fork), a new thread is created but the number of free slots decreases: this is why free slots are multiplied by 2 *)
(* As we change characters, the seen set might get 2*codesize new free slots (multiplied by 2 for the measure) *)
(* But the input decreases, which makes the measure also decrease, because input size is multiplied by (1 + 4*codesize)  *)
Definition measure (codesize:nat) (count:nat) (active blocked:list thread) (inp:input) :=
  (2 * free codesize count) + length active + length blocked + (inpsize inp * (1 + 4 * codesize)).

(* The invariant that is preserved through pikeVM execution, with a measure that strictly decreases *)
Inductive vm_inv (c:code): pike_vm_seen_state -> nat -> Prop :=
| inv_final:
  forall b, vm_inv c (PVSS_final b) 0
| inv_pvss:
  forall inp active best blocked seen count
    (* the threads in active and blocked have their pc inside the code range *)
    (ACTIVEWF: forall t, In t active -> fst (fst t) < size c)
    (BLOCKEDWF: forall t, In t blocked -> fst (fst t) < size c)
    (* the seen set is well-formed, and has `count` distinct elements *)
    (SEENWF: wf seen (size c) count),
    vm_inv c (PVSS inp active best blocked seen) (measure (size c) count active blocked inp).

Lemma nonfinal_pos:
  forall c inp active best blocked seen m,
    vm_inv c (PVSS inp active best blocked seen) m -> 0 < m.
Proof.
  intros c inp active best blocked seen m H. inversion H. subst. unfold measure.
  specialize (inpsize_strict inp) as SIZE. lia.
Qed.

(** * Well-formedness of the code  *)

(* Some bytecode is well-formed if every target label belongs in some range *)
Definition code_wf (c:code) (size:nat) :=
  forall pc i next,
    get_pc c pc = Some i ->
    In next (next_pcs pc i) ->
    next < size.

Theorem compiled_wf:
  forall r, code_wf (compilation r) (size (compilation r)).
Proof.
Admitted.

Lemma eps_step_blocked_wf:
  forall t code inp newt,
    epsilon_step rer t code inp = EpsBlocked newt ->
    exists i, get_pc code (fst (fst t)) = Some i /\
           In (fst (fst newt)) (next_pcs (fst (fst t)) i).
Proof.
  unfold epsilon_step. intros [[pc gm]b] code inp newt H.
  destruct (get_pc code pc) eqn:GET; [|inversion H].
  destruct b0; inversion H; subst.
  - destruct (check_read rer c inp forward); inversion H1; subst.
    simpl; eexists; split; eauto; simpl; auto; lia.
  - destruct b; inversion H1.
Qed.

Lemma eps_step_active_wf:
  forall t code inp next newt,
    epsilon_step rer t code inp = EpsActive next ->
    In newt next ->
    exists i, get_pc code (fst (fst t)) = Some i /\
           In (fst (fst newt)) (next_pcs (fst (fst t)) i).
Proof.
  unfold epsilon_step. intros [[pc gm] b] code inp next newt H IN.
  destruct (get_pc code pc) eqn:GET.
  2: { inversion H. subst. inversion IN. }
  destruct b0; inversion H; subst;
    try solve[inversion IN; subst; try solve [inversion H0];
              simpl; eexists; split; eauto; simpl; auto; lia].
  - destruct (check_read rer c inp forward); inversion H1; subst;
      inversion IN; subst; try solve [inversion H0];
      simpl; eexists; split; eauto; simpl; auto; lia.
  - inversion IN; [|inversion H0]; subst; try solve [inversion H1];
      simpl; eexists; split; eauto; simpl; auto.
  - destruct b; subst; inversion H1; subst;
      inversion IN; subst; try solve [inversion H0];
      simpl; eexists; split; eauto; simpl; auto; lia.
Qed.


(** * PikeVM measure decreases *)

(* epsilon_step cannot generate too many new threads *)
Lemma eps_step_active:
  forall t code inp next,
    epsilon_step rer t code inp = EpsActive next ->
    length next <= 2.
Proof.
  unfold epsilon_step. intros [[pc gm] b] code inp next H.
  destruct (get_pc code pc) eqn:GET.
  2: { inversion H. simpl. lia. }
  destruct b0; try solve [inversion H; simpl; lia].
  - destruct (check_read rer c inp forward); try solve [inversion H; simpl; lia].
  - destruct b; try solve [inversion H; simpl; lia].
Qed.

Lemma advance_input_decreases:
  forall i1 i2,
    advance_input i1 forward = Some i2 ->
    inpsize i2 < inpsize i1.
Proof.
  intros [n1 p1] [n2 p2] H. simpl in H. destruct n1 as [|h1 n1]; inversion H; subst. simpl. lia.
Qed.

Theorem increase_mult:
  forall a b x,
    a < b ->
    x + a * (S x) < b * (S x).
Proof.
  intros a b c H. repeat rewrite PeanoNat.Nat.mul_succ_r.
  induction c; try lia.
Qed.


(* at each step, the measure strictly decreases *)
(* the well-formedness of the seen set is preserved *)
Theorem pikevm_decreases:
  forall code pvs1 pvs2 m1,
    code_wf code (size code) ->
    pike_vm_seen_step rer code pvs1 pvs2 ->
    vm_inv code pvs1 m1 ->
    exists m2, vm_inv code pvs2 m2 /\ m2 < m1.
Proof.
  intros code pvs1 pvs2 m1 CODEWF STEP INV. inversion STEP; subst; simpl measure; inversion INV; subst.
  (* when reaching a final state, we end up with a measure of 0, while the previous measure was strictly positive *)
  - exists 0. split.
    + constructor.
    + apply nonfinal_pos in INV. auto.
  - exists 0. split.
    + constructor.
    + apply nonfinal_pos in INV. auto.
  (* nextchar: we might add (2*codesize) free slots, but we lose an input length *)
  - exists (measure (size code) 0 (thr::blocked) [] inp2). split; [constructor|]; auto.
    + constructor.
    + unfold measure. simpl. rewrite free_initial. apply advance_input_decreases in ADVANCE.
      apply increase_mult with (x:= 4 * size code) in ADVANCE as NEXT. simpl in NEXT. lia.
  (* skip: we lose a thread *)
  - exists (measure (size code) count active blocked inp). split; [constructor|]; auto.
    + intros t0 H. apply ACTIVEWF. simpl. right. auto.
    + unfold measure. simpl. lia.
  (* active: we may add a new thread, but lose a free slot *)
  - assert (RANGE: fst (fst t) < size code).
    { apply ACTIVEWF. left. auto. }
    exists (measure (size code) (S count) (nextactive++active) blocked inp). split; [constructor|]; auto.
    + intros t0 H. apply in_app_or in H as [H|H].
      * eapply eps_step_active_wf in STEP0 as [i [GET IN]]; eauto.
      * apply ACTIVEWF. right. auto.
    + destruct t as [[pc gm] b]. unfold add_thread. apply wf_new; auto.
    + specialize (free_add seen (size code) count t SEENWF UNSEEN) as FREE.
      apply wf_size in FREE; auto. apply eps_step_active in STEP0.
      unfold measure, free. rewrite app_length. simpl. lia.
  (* match: we lose a thread and a free slot *)
  - assert (RANGE: fst (fst t) < size code).
    { apply ACTIVEWF. left. auto. }
    exists (measure (size code) (S count) [] blocked inp). split; [constructor|]; auto.
    + intros t0 H. inversion H.
    + destruct t as [[pc gm] b]. unfold add_thread. apply wf_new; auto.
    + specialize (free_add seen (size code) count t SEENWF UNSEEN RANGE) as FREE.
      apply wf_size in FREE. unfold measure, free. simpl. lia.
  (* blocked: we switch an active thread to blocked, but lose a free slot *)
  -  assert (RANGE: fst (fst t) < size code).
     { apply ACTIVEWF. left. auto. }
     exists (measure (size code) (S count) active (blocked++[newt]) inp). split; [constructor|]; auto.
     + intros t0 H. apply ACTIVEWF. simpl. right. auto.
     + intros t0 H. apply in_app_or in H as [H|H].
       * eapply BLOCKEDWF; eauto.
       * inversion H; [|inversion H0]. subst.
         eapply eps_step_blocked_wf in STEP0 as [i [GET IN]]; eauto.
     + destruct t as [[pc gm] b]. unfold add_thread. apply wf_new; auto.
     + specialize (free_add seen (size code) count t SEENWF UNSEEN RANGE) as FREE.
       apply wf_size in FREE. unfold measure, free. rewrite app_length. simpl. lia.
Qed.
