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

(** * Pike VM measure  *)

(* the number of free slots in a seen set *)
(* the total number of slots is 2 times the size of the code: each label can be added with 2 possible LoopBool values *)
(* we remove the number of distinct entries in the seen set *)
Definition free (codesize:nat) (seen:seenpcs) : nat :=
  (2 * codesize) - (VMS.count seen).

Lemma free_initial:
  forall codesize, free codesize initial_seenpcs = 2 * codesize.
Proof.
  intros codesize. unfold free, initial_seenpcs. rewrite VMS.count_empty. lia.
Qed.

(* this is FALSE, we need a nice property on the seen set and pc of t before doing that *)
Lemma free_add:
  forall codesize seen t, free codesize seen = 1 + free codesize (add_thread seen t).
Proof.
Admitted.
  

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

(* The number of free slots decreases at most steps *)
(* In some cases ( afork), a new thread is created but the number of free slots decreases: this is why free slots are multiplied by 2 *)
(* As we change characters, the seen set might get 2*codesize new free slots (multiplied by 2 for the measure) *)
(* But the input decreases, which makes the measure also decrease, because input size is multiplied by (1 + 4*codesize)  *)
Definition measure (codesize:nat) (pvs: pike_vm_seen_state) : nat :=
  match pvs with
  | PVSS_final _ => 0
  | PVSS inp active best blocked seen =>
      (2 * free codesize seen) + length active + length blocked + (inpsize inp * (1 + 4 * codesize))
  end.

Definition size (c:code) : nat := length c.

(** * PikeVM measure decrease *)

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
Theorem pikevm_decreases:
  forall code pvs1 pvs2,
    pike_vm_seen_step rer code pvs1 pvs2 ->
    measure (size code) pvs2 < measure (size code) pvs1.
Proof.
  intros code pvs1 pvs2 STEP. inversion STEP; subst; simpl measure.
  (* when reaching a final state, we end up with a measure of 0, while the previous measure was strictly positive *)
  - specialize (inpsize_strict inp) as SIZE. lia.
  - specialize (inpsize_strict inp) as SIZE. lia.
  (* nextchar: we might add (2*codesize) free slots, but we lose an input length *)
  - rewrite free_initial. apply advance_input_decreases in ADVANCE.
    repeat rewrite PeanoNat.Nat.add_0_r.
    apply increase_mult with (x:= 4 * size code) in ADVANCE as NEXT. simpl in NEXT. lia.
  (* skip: we lose a thread *)
  - lia.
  (* active: we may add a new thread, but lose a free slot *)
  - specialize (free_add (size code) seen t) as FREE.
    apply  eps_step_active in STEP0. rewrite app_length. lia.
  (* match: we lose a thread and a free slot *)
  - specialize (free_add (size code) seen t) as FREE. lia.
  (* blocked: we switch an active thread to blocked, but lose a free slot *)
  - specialize (free_add (size code) seen t) as FREE. 
    rewrite app_length. simpl. lia.
Qed.
