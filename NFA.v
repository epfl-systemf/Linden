Require Import List Lia.
Import ListNotations.

Require Import Regex.
Require Import Tree.
Require Import Semantics.


(** * NFA Bytecdode *)

Definition label : Type := nat.

Inductive bytecode: Type :=
| Accept
| Consume: char_descr -> bytecode
| Jmp: label -> bytecode
| Fork: label -> label -> bytecode
| SetRegOpen: group_id -> bytecode
| SetRegClose: group_id -> bytecode
| BeginLoop: bytecode
| EndLoop: label -> bytecode.    (* also contains the backedge instead of adding a jump *)

Definition code : Type := list bytecode.

Definition get_pc (c:code) (pc:label) : option bytecode :=
  List.nth_error c pc.


(** * NFA Compilation  *)

(* also returns the next fresh label *)
Fixpoint compile (r:regex) (fresh:label) : code * label :=
  match r with
  | Epsilon => ([], fresh)
  | Character cd => ([Consume cd], S fresh)
  | Disjunction r1 r2 =>
      let (bc1, f1) := compile r1 (S fresh) in
      let (bc2, f2) := compile r2 (S f1) in
      ([Fork (S fresh) (S f1)] ++ bc1 ++ [Jmp f2] ++ bc2, f2)
  | Sequence r1 r2 =>
      let (bc1, f1) := compile r1 fresh in
      let (bc2, f2) := compile r2 f1 in
      (bc1 ++ bc2, f2)
  (* no capture reset for now *)
  | Star r1 =>
      let (bc1, f1) := compile r1 (S (S fresh)) in
      ([Fork (S fresh) (S f1); BeginLoop] ++ bc1 ++ [EndLoop fresh], S f1)
  | Group gid r1 =>
      let (bc1, f1) := compile r1 (S fresh) in
      ([SetRegOpen gid] ++ bc1 ++ [SetRegClose gid], S f1)
  end.



Lemma fresh_correct:
  forall r fresh l next,
    compile r fresh = (l, next) ->
    fresh + List.length l = next.
Proof.
  intros r.
  induction r; intros fresh l next COMPILE.
  - inversion COMPILE. subst. simpl. lia.
  - inversion COMPILE. subst. simpl. lia.
  - inversion COMPILE.
    destruct (compile r1 (S fresh)) as [bc1 f1] eqn:COMP1. destruct (compile r2 (S f1)) as [bc2 f2] eqn:COMP2.
    inversion H0. subst f2. apply IHr1 in COMP1. apply IHr2 in COMP2. simpl.
    rewrite <- COMP1 in COMP2. simpl in COMP2. rewrite app_length. simpl. lia.
  - inversion COMPILE.
    destruct (compile r1 fresh) as [bc1 f1] eqn:COMP1. destruct (compile r2 f1) as [bc2 f2] eqn:COMP2.
    inversion H0. subst f2. apply IHr1 in COMP1. apply IHr2 in COMP2.
    rewrite <- COMP1 in COMP2. rewrite app_length. lia.
  - inversion COMPILE.
    destruct (compile r (S (S fresh))) as [bc1 f1] eqn:COMP1. inversion H0. apply IHr in COMP1.
    subst. simpl. rewrite app_length. simpl. lia.
  - inversion COMPILE.
    destruct (compile r (S fresh)) as [bc1 f1] eqn:COMP1. inversion H0. apply IHr in COMP1.
    subst. simpl. rewrite app_length. simpl. lia.
Qed.


(** * NFA Exponential Semantics  *)
(* exponential because we're not tracking the seen set *)

Definition registers : Type := group_id -> nat.

Definition thread : Type := (label * registers).

Definition nfa_state : Type :=
  (* string, index, active, blocked, bestmatch *)
  (input * nat * list thread * list thread * option thread).
