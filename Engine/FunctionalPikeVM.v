(* The PikeVm algorithm, expressed as a fuel-based function *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import PikeVM PikeVMSeen Correctness.
From Warblre Require Import Base.

(** * Functional Definition  *)

(* a functional version of the small step *)
Definition pike_vm_func_step (c:code) (pvs:pike_vm_seen_state) : pike_vm_seen_state :=
  match pvs with
  | PVSS_final _ => pvs
  | PVSS inp active best blocked seen =>
      match active with
      | [] =>
          match blocked with
          | [] => PVSS_final best (* pvss_final *)
          | thr::blocked =>
              match (advance_input inp forward) with
              | None => PVSS_final best (* pvss_end *)
              | Some nextinp => PVSS nextinp (thr::blocked) best [] initial_seenpcs (* pvss_nextchar *)
              end
          end     
      | t::active =>
          match (seen_thread seen t) with
          | true => PVSS inp active best blocked seen (* pvss_skip *)
          | false =>
              let nextseen := add_thread seen t in
              match (epsilon_step t c inp) with
              | EpsActive nextactive =>
                  PVSS inp (nextactive++active) best blocked nextseen (* pvss_active *)
              | EpsMatch =>
                  PVSS inp [] (Some (inp,gm_of t)) blocked nextseen (* pvss_match *)
              | EpsBlocked newt =>
                  PVSS inp active best (blocked ++ [newt]) nextseen (* pvss_blocked *)
              end
          end
      end
  end.

(* looping the small step function until fuel runs out or a final state is reached *)
Fixpoint pike_vm_loop (c:code) (pvs:pike_vm_seen_state) (fuel:nat) : pike_vm_seen_state :=
  match pvs with
  | PVSS_final _ => pvs
  | _ =>
      match fuel with
      | 0 => pvs
      | S fuel =>
          pike_vm_loop c (pike_vm_func_step c pvs) fuel
      end
  end.

(* an upper bound for the fuel necessary to compute a result *)
Definition bytecode_fuel (c:code) (inp:input) : nat :=
  2 * (S (length (next_str inp))) * (S (length c)).

Inductive matchres : Type :=
| OutOfFuel
| Finished: option leaf -> matchres.

Definition getres (pvs:pike_vm_seen_state) : matchres :=
  match pvs with
  | PVSS_final best => Finished best
  | _ => OutOfFuel
  end.

(* Functional version of the PikeVM *)
Definition pike_vm_match (r:regex) (inp:input) : matchres :=
  let code := compilation r in
  let fuel := bytecode_fuel code inp in
  let pvsinit := pike_vm_seen_initial_state inp in
  getres (pike_vm_loop code pvsinit fuel).
                                                   

(** * Smallstep correspondence  *)

Inductive final_state: pike_vm_seen_state -> Prop :=
| pfinal: forall best, final_state (PVSS_final best).

Ltac match_destr:=
  match goal with
  | [ H : match ?x with _ => _ end = _  |- _ ] => let H := fresh "H" in destruct x eqn:H
  end.

Theorem func_step_correct:
  forall c pvs1 pvs2,
    pike_vm_func_step c pvs1 = pvs2 ->
    pike_vm_seen_step c pvs1 pvs2 \/ final_state pvs1.
Proof.
  unfold pike_vm_func_step. intros c pvs1 pvs2 H.
  repeat match_destr; subst; try solve[left; constructor; auto].
  right. constructor.
Qed.

Corollary func_step_not_final:
  forall c inp active best blocked seen,
    pike_vm_seen_step c (PVSS inp active best blocked seen) (pike_vm_func_step c (PVSS inp active best blocked seen)).
Proof.
  intros c inp active best blocked seen. specialize (func_step_correct c (PVSS inp active best blocked seen) _ (@eq_refl _ _)).
  intros [H|H]; auto. inversion H.
Qed.

Theorem loop_trc:
  forall c pvs1 pvs2 fuel,
    pike_vm_loop c pvs1 fuel = pvs2 ->
    trc_pike_vm c pvs1 pvs2.
Proof.
  intros c pvs1 pvs2 fuel H.
  generalize dependent pvs1. induction fuel; intros; simpl in H.
  { destruct pvs1; inversion H. constructor. constructor. }
  match_destr; subst.
  - econstructor; eauto. apply func_step_not_final. apply IHfuel. auto.
  - constructor.
Qed.

(* when the function finishes, it retruns the correct result *)
Theorem pike_vm_match_correct:
  forall r inp result,
    pike_vm_match r inp = Finished result ->
    trc_pike_vm (compilation r) (pike_vm_seen_initial_state inp) (PVSS_final result).
Proof.
  unfold pike_vm_match, getres. intros r inp result H. 
  match_destr; subst; inversion H; subst.
  eapply loop_trc; eauto.
Qed.
