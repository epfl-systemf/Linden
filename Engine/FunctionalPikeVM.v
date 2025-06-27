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
(* For each position in the input (there are (S length (next_str input)) such positions),
   in the worst-case the algorithm explores each (label,bool) configuration.
   Each of these explorations may generate up to two children.
   So we might need as many steps as 4 times the length of the bytecode (2 * 2 boolean values).
   You need one extra step per input position for pvss_nextchar. *)
Definition bytecode_fuel (c:code) (inp:input) : nat :=
  4 * (2 + (length (next_str inp))) * (1 + (length c)).

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

(** * Execution Example  *)

Lemma unroll_loop:
  forall code inp active best blocked seen fuel,
    pike_vm_loop code (PVSS inp active best blocked seen) (S fuel) =
      pike_vm_loop code (pike_vm_func_step code (PVSS inp active best blocked seen)) fuel.
Proof. auto. Qed.


(* Nullable Quantifier Example *)
(* Matching ((a|epsilon)(epsilon|b))* on string "ab" matches "ab", a specificity of Javascript semantics *)

Parameter a : Character.type.
Parameter b : Character.type.

Example a_char : regex := Regex.Character (CdSingle a).
Example b_char : regex := Regex.Character (CdSingle b).
Axiom neq_ab: (a ==? b)%wt = false.
Corollary neq_ba : (b ==? a)%wt = false.
Proof. rewrite EqDec.inversion_false. symmetry. rewrite <- EqDec.inversion_false. apply neq_ab. Qed.

Example nq_regex: regex :=
  greedy_star(Sequence
                (Disjunction(a_char)(Epsilon))
                (Disjunction(Epsilon)(b_char))).

Example nq_bytecode := [Fork 1 10; BeginLoop; ResetRegs []; Fork 4 6; Consume (CdSingle a); Jmp 6; Fork 7 8; Jmp 9; Consume (CdSingle b); EndLoop 0; Accept].

Lemma compile_nq: compilation nq_regex = nq_bytecode.
Proof. auto. Qed.

Example nq_inp: input := Input [a;b] [].

Lemma fuel_nq: bytecode_fuel nq_bytecode nq_inp = 192.
Proof. auto. Qed.

Lemma init_nq: pike_vm_seen_initial_state nq_inp = PVSS nq_inp [(0,GroupMap.empty,CanExit)] None [] initial_seenpcs.
Proof. auto. Qed.

Ltac simpl_step:=
   match goal with
   | [ |- context[VMS.lblbool_eqb ?l1 ?l2] ] => unfold VMS.lblbool_eqb
   | [ |- context[VMS.lblbool_eq_dec ?l1 ?l2] ] => 
       let H := fresh "H" in
       destruct (VMS.lblbool_eq_dec l1 l2) as [H|H];
       auto; try inversion H
   | [ |- context[orb false ?b] ] => simpl orb
   | [ |- context[orb ?b false] ] => simpl orb
   | [ |- context[if false then ?x else ?y] ] => replace (if false then x else y) with y by auto
   | [ |- context[(?x ==? ?x)%wt] ] => rewrite EqDec.reflb
   | [ |- context[(a ==? b)%wt] ] => rewrite neq_ab
   | [ |- context[(b ==? a)%wt] ] => rewrite neq_ba
   | [ |- context[EpsDead] ] => unfold EpsDead
  end.

Ltac one_step:= rewrite unroll_loop; simpl pike_vm_func_step; repeat simpl_step.
  

Lemma nullable_quant:
  pike_vm_match nq_regex nq_inp = Finished (Some (Input [] [b;a], GroupMap.empty)).
Proof. 
  unfold pike_vm_match, getres. rewrite compile_nq. rewrite fuel_nq. rewrite init_nq.
  do 37 one_step.
Qed.
