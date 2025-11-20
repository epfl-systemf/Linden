(* The PikeVm algorithm, expressed as a fuel-based function *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset Prefix.
From Linden Require Import PikeVM Correctness SeenSets Semantics.Examples.
From Linden Require Import Parameters.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import FunctionalUtils FunctionalSemantics.

Section FunctionalPikeVM.
  Context {params: LindenParameters}.
  Context {VMS: VMSeen}.
  Context {strs:StrSearch}.
  Context (rer: RegExpRecord).
(** * Functional Definition  *)


(* the non-prefix accelerated non-lazyprefix functional version of the small step *)
Definition pike_vm_non_lazyprefix_func_step (c:code) (pvs:pike_vm_state) : pike_vm_state :=
  match pvs with
  | PVS_final _ => pvs
  | PVS inp active best blocked nextprefix seen =>
      match active with
      | [] =>
          match blocked with
          | [] => PVS_final best (* pvs_final *)
          | thr::blocked =>
              match (advance_input inp forward) with
              | None => PVS_final best (* pvs_end *)
              | Some nextinp => PVS nextinp (thr::blocked) best [] nextprefix initial_seenpcs (* pvs_nextchar *)
              end
          end     
      | t::active =>
          match (seen_thread seen t) with
          | true => PVS inp active best blocked nextprefix seen (* pvs_skip *)
          | false =>
              let nextseen := add_thread seen t in
              match (epsilon_step rer t c inp) with
              | EpsActive nextactive =>
                  PVS inp (nextactive++active) best blocked nextprefix nextseen (* pvs_active *)
              | EpsMatch =>
                  PVS inp [] (Some (inp,gm_of t)) blocked nextprefix nextseen (* pvs_match *)
              | EpsBlocked newt =>
                  PVS inp active best (blocked ++ [newt]) nextprefix nextseen (* pvs_blocked *)
              end
          end
      end
  end.

(* a functional version of the small step *)
Definition pike_vm_func_step (c:code) (lit:literal) (pvs:pike_vm_state) : pike_vm_state :=
  match pvs with
  | PVS_final _ => pvs
  | PVS inp active best blocked nextprefix seen =>
      match active with
      | [] =>
          match blocked with
          | [] =>
              match nextprefix with
              | Some n =>
                let nextinp := advance_input_n inp (S n) forward in
                PVS nextinp [pike_vm_initial_thread] best [] (next_prefix_counter nextinp lit) initial_seenpcs (* pvs_jump *)
              | None => PVS_final best (* pvs_final *)
              end
          | thr::blocked =>
              match (advance_input inp forward) with
              | None => PVS_final best (* pvs_end *)
              | Some nextinp =>
                  match nextprefix with
                  | None => PVS nextinp (thr::blocked) best [] None initial_seenpcs (* pvs_nextchar *)
                  | Some 0 => PVS nextinp (thr::blocked ++ [pike_vm_initial_thread]) best [] (next_prefix_counter nextinp lit) initial_seenpcs (* pvs_nextchar_star *)
                  | Some (S n) => PVS nextinp (thr::blocked) best [] (Some n) initial_seenpcs (* pvs_nextchar_star_skip *)
                  end
              end
          end     
      | t::active =>
          match (seen_thread seen t) with
          | true => PVS inp active best blocked nextprefix seen (* pvs_skip *)
          | false =>
              let nextseen := add_thread seen t in
              match (epsilon_step rer t c inp) with
              | EpsActive nextactive =>
                  PVS inp (nextactive++active) best blocked nextprefix nextseen (* pvs_active *)
              | EpsMatch =>
                  PVS inp [] (Some (inp,gm_of t)) blocked None nextseen (* pvs_match *)
              | EpsBlocked newt =>
                  PVS inp active best (blocked ++ [newt]) nextprefix nextseen (* pvs_blocked *)
              end
          end
      end
  end.

Lemma pike_vm_same_step_with_no_nextprefix:
  forall c inp active best blocked seen lit,
    pike_vm_non_lazyprefix_func_step c (PVS inp active best blocked None seen) =
    pike_vm_func_step c lit (PVS inp active best blocked None seen).
Proof. reflexivity. Qed.

(* looping the small step function until fuel runs out or a final state is reached *)
Fixpoint pike_vm_loop (c:code) (lit:literal) (pvs:pike_vm_state) (fuel:nat) : pike_vm_state :=
  match pvs with
  | PVS_final _ => pvs
  | _ =>
      match fuel with
      | 0 => pvs
      | S fuel =>
          pike_vm_loop c lit (pike_vm_func_step c lit pvs) fuel
      end
  end.

(* an upper bound for the fuel necessary to compute a result *)
Definition bytecode_fuel (c:code) (inp:input) : nat :=
  (4 * length c) + 1 + (length (next_str inp) * (1 + 4 * length c)). 

Inductive matchres : Type :=
| OutOfFuel
| Finished: option leaf -> matchres.

Definition getres (pvs:pike_vm_state) : matchres :=
  match pvs with
  | PVS_final best => Finished best
  | _ => OutOfFuel
  end.

(* Functional version of the PikeVM *)
(* lit is never used in this version, so anything can be passed *)
Definition pike_vm_match (r:regex) (lit:literal) (inp:input) : matchres :=
  let code := compilation r in
  let fuel := bytecode_fuel code inp in
  let pvsinit := pike_vm_initial_state inp in
  getres (pike_vm_loop code lit pvsinit fuel).

(* Functional version of the lazy prefix PikeVM *)
Definition pike_vm_match_lazyprefix (r:regex) (inp:input) : matchres :=
  let code := compilation r in
  let fuel := bytecode_fuel code inp in
  let lit := extract_literal r in
  let pvsinit := pike_vm_initial_state_lazyprefix lit inp in
  getres (pike_vm_loop code lit pvsinit fuel).
                                                   

(** * Smallstep correspondence  *)

Inductive final_state: pike_vm_state -> Prop :=
| pfinal: forall best, final_state (PVS_final best).

Ltac match_destr:=
  match goal with
  | [ H : match ?x with _ => _ end = _  |- _ ] => let H := fresh "H" in destruct x eqn:H
  end.

Theorem func_step_correct:
  forall c lit pvs1 pvs2,
    pike_vm_func_step c lit pvs1 = pvs2 ->
    pike_vm_step rer c lit pvs1 pvs2 \/ final_state pvs1.
Proof.
  unfold pike_vm_func_step. intros c lit pvs1 pvs2 H.
  repeat match_destr; subst; try solve[left; constructor; auto].
  right. constructor.
Qed.

Corollary func_step_not_final:
  forall c lit inp active best blocked nextprefix seen,
    pike_vm_step rer c lit (PVS inp active best blocked nextprefix seen) (pike_vm_func_step c lit (PVS inp active best blocked nextprefix seen)).
Proof.
  intros c lit inp active best blocked nextprefix seen. specialize (func_step_correct c lit (PVS inp active best blocked nextprefix seen) _ (@eq_refl _ _)).
  intros [H|H]; auto. inversion H.
Qed.

Theorem loop_trc:
  forall c lit pvs1 pvs2 fuel,
    pike_vm_loop c lit pvs1 fuel = pvs2 ->
    trc_pike_vm rer c lit pvs1 pvs2.
Proof.
  intros c lit pvs1 pvs2 fuel H.
  generalize dependent pvs1. induction fuel; intros; simpl in H.
  { destruct pvs1; inversion H. constructor. constructor. }
  match_destr; subst.
  - econstructor; eauto. apply func_step_not_final. apply IHfuel. auto.
  - constructor.
Qed.

(* when the function finishes, it returns the correct result *)
Theorem pike_vm_match_correct:
  forall r lit inp result,
    pike_vm_match r lit inp = Finished result ->
    trc_pike_vm rer (compilation r) lit (pike_vm_initial_state inp) (PVS_final result).
Proof.
  unfold pike_vm_match, getres. intros r lit inp result H. 
  match_destr; inversion H; subst.
  eapply loop_trc; eauto.
Qed.

(* when the function finishes, it returns the correct result *)
Theorem pike_vm_match_lazyprefix_correct:
  forall r inp result,
    pike_vm_match_lazyprefix r inp = Finished result ->
    trc_pike_vm rer (compilation r) (extract_literal r) (pike_vm_initial_state_lazyprefix (extract_literal r) inp) (PVS_final result).
Proof.
  unfold pike_vm_match_lazyprefix, getres. intros r inp result H. 
  match_destr; inversion H; subst.
  eapply loop_trc; eauto.
Qed.

(* TODO: replace with theorem where the fuel is derived from the complexity of the PikeVM *)
Axiom pike_vm_fuel: forall r lit inp, pike_vm_match r lit inp <> OutOfFuel.

(* we show that the PikeVM fits the scheme of an engine *)
#[refine]
Instance PikeVMEngine: Engine rer := {
  exec r inp := match pike_vm_match r (extract_literal r) inp with
                | OutOfFuel => None
                | Finished res => res
                end;
  supported_regex := pike_regex;
}.
  (* exec_correct *)
  intros r inp ol Hsubset.
  destruct pike_vm_match eqn:Hmatch; [pose proof pike_vm_fuel r (extract_literal r) inp; contradiction|].
  split.
  - intros [tree [Htree Hleaf]].
    subst. eauto using pike_vm_match_correct, pike_vm_correct.
  - intros ?; subst.
    pose proof (is_tree_productivity rer [Areg r] inp Groups.GroupMap.empty forward) as [tree Htree].
    exists tree.
    split; eauto.
    symmetry. eauto using pike_vm_match_correct, pike_vm_correct.
Qed.

End FunctionalPikeVM.

(** * Execution Examples  *)

From Linden Require Import Inst.
From Warblre Require Import Inst.
Require Import Coq.Strings.Ascii Coq.Strings.String.
Open Scope string_scope.

Section Example.
  Context {strs: StrSearch}.

  (** * Nullable Quantifier Example *)
  (* Matching ((a|epsilon)(epsilon|b))* on string "ab" matches "ab", a specificity of Javascript semantics *)

  Definition a : Character.type := $ "a".
  Definition b : Character.type := $ "b".

  Example a_char : regex := Regex.Character (CdSingle a).
  Example b_char : regex := Regex.Character (CdSingle b).

  Example nq_regex: regex :=
    greedy_star(Sequence
                  (Disjunction(a_char)(Epsilon))
                  (Disjunction(Epsilon)(b_char))).

  Example nq_bytecode := [Fork 1 10; BeginLoop; ResetRegs []; Fork 4 6; Consume (CdSingle a); Jmp 6; Fork 7 8; Jmp 9; Consume (CdSingle b); EndLoop 0; Accept].

  Lemma compile_nq: compilation nq_regex = nq_bytecode.
  Proof. auto. Qed.

  Example nq_inp: input := Input [a;b] [].

  Lemma nullable_quant:
    pike_vm_match (rer_of nq_regex) nq_regex Impossible nq_inp = Finished (Some (Input [] [b;a], GroupMap.empty)).
  Proof. reflexivity. Qed.

(** * Example from the paper - Figure 15  *)
(* regex (a*|a)b on string "ab" *)

Example paper_regex : regex := Sequence (Group 1 (Disjunction (greedy_star a_char) a_char)) b_char.

Example paper_bytecode := [SetRegOpen 1; Fork 2 8; Fork 3 7; BeginLoop; ResetRegs []; Consume (CdSingle a);
                           EndLoop 2; Jmp 9; Consume (CdSingle a); SetRegClose 1; Consume (CdSingle b); Accept].

Lemma compile_paper: compilation paper_regex = paper_bytecode.
Proof. auto. Qed.

Example paper_input := Input [a;b] [].

Example paper_tree: tree :=
  GroupAction (Open 1) (
      Choice
        (Choice (
             GroupAction (Reset []) (Read a (Progress (
                                                 Choice (GroupAction (Reset []) Mismatch)
                                                   (GroupAction (Close 1) (Read b Match)))
               ))
           ) (GroupAction (Close 1) Mismatch))
        (Read a (GroupAction (Close 1) (Read b Match)))).

Lemma paper_is_tree:
  is_tree (rer_of paper_regex) [Areg paper_regex] paper_input GroupMap.empty forward paper_tree.
Proof.
  apply compute_tr_eq_is_tree. reflexivity.
Qed.

Example final_gm : GroupMap.t :=
  GroupMap.close 1 1 (GroupMap.open 0 1 GroupMap.empty).

Lemma paper_pikevm_exec:
  pike_vm_match (rer_of paper_regex) paper_regex Impossible paper_input = Finished (Some (Input [] [b;a], final_gm)).
Proof. reflexivity. Qed.

End Example.
