(* The PikeVm algorithm, expressed as a fuel-based function *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import PikeVM Correctness.
From Linden Require Import Parameters.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import FunctionalUtils FunctionalSemantics.

Section FunctionalPikeVM.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).
(** * Functional Definition  *)

(* a functional version of the small step *)
Definition pike_vm_func_step (c:code) (pvs:pike_vm_state) : pike_vm_state :=
  match pvs with
  | PVS_final _ => pvs
  | PVS inp active best blocked seen =>
      match active with
      | [] =>
          match blocked with
          | [] => PVS_final best (* pvs_final *)
          | thr::blocked =>
              match (advance_input inp forward) with
              | None => PVS_final best (* pvs_end *)
              | Some nextinp => PVS nextinp (thr::blocked) best [] initial_seenpcs (* pvs_nextchar *)
              end
          end     
      | t::active =>
          match (seen_thread seen t) with
          | true => PVS inp active best blocked seen (* pvs_skip *)
          | false =>
              let nextseen := add_thread seen t in
              match (epsilon_step rer t c inp) with
              | EpsActive nextactive =>
                  PVS inp (nextactive++active) best blocked nextseen (* pvs_active *)
              | EpsMatch =>
                  PVS inp [] (Some (inp,gm_of t)) blocked nextseen (* pvs_match *)
              | EpsBlocked newt =>
                  PVS inp active best (blocked ++ [newt]) nextseen (* pvs_blocked *)
              end
          end
      end
  end.

(* looping the small step function until fuel runs out or a final state is reached *)
Fixpoint pike_vm_loop (c:code) (pvs:pike_vm_state) (fuel:nat) : pike_vm_state :=
  match pvs with
  | PVS_final _ => pvs
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
   You need one extra step per input position for pvs_nextchar. *)
Definition bytecode_fuel (c:code) (inp:input) : nat :=
  4 * (2 + (length (next_str inp))) * (1 + (length c)).

Inductive matchres : Type :=
| OutOfFuel
| Finished: option leaf -> matchres.

Definition getres (pvs:pike_vm_state) : matchres :=
  match pvs with
  | PVS_final best => Finished best
  | _ => OutOfFuel
  end.

(* Functional version of the PikeVM *)
Definition pike_vm_match (r:regex) (inp:input) : matchres :=
  let code := compilation r in
  let fuel := bytecode_fuel code inp in
  let pvsinit := pike_vm_initial_state inp in
  getres (pike_vm_loop code pvsinit fuel).
                                                   

(** * Smallstep correspondence  *)

Inductive final_state: pike_vm_state -> Prop :=
| pfinal: forall best, final_state (PVS_final best).

Ltac match_destr:=
  match goal with
  | [ H : match ?x with _ => _ end = _  |- _ ] => let H := fresh "H" in destruct x eqn:H
  end.

Theorem func_step_correct:
  forall c pvs1 pvs2,
    pike_vm_func_step c pvs1 = pvs2 ->
    pike_vm_step rer c pvs1 pvs2 \/ final_state pvs1.
Proof.
  unfold pike_vm_func_step. intros c pvs1 pvs2 H.
  repeat match_destr; subst; try solve[left; constructor; auto].
  right. constructor.
Qed.

Corollary func_step_not_final:
  forall c inp active best blocked seen,
    pike_vm_step rer c (PVS inp active best blocked seen) (pike_vm_func_step c (PVS inp active best blocked seen)).
Proof.
  intros c inp active best blocked seen. specialize (func_step_correct c (PVS inp active best blocked seen) _ (@eq_refl _ _)).
  intros [H|H]; auto. inversion H.
Qed.

Theorem loop_trc:
  forall c pvs1 pvs2 fuel,
    pike_vm_loop c pvs1 fuel = pvs2 ->
    trc_pike_vm rer c pvs1 pvs2.
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
    trc_pike_vm rer (compilation r) (pike_vm_initial_state inp) (PVS_final result).
Proof.
  unfold pike_vm_match, getres. intros r inp result H. 
  match_destr; subst; inversion H; subst.
  eapply loop_trc; eauto.
Qed.

(** * Execution Example  *)

Lemma unroll_loop:
  forall code inp active best blocked seen fuel,
    pike_vm_loop code (PVS inp active best blocked seen) (S fuel) =
      pike_vm_loop code (pike_vm_func_step code (PVS inp active best blocked seen)) fuel.
Proof. auto. Qed.

End FunctionalPikeVM.


From Linden Require Import Inst.
From Warblre Require Import Inst.
Require Import Coq.Strings.Ascii Coq.Strings.String.
Open Scope string_scope.

(* Nullable Quantifier Example *)
(* Matching ((a|epsilon)(epsilon|b))* on string "ab" matches "ab", a specificity of Javascript semantics *)
Section Example.
  Context (rer: RegExpRecord).

  Definition a : Character.type := $ "a".
  Definition b : Character.type := $ "b".

  Example a_char : regex := Regex.Character (CdSingle a).
  Example b_char : regex := Regex.Character (CdSingle b).
  Lemma charmatch_same:
    forall c, char_match rer c (CdSingle c) = true.
  Proof. unfold char_match, char_match'. intros. apply EqDec.reflb. Qed.

  (* These characters cannot match, regardless of the flags *)
  Lemma charmatch_ab:
    char_match rer a (CdSingle b) = false.
  Proof. reflexivity. Qed.
  Lemma charmatch_ba:
    char_match rer b (CdSingle a) = false.
  Proof. reflexivity. Qed.



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

  Lemma init_nq: pike_vm_initial_state nq_inp = PVS nq_inp [(0,GroupMap.empty,CanExit)] None [] initial_seenpcs.
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
   | [ |- context[char_match _ ?x (CdSingle ?x)] ] => rewrite charmatch_same
   | [ |- context[char_match rer a (CdSingle b)] ] => rewrite charmatch_ab
   | [ |- context[char_match rer b (CdSingle a)] ] => rewrite charmatch_ba
   | [ |- context[EpsDead] ] => unfold EpsDead
  end.

Ltac one_step:= rewrite unroll_loop; simpl pike_vm_func_step; repeat simpl_step.
  

Lemma nullable_quant:
  pike_vm_match rer nq_regex nq_inp = Finished (Some (Input [] [b;a], GroupMap.empty)).
Proof. 
  unfold pike_vm_match, getres. rewrite compile_nq. rewrite fuel_nq. rewrite init_nq.
  do 37 one_step. 
Qed.

(** * Example from the paper  *)
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
  is_tree rer [Areg paper_regex] paper_input GroupMap.empty forward paper_tree.
Proof.
  unfold paper_input.
  repeat (econstructor; simpl; try rewrite charmatch_same).
  unfold greedy_star. replace +∞ with (NoI.N 1 + +∞)%NoI by auto.
  econstructor; simpl; eauto.
  2: { repeat (constructor; simpl). (*rewrite charmatch_ab. auto.*) }
  repeat (econstructor; simpl; try rewrite charmatch_same); simpl.
  unfold greedy_star. replace +∞ with (NoI.N 1 + +∞)%NoI by auto.
  repeat (econstructor; simpl; auto).
  (* { rewrite charmatch_ba. auto. }
  rewrite charmatch_same. auto. *)
Qed.

Example final_gm : GroupMap.t :=
  GroupMap.close 1 1 (GroupMap.open 0 1 GroupMap.empty).

Lemma paper_fuel: bytecode_fuel paper_bytecode paper_input = 208.
Proof. auto. Qed.

Lemma paper_init: pike_vm_initial_state paper_input = PVS paper_input [(0,GroupMap.empty,CanExit)] None [] initial_seenpcs.
Proof. auto. Qed.

Lemma paper_pikevm_exec:
  pike_vm_match rer paper_regex paper_input = Finished (Some (Input [] [b;a], final_gm)).
Proof. 
  unfold pike_vm_match, getres, final_gm. rewrite compile_paper. rewrite paper_fuel. rewrite paper_init.
  do 24 one_step. (*auto.*)
Qed.

End Example.
