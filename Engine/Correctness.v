(** * Correctness theorems for the PikeVM engine  *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeTree PikeVM.
From Linden Require Import PikeTreeSeen PikeVMSeen.
From Linden Require Import PikeEquiv PikeSeenEquiv PikeSubset.
From Linden Require Import EquivMain RegexpTranslation GroupMapMS.
From Warblre Require Import Base Semantics Result.
Import Result.Notations.

(** * Transitive Reflexive Closure of Small-step semantics  *)

Inductive trc {A:Type} {R: A -> A -> Prop}: A -> A -> Prop:=
| trc_refl: forall a, trc a a
| trc_cons:
  forall x y z
    (STEP: R x y)
    (TRC: trc y z),
    trc x z.

Lemma trc_step:
  forall A (R:A->A->Prop) x y,
    R x y ->
    @trc A R x y.
Proof.
  intros A R x y H. eapply trc_cons; eauto. eapply trc_refl.
Qed.


Definition trc_pike_tree := @trc pike_tree_seen_state pike_tree_seen_step.
Definition trc_pike_vm (c:code) := @trc pike_vm_seen_state (pike_vm_seen_step c).


(* The Pike invariant is preserved through the TRC *)
Lemma vm_to_tree:
  forall svm1 st1 svm2 code n1
    (STWF: stutter_wf code)
    (INVARIANT: pike_inv code st1 svm1 n1)
    (TRCVM: trc_pike_vm code svm1 svm2),
    exists st2 n2, trc_pike_tree st1 st2 /\ pike_inv code st2 svm2 n2.
Proof.
  intros svm1 st1 svm2 code n1 STWF INVARIANT TRCVM.
  generalize dependent st1. generalize dependent n1.
  induction TRCVM; intros.
  { exists st1. exists n1. split; auto. apply trc_refl. }
  eapply invariant_preservation in STEP; eauto.
  destruct STEP as [[pts2 [m [TSTEP INV]]] | [m [INV DECR]]].
  - apply IHTRCVM in INV as [st2 [n2 [TTRC TINV]]].
    exists st2. exists n2. split; auto. eapply trc_cons; eauto.
  - apply IHTRCVM in INV as [st2 [n2 [TTRC TINV]]].
    exists st2. exists n2. split; auto.
Qed.

(* Any execution of the PikeVM to a final state corresponds to an execution of the PikeTree *)
Theorem pike_vm_to_pike_tree:
  forall r inp tree result,
    pike_regex r -> 
    bool_tree [Areg r] inp CanExit tree ->
    trc_pike_vm (compilation r) (pike_vm_seen_initial_state inp) (PVSS_final result) ->
    trc_pike_tree (pike_tree_seen_initial_state tree inp) (PTSS_final result).
Proof.
  intros r inp tree result SUBSET TREE TRCVM.
  generalize (initial_pike_inv r inp tree (compilation r) TREE (@eq_refl _ _) SUBSET).
  intros INIT.
  eapply vm_to_tree in TRCVM as [vmfinal [nfinal [TRCTREE INV]]]; eauto.
  - inversion INV; subst. auto.
  - eapply compilation_stutter_wf; eauto.
Qed.

(* Through the TRC of PikeTree, the result is the result of the tree *)
Lemma pike_tree_trc_correct:
  forall s1 s2 result
    (INV: piketreeinv s1 result)
    (TRC: trc_pike_tree s1 s2),
    piketreeinv s2 result.
Proof.
  intros s1 s2 result INV TRC.
  induction TRC; auto.
  apply IHTRC. eapply ptss_preservation; eauto.
Qed.

  
(** * Correctness Theorem of the PikeVM result  *)

Theorem pike_vm_correct:
  forall r inp tree result,
    (* the regex `r` is in the supported subset *)
    pike_regex r ->
    (* `tree` is the tree of the regex `r` for the input `inp` *)
    is_tree [Areg r] inp GroupMap.empty forward tree ->
    (* the result of the PikeVM is `result` *)
    trc_pike_vm (compilation r) (pike_vm_seen_initial_state inp) (PVSS_final result) ->
    (* This `result` is the priority result of the `tree` *)
    result = first_branch' tree inp.
Proof.
  intros r inp tree result SUBSET TREE TRC.
  eapply encode_equal with (b:=CanExit) in TREE as BOOLTREE; pike_subset.
  eapply pike_vm_to_pike_tree in TRC; eauto.
  assert (SUBTREE: pike_subtree tree).
  { eapply pike_actions_pike_tree with (cont:=[Areg r]); eauto.
    pike_subset. }
  generalize (init_piketree_inv tree inp SUBTREE). intros INIT.
  eapply pike_tree_trc_correct in TRC as FINALINV; eauto.
  inversion FINALINV. subst. unfold first_branch. auto.
Qed.

Local Open Scope result_flow.
From Linden Require Import LindenParameters.

Theorem pike_vm_same_warblre:
  forall lr wr str0 rer,
    pike_regex lr ->
    equiv_regex wr lr ->
    rer = computeRer wr ->
    EarlyErrors.Pass_Regex wr nil ->
    exists m res,
      Semantics.compilePattern wr rer = Success m /\
      m str0 0 = Success res /\
      forall result,
        trc_pike_vm (compilation lr) (pike_vm_seen_initial_state (init_input str0)) (PVSS_final result) ->
        EquivDef.equiv_res result res.
Proof.
  intros lr wr str0 rer Hpike Hequiv Heqrer HearlyErrors.
  pose proof equiv_main wr lr rer str0 Hequiv Heqrer HearlyErrors as HequivMain.
  destruct HequivMain as [m [res [Hcompsucc [Hexecsucc Hsameresult]]]].
  exists m. exists res. split; [|split]; auto.
  set (tree := FunctionalUtils.compute_tr [Areg lr] (init_input str0) GroupMap.empty forward).
  specialize (Hsameresult tree eq_refl). destruct Hsameresult as [His_tree Hsameresult].
  intros result Hpikeresult.
  pose proof pike_vm_correct lr (init_input str0) tree result Hpike His_tree Hpikeresult as Hsameresult'.
  rewrite Hsameresult'. assumption.
Qed.

