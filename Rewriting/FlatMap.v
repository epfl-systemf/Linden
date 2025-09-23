From Linden Require Import LeavesEquivalence Parameters.
From Coq Require Import List.
Import ListNotations.


(** * FlatMap Lemmas  *)

(* a propositional version of flat_map *)
(* FlatMap lbase f lmapped means that lmapped corresponds to the list lbase where each element has been replaced by its image by f *)
Inductive FlatMap {X Y:Type} : list X -> (X -> list Y -> Prop) -> list Y -> Prop :=
| FM_nil: forall f,
  FlatMap [] f []
| FM_cons:
  forall lbase f lmapped x ly
    (FM: FlatMap lbase f lmapped)
    (HEAD: f x ly),
    FlatMap (x::lbase) f (ly ++ lmapped).

Property FlatMap_app {X Y: Type}:
  forall (lbase1 lbase2 : list X) (f: X -> list Y -> Prop) (lmapped1 lmapped2: list Y),
    FlatMap lbase1 f lmapped1 ->
    FlatMap lbase2 f lmapped2 ->
    FlatMap (lbase1 ++ lbase2) f (lmapped1 ++ lmapped2).
Proof.
  intros lbase1 lbase2 f lmapped1 lmapped2 FM1 FM2.
  induction FM1.
  - auto.
  - rewrite <- app_assoc, <- app_comm_cons. constructor; auto.
Qed.

Definition determ {A B: Type} (f: A -> B -> Prop) :=
  forall x y1 y2, f x y1 -> f x y2 -> y1 = y2.

Lemma FlatMap_in {A B}:
  forall (l: list A) (f: A -> list B -> Prop) fl x fx,
    determ f ->
    FlatMap l f fl ->
    In x l ->
    f x fx ->
    Forall (fun y => In y fl) fx.
Proof.
  intros l f fl x fx DETERM FM INxl F.
  revert fl FM.
  induction l.
  1: inversion INxl.
  intros fl FM. destruct INxl.
  - subst a. inversion FM; subst.
    assert (ly = fx) by eauto (* using DETERM *). subst ly. clear HEAD FM F IHl.
    induction fx.
    + constructor.
    + constructor.
      * rewrite <- app_comm_cons. left. reflexivity.
      * eapply Forall_impl; eauto. simpl. tauto.
  - inversion FM; subst. specialize (IHl H lmapped FM0).
    eapply Forall_impl; eauto. simpl. intro. rewrite in_app_iff. tauto.
Qed.

Lemma FlatMap_in2 {params: LindenParameters}:
  forall f leaf fleaf seen fseen,
    determ f -> 
    f leaf fleaf ->
    is_seen leaf seen = true ->
    FlatMap seen f fseen ->
    forall x, is_seen x fleaf = true -> is_seen x fseen = true.
Proof.
  intros f leaf fleaf seen fseen H H0 H1 H2 x H3.
  rewrite is_seen_spec in H3, H1. rewrite is_seen_spec.
  specialize (FlatMap_in _ _ _ _ _ H H2 H1 H0).
  intros H4. rewrite Forall_forall in H4. auto.
Qed.

Lemma flatmap_leaves_equiv_l_seen {params: LindenParameters}:
  forall l1 l2 seen f fseen fl1 fl2,
    determ f ->
    leaves_equiv seen l1 l2 ->
    FlatMap l1 f fl1 ->
    FlatMap l2 f fl2 ->
    FlatMap seen f fseen ->
    leaves_equiv fseen fl1 fl2.
Proof.
  intros l1 l2 seen f fseen fl1 fl2 DET EQUIV FM1 FM2 FMSEEN.
  generalize dependent fl1. generalize dependent fl2. generalize dependent fseen.
  induction EQUIV; intros.
  - inversion FM2; subst. inversion FM1; subst. apply leaves_equiv_refl.
  - inversion FM1; subst. apply leaves_equiv_subseen; auto.
    eapply FlatMap_in2; eauto.
  - inversion FM2; subst. symmetry.
    apply leaves_equiv_subseen; auto.
    2: { symmetry. auto. }
    eapply FlatMap_in2; eauto.
  - inversion FM1; inversion FM2; subst.
    specialize (DET _ _ _ HEAD HEAD0). subst.
    apply leaves_equiv_app2; auto.
    + apply leaves_equiv_refl.
    + eapply IHEQUIV; eauto. constructor; auto.
Qed.

Lemma flatmap_leaves_equiv_l {params: LindenParameters}:
  forall leaves1 leaves2 f leavesf1 leavesf2,
    determ f ->
    leaves_equiv [] leaves1 leaves2 ->
    FlatMap leaves1 f leavesf1 ->
    FlatMap leaves2 f leavesf2 ->
    leaves_equiv [] leavesf1 leavesf2.
Proof.
  intros.
  eapply flatmap_leaves_equiv_l_seen with (seen := []); eauto. constructor.
Qed.