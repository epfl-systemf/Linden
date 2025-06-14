(* Defining Capture Groups Registers *)
(* Keeping an index of when was a group opened and closed *)

Require Import List Lia.
Import ListNotations.
Require Import MSetList OrdersAlt PeanoNat FMapList.

From Linden Require Import Chars.
From Warblre Require Import Typeclasses.

(** * Group Manipulation  *)

Module GroupId <: OrderedTypeWithLeibniz.
  Include Nat.
  Lemma eq_leibniz : forall x y, Nat.eq x y -> x = y. Proof. trivial. Qed.
End GroupId.

Definition group_id : Type := GroupId.t.

(** ** Group Sets *)

Definition group_set : Type := list group_id.

(** ** Group actions *)
(* The possible operations done on group maps during matching *)
Inductive groupaction : Type :=
| Open (g: group_id)
| Close (g: group_id)
| Reset (gl: group_set)
.

(** ** Group Maps *)

Require Import FMapFacts.

(* Partial maps from group ids to capture ranges *)
Module GroupMap.

  (* Capture groups are represented by their range in the matched string. *)
  (* The start and end indices are inclusive and exclusive respectively. *)
  (* A group is considered open when it has no end index, and closed o.w. *)
  Record range : Type := Range { startIdx : nat; endIdx : option nat }.
  Instance range_EqDec : EqDec.type range := { eq_dec := ltac:(repeat decide equality) }.

  Module MapS <: FMapInterface.S.
    Module GroupId' <: OrderedTypeOrig.
      Include OrdersAlt.Backport_OT GroupId.

      Lemma compare_refl k:
        let k0 := k in
        let k1 := k in
        compare k0 k1 = EQ (y := k1) (eq_refl k0).
      Proof.
        intros.
        generalize (eq_refl k0: k0 = k1).
        clearbody k1; intros.
        destruct compare; unfold lt in *; try lia.
        subst; f_equal.
        apply Eqdep_dec.UIP_refl_nat.
      Qed.
    End GroupId'.

    Include FMapList.Make GroupId'.
  End MapS.

  Module Facts := FMapFacts.Facts MapS.

  Definition t := MapS.t range.

  Definition empty : t := MapS.empty range.

  Definition find : group_id -> t -> option range := MapS.find (elt := range).

  Definition add: group_id -> range -> t -> t := MapS.add (elt := range).

  Section ops.
    Variable currIdx : nat. (* The current index in the string being matched *)

    Definition open (gid : group_id) : t -> t :=
      MapS.add gid (Range currIdx None).

    (* Assumes, but does not check, the g is associated to an open range *)
    Definition close (gid : group_id) (gm : t) : t :=
      match find gid gm with
      | Some (Range startIdx _) =>
          if startIdx <=? currIdx then
            MapS.add gid (Range startIdx (Some currIdx)) gm
          else
            MapS.add gid (Range currIdx (Some startIdx)) gm
      | None => gm
      end.

    Definition reset : group_set -> t -> t :=
      List.fold_left (fun s gid => MapS.remove gid s).

    Definition update (op : groupaction) : t -> t :=
      match op with
      | Open g => open g
      | Close g => close g
      | Reset gs => reset gs
      end.
  End ops.

  Require Import Permutation SetoidList.

  Lemma In_InA_iff [A] (l : list A) (x : A):
    In x l <-> InA eq x l.
  Proof.
    split; eauto using In_InA.
    revert l x; induction l; simpl; inversion 1; subst; eauto.
  Qed.

  Lemma Sorted_unique {T} cmp :
    StrictOrder cmp ->
    forall  (l0 l1: list T),
      Sorted cmp l0 ->
      Sorted cmp l1 ->
      (forall t, In t l0 <-> In t l1) ->
      l0 = l1.
  Proof.
    intros Horder l0 l1 Hl0 Hl1 HP.
    apply eqlistA_ind with (eqA := eq); [ congruence .. | ].
    eapply SortA_equivlistA_eqlistA with (ltA := cmp); eauto.
    - cbv; intros; subst; tauto.
    - intro t; rewrite !InA_alt; split.
      all: intros [t' (-> & ?)].
      all: exists t'; split; try apply HP; eauto.
  Qed.

  Lemma In_elements {elt} x (t: MapS.t elt):
    In x (MapS.elements t) <-> MapS.MapsTo (fst x) (snd x) t.
  Proof.
    rewrite In_InA_iff, Facts.elements_mapsto_iff, !InA_alt.
    unfold MapS.eq_key_elt, MapS.Raw.PX.eqke.
    split; intros [x' (Heq & ?)]; exists x; simpl in *.
    - subst; eauto.
    - destruct x, x'; simpl in *; inversion Heq; subst; eauto.
  Qed.

  Lemma Equal_eq_this (t0: t): forall t1, MapS.Equal t0 t1 -> t0.(MapS.this) = t1.(MapS.this).
  Proof.
    intros.
    eapply Sorted_unique; eauto using MapS.sorted, MapS.Raw.PX.ltk_strorder.
    change (MapS.this ?t) with (MapS.elements t).
    intros; rewrite !In_elements.
    apply Facts.Equal_mapsto_iff; eauto.
  Qed.

  Require Import ProofIrrelevance.

  Lemma Equal_eq (t0 t1: t): MapS.Equal t0 t1 <-> t0 = t1.
  Proof.
    split; [ | intros ->; reflexivity ].
    intros HEq%Equal_eq_this.
    destruct t0, t1; simpl in *; destruct HEq.
    f_equal; apply proof_irrelevance.
  Qed.

  Definition eqb: t -> t -> bool := MapS.equal EqDec.eqb.

  Lemma eqb_eq t0 t1: eqb t0 t1 = true <-> t0 = t1.
  Proof.
    unfold eqb.
    rewrite <- Equal_eq, <- Facts.equal_iff, <- Facts.Equal_Equivb.
    - reflexivity.
    -  apply EqDec.inversion_true.
  Qed.

  #[refine] Instance EqDec_t: EqDec t :=
    { eq_dec t1 t2 := match eqb t1 t2 as b return eqb t1 t2 = b -> _ with
                     | true => fun Heq => left _
                     | false => fun Hneq => right _
                     end eq_refl }.
  Proof.
    - apply eqb_eq; assumption.
    - rewrite <- eqb_eq. congruence.
  Qed.

  (* MapsTo, In *)
  Definition MapsTo := MapS.MapsTo (elt := range).
  Definition In := MapS.In (elt := range).
End GroupMap.

Definition group_map : Type := GroupMap.t.
