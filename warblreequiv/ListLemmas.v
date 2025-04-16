From Warblre Require Import List.
From Coq Require Import List Lia.
Import ListNotations.

Lemma decr_range: forall base l: nat,
  base >= 1 -> List.map (fun x => x-1) (List.List.Range.Nat.Length.range base l) =
    List.List.Range.Nat.Length.range (base-1) l.
Proof.
  intros base l.
  revert base.
  induction l as [|l IHl].
  - intros base Hb1. simpl. reflexivity.
  - intros base Hb1. simpl. f_equal.
    replace (base - 1 + 1) with (base + 1 - 1) by lia. apply IHl. lia.
Qed.