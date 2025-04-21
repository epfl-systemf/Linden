From Warblre Require Import List.
From Coq Require Import List Lia ZArith.
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


Lemma skipn_ind_inv {A: Type}:
  forall (i1 i2: Z) (l: list A),
    (0 <= i1)%Z -> (i1 <= Z.of_nat (length l))%Z -> (0 <= i2)%Z -> (i2 <= Z.of_nat (length l))%Z ->
    skipn (Z.to_nat i1) l = skipn (Z.to_nat i2) l ->
    i1 = i2.
Proof.
  intros i1 i2 l Hi1_nneg Hi1_le_n Hi2_nneg Hi2_le_n Hskipn.
  apply (f_equal (length (A := A))) in Hskipn.
  do 2 rewrite skipn_length in Hskipn.
  lia.
Qed.
