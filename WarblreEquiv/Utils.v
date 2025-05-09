From Coq Require Import List.
Import ListNotations.
From Warblre Require Import Typeclasses.

Module List.
  Definition inb {A} `{EqDec A} (x: A) (l: list A): bool :=
    if in_dec EqDec.eq_dec x l then true else false.

  Lemma inb_spec {A} `{EqDec A}:
    forall (x: A) (l: list A), inb x l = true <-> In x l.
  Proof.
    intros x l. unfold inb. destruct (in_dec _ x l).
    - tauto.
    - split. + discriminate. + contradiction.
  Qed.
End List.
