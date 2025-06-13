From Linden Require Import ProofSetup.
From Linden.Rewriting Require Import Examples.

Coercion nat_to_N (n: nat) := NoI.N n.

(*|
# Regexp-tree
|*)

Section RegexpTree.
  Context {char: Parameters.Character.class}.
  Coercion char_to_re (c: Parameters.Character) := Character (CdSingle c).

(*|
## Bounded repetitions
|*)

  Section BoundedRepetitions.
    Lemma bounded_util m n delta r: (* r{m}r{n,n+k} ≅ r{m+n,k}, generalized from regexp_tree *)
      (Sequence (Quantified true m 0 r) (Quantified true n delta r))
        ≅ Quantified true (m + n) delta r.
    Proof.
      induction m as [ | m' IHm ]; simpl; intros.
      - etransitivity.
        apply seq_equiv.
        apply quantified_zero_equiv.
        reflexivity.
        etransitivity.
        apply sequence_epsilon_left_equiv.
        reflexivity.
      - etransitivity.
        { apply seq_equiv.
          apply quantified_S_equiv.
          reflexivity. }
        etransitivity; cycle 1.
        { symmetry.
          eapply quantified_S_equiv. }
        etransitivity.
        { symmetry.
          eapply sequence_assoc_equiv. }
        eapply seq_equiv.
        reflexivity.
        assumption.
    Qed.

    Lemma bounded_bounded_equiv m n r: (* r{m}r{n} ≅ r{m+n} *)
      (Sequence (Quantified true m 0 r) (Quantified true n 0 r))
        ≅ Quantified true (m + n) 0 r.
    Proof. apply bounded_util. Qed.

    Lemma bounded_atmost_equiv m n r: (* r{m}r{0,n} ≅ r{m,m+n} *)
      (Sequence (Quantified true m 0 r) (Quantified true 0 n r))
        ≅ Quantified true m n r.
    Proof. rewrite bounded_util, PeanoNat.Nat.add_0_r; reflexivity. Qed.

    Lemma bounded_atmost_lazy_equiv (m n: nat) r: (* r{m}r{0,n}? ≅ r{m,m+n}? *)
      (Sequence (Quantified true m 0 r) (Quantified false 0 n r))
        ≅ Quantified false m n r.
    Proof.
    Admitted.

    Context (c0 c1 c2: Parameters.Character).
    Context (H01: c0 <> c1) (H12: c0 <> c2) (H02: c1 <> c2) .

    Lemma atmost_bounded_nequiv: (* r{0,m}r{n} ≅ r{n,n+m} *)
      exists m n r,
        (Sequence (Quantified true 0 m r) (Quantified true n 0 r))
          ≇ Quantified true n m r.
    Proof.
      exists 1, 1.
      exists (Disjunction c0 (Sequence c0 c1)).
      apply tree_nequiv_compute_counterexample.
      exists (init_input [c0; c1; c0]), GroupMap.empty, forward.
      compute_tr_cbv.
      inversion 1.
    Qed.

    Lemma atmost_atmost_equiv (m n: nat) r: (* r{0,m}r{0,n} ≅ r{0,m+n} *)
      (Sequence (Quantified true 0 m r) (Quantified true 0 n r))
        ≅ Quantified true 0 (m + n) r.
    Admitted.

    Lemma atmost_lazy_atmost_lazy_nequiv: (* r{0,m}?r{0,n}? ≇ r{0,m+n}? *)
      exists (m n: nat) r,
        (Sequence (Quantified true 0 m r) (Quantified true 0 n r))
          ≇ Quantified true 0 (m + n) r.
    Proof.
      exists 1, 1.
      exists (Sequence
           (Disjunction (Sequence c0 c1) (Sequence c0 (Sequence c1 c0)))
           (Disjunction c1 c2)).
      apply tree_nequiv_compute_counterexample.
      exists (init_input [c0; c1; c0; c1; c2]), GroupMap.empty, forward.
      compute_tr_cbv.
      inversion 1.
    Qed.

    Lemma star_bounded_nequiv: (* r*r{n} ≇ r{n,}? *)
      exists (n: nat) r,
        (Sequence (Quantified true 0 NoI.Inf r) (Quantified true n 0 r))
          ≇ Quantified true n NoI.Inf r.
    Proof.
      exists 1.
      exists (Disjunction c0 (Sequence c0 c1)).
      apply tree_nequiv_compute_counterexample.
      exists (init_input [c0; c1; c0; c1; c2]), GroupMap.empty, forward.
      compute_tr_cbv.
      inversion 1.
    Qed.
  End BoundedRepetitions.

(*|
## Other rewrites

Illustrative examples taken from https://github.com/DmitrySoshnikov/regexp-tree/tree/master/src/optimizer (not complete).
|*)

(* ## unicode pairs *)
(* ## simpler char codes *)
(* ## lower case when using flag i *)

## remove duplicates in char classes
## merge adjacent ranges
Lemma class_sequence_equiv:
    Sequence (Character cd0) (Character cd1) ≅ Character (CdUnion cd0 cd1).

Lemma range_range_equiv: (* [a-de-f] -> [a-f] *)
  Character.numeric_value c0 <= Character.numeric_value c1 ->
  Character.numeric_value c1 <= Character.numeric_value c2 ->
  Character (CdUnion (CdRange c0 c1) (CdRange c1 c2)) ≅ Character (CdRange c0 c2).

## use character class escapes
Lemma class_single_left_equiv:
    Character (CdUnion (CdSingle c0) CdEmpty) ≅ Character (CdSingle c0).
## from char class to single char
## remove unnecessary escapes

Lemma disjunction_class_equiv:
    (Disjunction (Character (CdSingle c0)) (Character (CdSingle c1)))
      ≅ Character (CdUnion (CdSingle c0) (CdSingle c1)).
(* ## dijsunction to char classes a|b ~ [ab] *)
