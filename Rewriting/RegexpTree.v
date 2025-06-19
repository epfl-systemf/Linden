From Linden Require Import ProofSetup.
From Linden.Rewriting Require Import Examples.

Coercion nat_to_N (n: nat) := NoI.N n.

(*|
# Regexp-tree
|*)

Section RegexpTree.
  Context {char: Parameters.Character.class}.

(*|
## Bounded repetitions
|*)

  Section BoundedRepetitions.
    Lemma bounded_util m n delta r:
      def_groups r = [] -> (* r{m}r{n,n+k} ≅ r{m+n,k}, generalized from regexp_tree *)
      (Sequence (Quantified true m 0 r) (Quantified true n delta r))
        ≅ Quantified true (m + n) delta r.
    Proof.
      induction m as [ | m' IHm ]; simpl; intros.
      - etransitivity.
        apply seq_equiv.
        apply quantified_zero_equiv.
        auto.
        reflexivity.
        etransitivity.
        apply sequence_epsilon_left_equiv.
        reflexivity.
      - etransitivity.
        { apply seq_equiv.
          apply quantified_S_equiv.
          auto.
          reflexivity. }
        etransitivity; cycle 1.
        { symmetry.
          eapply quantified_S_equiv.
          auto. }
        etransitivity.
        { symmetry.
          eapply sequence_assoc_equiv. }
        eapply seq_equiv.
        reflexivity.
        auto.
    Qed.

    Lemma bounded_bounded_equiv m n r: (* r{m}r{n} ≅ r{m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true m 0 r) (Quantified true n 0 r))
        ≅ Quantified true (m + n) 0 r.
    Proof. apply bounded_util. Qed.

    Lemma bounded_atmost_equiv m n r: (* r{m}r{0,n} ≅ r{m,m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true m 0 r) (Quantified true 0 n r))
        ≅ Quantified true m n r.
    Proof. intro NO_GROUPS. rewrite bounded_util, PeanoNat.Nat.add_0_r. 1: reflexivity. auto. Qed.

    Lemma bounded_atmost_lazy_equiv (m n: nat) r: (* r{m}r{0,n}? ≅ r{m,m+n}? *)
      def_groups r = [] ->
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
      exists 1, 1, (Disjunction c0 (Sequence c0 c1)).
      tree_equiv_rw.
      exists forward, (init_input [c0; c1; c0]), GroupMap.empty.
      compute_tr_cbv; inversion 1.
    Qed.

    Lemma atmost_atmost_equiv (m n: nat) r: (* r{0,m}r{0,n} ≅ r{0,m+n} *)
      (Sequence (Quantified true 0 m r) (Quantified true 0 n r))
        ≅ Quantified true 0 (m + n) r.
    Admitted.

    (* TODO: Change nequiv to be contextual *)
    Lemma atmost_lazy_atmost_lazy_nequiv: (* r{0,m}?r{0,n}? ≇ r{0,m+n}? *)
      exists (m n: nat) r,
        (Sequence (Quantified false 0 m r) (Quantified false 0 n r))
          ≇ Quantified false 0 (m + n) r.
    Proof.
      exists 1, 1.
      exists (Sequence
           (Disjunction (Sequence c0 c1) (Sequence c0 (Sequence c1 c0)))
           (Disjunction c1 c2)).
      tree_equiv_rw.
      exists forward, (init_input [c0; c1; c0; c1; c2]), GroupMap.empty.
      compute_tr_cbv; inversion 1.
    Admitted.
  End BoundedRepetitions.

(*|
## Character classes

Illustrative examples taken from https://github.com/DmitrySoshnikov/regexp-tree/tree/master/src/optimizer (not complete).
|*)

  Section CharacterClasses.
    Lemma class_union_equiv cd0 cd1:
      Disjunction (Character cd0) (Character cd1) ≅ Character (CdUnion cd0 cd1).
    Proof.
      tree_equiv_rw. tree_equiv_symbex.
      all: leaves_equiv_t.
    Qed.

    Lemma range_range_equiv c0 c1 c2: (* [a-de-f] -> [a-f] *)
      Character.numeric_value c0 <= Character.numeric_value c1 ->
      Character.numeric_value c1 <= Character.numeric_value c2 ->
      Character (CdUnion (CdRange c0 c1) (CdRange c1 c2)) ≅ Character (CdRange c0 c2).
    Proof.
      tree_equiv_rw; tree_equiv_symbex.
      all: repeat match goal with
                  | [ H: _ = true |- _ ] => apply PeanoNat.Nat.leb_le in H
                  | [ H: _ = false |- _ ] => apply PeanoNat.Nat.leb_nle in H
                  end; (lia || reflexivity).
    Qed.

    Lemma class_single_left_equiv c0:
      Character (CdUnion (CdSingle c0) CdEmpty) ≅ Character (CdSingle c0).
    Proof.
      tree_equiv_rw; tree_equiv_symbex; reflexivity.
    Qed.

    Lemma class_single_right_equiv c0:
      Character (CdUnion CdEmpty (CdSingle c0)) ≅ Character (CdSingle c0).
    Proof.
      tree_equiv_rw; tree_equiv_symbex; reflexivity.
    Qed.
  End CharacterClasses.
End RegexpTree.
