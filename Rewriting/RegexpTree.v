From Linden Require Import ProofSetup.
From Linden.Rewriting Require Import Examples.

Coercion nat_to_N (n: nat) := NoI.N n.

(*|
# Regexp-tree
|*)

Section RegexpTree.
  Context {char: Parameters.Character.class}.
  Context {unicodeProp: Parameters.Property.class Parameters.Character}.

(*|
## Bounded repetitions
|*)

  Section BoundedRepetitions.
    Lemma bounded_util_fwd m n delta r:
      def_groups r = [] -> (* r{m}r{n,n+k} ≅[forward] r{m+n,m+n+k}, generalized from regexp_tree *)
      (Sequence (Quantified true m 0 r) (Quantified true n delta r))
        ≅[forward] Quantified true (m + n) delta r.
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
        { apply seq_equiv_dir.
          apply quantified_S_equiv_forward.
          auto.
          reflexivity. }
        etransitivity; cycle 1.
        { symmetry.
          eapply quantified_S_equiv_forward.
          auto. }
        etransitivity.
        { symmetry.
          eapply sequence_assoc_equiv. }
        eapply seq_equiv_dir.
        reflexivity.
        auto.
    Qed.

    Lemma bounded_util_bwd m n delta r:
      def_groups r = [] -> (* r{n,n+k}r{m} ≅[backward] r{m+n,m+n+k}, generalized from regexp_tree *)
      (Sequence (Quantified true n delta r) (Quantified true m 0 r))
        ≅[backward] Quantified true (m + n) delta r.
    Proof.
      induction m as [ | m' IHm ]; simpl; intros.
      - etransitivity.
        apply seq_equiv_dir.
        reflexivity.
        apply quantified_zero_equiv.
        auto.
        etransitivity.
        apply sequence_epsilon_right_equiv.
        reflexivity.
      - etransitivity.
        { apply seq_equiv_dir.
          reflexivity.
          apply quantified_S_equiv_backward.
          auto. }
        etransitivity; cycle 1.
        { symmetry.
          eapply quantified_S_equiv_backward.
          auto. }
        etransitivity.
        { eapply sequence_assoc_equiv. }
        eapply seq_equiv_dir.
        auto.
        reflexivity.
    Qed.

    Lemma bounded_bounded_equiv m n r: (* r{m}r{n} ≅ r{m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true m 0 r) (Quantified true n 0 r))
        ≅ Quantified true (m + n) 0 r.
    Proof.
      intros H [].
      - apply bounded_util_fwd. auto.
      - rewrite PeanoNat.Nat.add_comm. apply bounded_util_bwd. auto.
    Qed.

    Lemma bounded_atmost_equiv m n r: (* r{m}r{0,n} ≅[forward] r{m,m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true m 0 r) (Quantified true 0 n r))
        ≅[forward] Quantified true m n r.
    Proof. intro NO_GROUPS. rewrite bounded_util_fwd, PeanoNat.Nat.add_0_r. 1: reflexivity. auto. Qed.

    Lemma atmost_bounded_equiv m n r: (* r{0,n}r{m} ≅[backward] r{m,m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true 0 n r) (Quantified true m 0 r))
        ≅[backward] Quantified true m n r.
    Proof. intro NO_GROUPS. rewrite bounded_util_bwd, PeanoNat.Nat.add_0_r. 1: reflexivity. auto. Qed.

    Lemma bounded_atmost_lazy_equiv m n r: (* r{m}r{0,n}? ≅[forward] r{m,m+n}? *)
      def_groups r = [] ->
      (Sequence (Quantified true m 0 r) (Quantified false 0 n r))
        ≅[forward] Quantified false m n r.
    Proof.
      intro NO_GROUPS.
      induction m as [|m IHm]; simpl.
      - etransitivity.
        apply seq_equiv_dir.
        apply quantified_zero_equiv.
        auto.
        reflexivity.
        apply sequence_epsilon_left_equiv.
      - etransitivity.
        { apply seq_equiv_dir.
          apply quantified_S_equiv_forward.
          auto.
          reflexivity. }
        etransitivity; cycle 1.
        { symmetry.
          eapply quantified_S_equiv_forward.
          auto. }
        etransitivity.
        { symmetry.
          eapply sequence_assoc_equiv. }
        eapply seq_equiv_dir.
        apply quantified_delta0_greedy_irrelevant.
        auto.
    Qed.

    Lemma atmost_bounded_lazy_equiv m n r: (* r{0,n}?r{m} ≅[backward] r{m,m+n}? *)
      def_groups r = [] ->
      (Sequence (Quantified false 0 n r) (Quantified true m 0 r))
        ≅[backward] Quantified false m n r.
    Proof.
      intro NO_GROUPS.
      induction m as [|m IHm]; simpl.
      - etransitivity.
        apply seq_equiv_dir.
        reflexivity.
        apply quantified_zero_equiv.
        auto.
        apply sequence_epsilon_right_equiv.
      - etransitivity.
        { apply seq_equiv_dir.
          reflexivity.
          apply quantified_S_equiv_backward.
          auto. }
        etransitivity; cycle 1.
        { symmetry.
          eapply quantified_S_equiv_backward.
          auto. }
        etransitivity.
        { eapply sequence_assoc_equiv. }
        eapply seq_equiv_dir.
        auto.
        apply quantified_delta0_greedy_irrelevant.
    Qed.

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

    Definition incl {A} (a b: list A) :=
      forall x, In x a -> In x b.

    Definition funct_incl {A B} (f1 f2: A -> list B -> Prop) :=
      forall a l1 l2, f1 a l1 -> f2 a l2 -> incl l1 l2.

    Lemma flatmap_incl {A B}:
      forall (leaves: list A) (f1 f2: A -> list B -> Prop) leaves1 leaves2,
        FlatMap leaves f1 leaves1 ->
        FlatMap leaves f2 leaves2 ->
        funct_incl f1 f2 ->
        incl leaves1 leaves2.
    Proof.
      intros leaves f1 f2 leaves1 leaves2 FM1 FM2 INCL.
      generalize dependent leaves2.
      induction FM1.
      - intros _ _ _ [].
      - specialize (IHFM1 INCL). intros leaves2 FM2 lf Hin.
        inversion FM2; subst.
        specialize (INCL _ _ _ HEAD HEAD0).
        apply in_app_or in Hin. destruct Hin.
        + apply in_or_app. left. auto.
        + apply in_or_app. right. unfold incl in IHFM1. auto.
    Qed.

    Lemma atmost_leaves_incl' (m d: nat) r:
      forall inp gm dir tm tn,
        is_tree [Areg (Quantified true 0 m r)] inp gm dir tm ->
        is_tree [Areg (Quantified true 0 (m+d) r)] inp gm dir tn ->
        incl (tree_leaves tm gm inp dir) (tree_leaves tn gm inp dir).
    Proof.
      induction m as [|m IHm].
      - intros inp gm dir tm tn TREE_m TREE_n.
        inversion TREE_m; subst. 2: { destruct plus; discriminate. }
        inversion SKIP; subst.
        inversion TREE_n; subst.
        + inversion SKIP0; subst. unfold incl. auto.
        + inversion SKIP0; subst. simpl.
          intros lf H. destruct H; try solve[inversion H]. subst lf.
          apply in_or_app. right. left. reflexivity.
      - intros inp gm dir tm tn TREE_m TREE_n.
        inversion TREE_m; subst.
        simpl in TREE_n.
        inversion TREE_n; subst. clear TREE_m TREE_n.
        assert (plus = m). { destruct plus; try discriminate. injection H1 as ->. reflexivity. }
        assert (plus0 = m + d). { destruct plus0; try discriminate. injection H2 as ->. reflexivity. }
        subst plus plus0. clear H1 H2.
        inversion SKIP; subst. inversion SKIP0; subst.
        simpl.
        assert (TREErcheck: exists trcheck, is_tree [Areg r; Acheck inp] inp (GroupMap.reset (def_groups r) gm) dir trcheck). {
          eexists. eapply compute_tr_is_tree.
        }
        destruct TREErcheck as [trcheck TREErcheck].
        pose proof leaves_concat _ _ _ [Areg r; Acheck inp] _ _ _ ISTREE1 TREErcheck as CONCAT.
        pose proof leaves_concat _ _ _ [Areg r; Acheck inp] _ _ _ ISTREE0 TREErcheck as CONCAT0.
        intros lf Hin.
        apply in_app_or in Hin. destruct Hin.
        + apply in_or_app. left. eapply (flatmap_incl _ _ _ _ _ CONCAT CONCAT0); eauto.
          unfold funct_incl. intros a l1 l2 ACT1 ACT2.
          inversion ACT1; subst. inversion ACT2; subst. apply IHm; auto.
        + apply in_or_app. auto. 
    Qed.

    Corollary atmost_leaves_incl (m n: nat) r:
      m <= n ->
      forall inp gm dir tm tn,
        is_tree [Areg (Quantified true 0 m r)] inp gm dir tm ->
        is_tree [Areg (Quantified true 0 n r)] inp gm dir tn ->
        incl (tree_leaves tm gm inp dir) (tree_leaves tn gm inp dir).
    Proof.
      intros. apply atmost_leaves_incl' with (m := m) (d := n-m) (r := r) (tm := tm); auto.
      replace (m + (n - m)) with n by lia. auto.
    Qed.

    Lemma leaves_equiv_incl:
      forall a b c d e: list leaf,
        leaves_equiv [] a b -> leaves_equiv [] d e ->
        incl c b ->
        leaves_equiv [] (a ++ c ++ d) (b ++ e).
    Proof.
    Admitted.

    Lemma atmost_atmost_equiv (m n: nat) r: (* r{0,m}r{0,n} ≅ r{0,m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true 0 m r) (Quantified true 0 n r))
        ≅ Quantified true 0 (m + n) r.
    Proof.
      intros NO_GROUPS [].
      {
        induction m as [|m IHm].
        - etransitivity.
          apply seq_equiv.
          apply quantified_zero_equiv.
          auto.
          reflexivity.
          apply sequence_epsilon_left_equiv.
        - split. 1: { simpl. rewrite NO_GROUPS. reflexivity. }
          intros i gm tr1 tr2 TREE1 TREE2. simpl in TREE2.
          inversion TREE1; subst. rewrite app_nil_r in CONT. inversion TREE2; subst. inversion SKIP; subst.
          simpl. clear TREE1 TREE2.
          simpl in CONT.
          inversion CONT; subst. clear CONT. simpl.
          assert (plus = m + n). { destruct plus; try discriminate. injection H1 as ->. reflexivity. }
          assert (plus0 = m). { destruct plus0; try discriminate. injection H2 as ->. reflexivity. }
          subst plus plus0. clear H1 H2.
          unfold tree_equiv_tr_dir. simpl.
          inversion SKIP0; subst; simpl.
          + inversion SKIP1; subst. simpl. apply leaves_equiv_app. 2: reflexivity.
            clear SKIP SKIP0 SKIP1.
            remember i as i' in ISTREE1 at 1, ISTREE0 at 1. clear Heqi'.
            remember (GroupMap.reset (def_groups r) gm) as gm'. clear gm Heqgm'.
            revert i gm' titer0 titer ISTREE0 ISTREE1.
            apply app_eq_left with (acts := [Areg r; Acheck i']).
            destruct IHm as [_ IHm].
            unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
            apply IHm; auto.
            apply tree_sequence. rewrite app_nil_r. simpl. auto.
          + inversion SKIP1; subst. simpl.
            clear SKIP SKIP0 SKIP1.
            destruct n as [|n]. 1: { destruct plus; discriminate. }
            assert (plus = n). { destruct plus; try discriminate. now injection H1 as ->. }
            subst plus. clear H1.
            assert (INCL: incl (tree_leaves titer1 (GroupMap.reset (def_groups r) gm) i
              forward) (tree_leaves titer (GroupMap.reset (def_groups r) gm) i
              forward)). {
              assert (TREErcheck: exists trcheck, is_tree [Areg r; Acheck i] i (GroupMap.reset (def_groups r) gm) forward trcheck)
                by (eexists; eapply compute_tr_is_tree).
              destruct TREErcheck as [trcheck TREErcheck].
              pose proof leaves_concat _ _ _ [Areg r; Acheck i] [Areg (Quantified true 0 n r)] _ _ ISTREE2 TREErcheck as CONCAT2.
              pose proof leaves_concat _ _ _ [Areg r; Acheck i] [Areg (Quantified true 0 (m + S n) r)] _ _ ISTREE1 TREErcheck as CONCAT1.
              eapply (flatmap_incl _ _ _ _ _ CONCAT2 CONCAT1); eauto.
              unfold funct_incl. intros a l1 l2 ACT1 ACT2.
              inversion ACT1; subst. inversion ACT2; subst.
              apply atmost_leaves_incl with (m := n) (n := m + S n) (r := r); eauto. lia.
            }
            assert (EQUIV: leaves_equiv [] (tree_leaves titer0 (GroupMap.reset (def_groups r) gm) i
              forward) (tree_leaves titer (GroupMap.reset (def_groups r) gm) i forward)). {
              clear INCL ISTREE2 titer1.
              remember (GroupMap.reset (def_groups r) gm) as gm'. clear gm Heqgm'.
              remember i as i' in ISTREE1 at 1, ISTREE0 at 1. clear Heqi'.
              revert i gm' titer0 titer ISTREE0 ISTREE1.
              apply app_eq_left with (acts := [Areg r; Acheck i']).
              unfold actions_equiv_dir. intros. apply IHm; auto.
              apply tree_sequence. rewrite app_nil_r. auto.
            }
            apply leaves_equiv_incl; auto. reflexivity.
      }
      {
        induction n as [|n IHn].
        - etransitivity.
          apply seq_equiv.
          reflexivity.
          apply quantified_zero_equiv.
          auto.
          rewrite PeanoNat.Nat.add_0_r.
          apply sequence_epsilon_right_equiv.
        - split. 1: { simpl. rewrite NO_GROUPS. reflexivity. }
          intros i gm tr1 tr2 TREE1 TREE2.
          inversion TREE1; subst. rewrite app_nil_r in CONT. inversion TREE2; subst. 1: lia. inversion SKIP; subst.
          simpl. clear TREE1 TREE2.
          simpl in CONT.
          inversion CONT; subst. clear CONT. simpl.
          assert (plus = m + n). { destruct plus; try discriminate. injection H1 as H1. f_equal. 2: lia. intros ->. reflexivity. }
          assert (plus0 = n). { destruct plus0; try discriminate. injection H2 as ->. reflexivity. }
          subst plus plus0. clear H1 H2.
          unfold tree_equiv_tr_dir. simpl.
          inversion SKIP0; subst; simpl.
          + inversion SKIP1; subst. simpl. apply leaves_equiv_app. 2: reflexivity.
            clear SKIP SKIP0 SKIP1.
            remember i as i' in ISTREE1 at 1, ISTREE0 at 1. clear Heqi'.
            remember (GroupMap.reset (def_groups r) gm) as gm'. clear gm Heqgm'.
            revert i gm' titer0 titer ISTREE0 ISTREE1.
            apply app_eq_left with (acts := [Areg r; Acheck i']).
            destruct IHn as [_ IHn].
            unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
            apply IHn; auto.
            apply tree_sequence. rewrite app_nil_r. simpl. auto.
          + inversion SKIP1; subst. simpl.
            clear SKIP SKIP0 SKIP1.
            destruct m as [|m]. 1: { destruct plus; discriminate. }
            assert (plus = m). { destruct plus; try discriminate. now injection H1 as ->. }
            subst plus. clear H1.
            assert (INCL: incl (tree_leaves titer1 (GroupMap.reset (def_groups r) gm) i
              backward) (tree_leaves titer (GroupMap.reset (def_groups r) gm) i
              backward)). {
              assert (TREErcheck: exists trcheck, is_tree [Areg r; Acheck i] i (GroupMap.reset (def_groups r) gm) backward trcheck)
                by (eexists; eapply compute_tr_is_tree).
              destruct TREErcheck as [trcheck TREErcheck].
              pose proof leaves_concat _ _ _ [Areg r; Acheck i] [Areg (Quantified true 0 m r)] _ _ ISTREE2 TREErcheck as CONCAT2.
              pose proof leaves_concat _ _ _ [Areg r; Acheck i] [Areg (Quantified true 0 (S m + n) r)] _ _ ISTREE1 TREErcheck as CONCAT1.
              eapply (flatmap_incl _ _ _ _ _ CONCAT2 CONCAT1); eauto.
              unfold funct_incl. intros a l1 l2 ACT1 ACT2.
              inversion ACT1; subst. inversion ACT2; subst.
              apply atmost_leaves_incl with (m := m) (n := S m + n) (r := r); eauto. lia.
            }
            assert (EQUIV: leaves_equiv [] (tree_leaves titer0 (GroupMap.reset (def_groups r) gm) i
              backward) (tree_leaves titer (GroupMap.reset (def_groups r) gm) i backward)). {
              clear INCL ISTREE2 titer1.
              remember (GroupMap.reset (def_groups r) gm) as gm'. clear gm Heqgm'.
              remember i as i' in ISTREE1 at 1, ISTREE0 at 1. clear Heqi'.
              revert i gm' titer0 titer ISTREE0 ISTREE1.
              apply app_eq_left with (acts := [Areg r; Acheck i']).
              unfold actions_equiv_dir. intros. apply IHn; auto.
              apply tree_sequence. rewrite app_nil_r. auto.
            }
            apply leaves_equiv_incl; auto. reflexivity.
      }
    Qed.

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
      all: lia || reflexivity.
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
