From Linden Require Import ProofSetup.

Section Utilities.
  Context {char: Parameters.Character.class}.
  Context {unicodeProp: Parameters.Property.class Parameters.Character}.

  Lemma sequence_assoc_equiv r0 r1 r2:
    Sequence r0 (Sequence r1 r2) ≅ Sequence (Sequence r0 r1) r2.
  Proof.
    (* autounfold with tree_equiv; destruct dir; tree_equiv_inv. *)
    (*tree_equiv_rw; destruct dir; compute_tr_simpl.*)
    unfold tree_equiv. intros [].
    - unfold tree_equiv_dir. split. 1: simpl; apply app_assoc.
      intros i gm tr1 tr2 TREE1 TREE2. inversion TREE1; subst. inversion TREE2; subst. simpl in *.
      clear TREE1 TREE2.
      inversion CONT0; subst. simpl in CONT1.
      clear CONT0. revert i gm tr1 tr2 CONT CONT1.
      change (actions_equiv_dir [Areg r0; Areg (Sequence r1 r2)] [Areg r0; Areg r1; Areg r2] forward).
      apply app_eq_left with (acts := [Areg r0]).
      unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. simpl in CONT. replace t2 with t1 by (eapply is_tree_determ; eauto). reflexivity.
    - unfold tree_equiv_dir. split. 1: simpl; apply app_assoc.
      intros i gm tr1 tr2 TREE1 TREE2. inversion TREE1; subst. inversion TREE2; subst. simpl in *.
      clear TREE1 TREE2.
      inversion CONT; subst. simpl in CONT1.
      clear CONT. revert i gm tr1 tr2 CONT1 CONT0.
      change (actions_equiv_dir [Areg r2; Areg r1; Areg r0] [Areg r2; Areg (Sequence r0 r1)] backward).
      apply app_eq_left with (acts := [Areg r2]).
      unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE2; subst. simpl in CONT. replace t2 with t1 by (eapply is_tree_determ; eauto). reflexivity.
  Qed.

  Hint Constructors is_tree: is_tree.
  Lemma is_tree_skip_epsilon_r a i gm dir tr:
    is_tree a i gm dir tr ->
    is_tree (a ++ [Areg Epsilon]) i gm dir tr.
  Proof.
    induction 1; subst; simpl; eauto with is_tree.
    - rewrite <- app_assoc in IHis_tree; eauto with is_tree.
    - destruct greedy, plus; simpl.
      all: try change (NoI.N (S n)) with (NoI.N 1 + NoI.N n)%NoI.
      all: try change (NoI.Inf) with (NoI.N 1 + NoI.Inf)%NoI.
      all: eauto with is_tree.
  Qed.

  Lemma seq_equiv_dir: forall x x' y y' dir, x ≅[dir] x' -> y ≅[dir] y' -> Sequence x y ≅[dir] Sequence x' y'.
  Proof.
    intros x x' y y' [] EQUIV_x EQUIV_y.
    - destruct EQUIV_x as [DEF_GROUPS_x EQUIV_x]. destruct EQUIV_y as [DEF_GROUPS_y EQUIV_y].
      split. 1: { simpl. rewrite <- DEF_GROUPS_x, DEF_GROUPS_y. reflexivity. }
      intros i gm tr1 tr2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst. simpl in *. clear TREE1 TREE2.
      revert i gm tr1 tr2 CONT CONT0.
      change (actions_equiv_dir [Areg x; Areg y] [Areg x'; Areg y'] forward).
      change (actions_equiv_dir [Areg x] [Areg x'] forward) in EQUIV_x.
      change (actions_equiv_dir [Areg y] [Areg y'] forward) in EQUIV_y.
      apply app_eq_both with (a1 := [Areg x]) (a2 := [Areg x']) (b1 := [Areg y]) (b2 := [Areg y']) (dir := forward); auto.
    - destruct EQUIV_x as [DEF_GROUPS_x EQUIV_x]. destruct EQUIV_y as [DEF_GROUPS_y EQUIV_y].
      split. 1: { simpl. rewrite <- DEF_GROUPS_x, DEF_GROUPS_y. reflexivity. }
      intros i gm tr1 tr2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst. simpl in *. clear TREE1 TREE2.
      revert i gm tr1 tr2 CONT CONT0.
      change (actions_equiv_dir [Areg y; Areg x] [Areg y'; Areg x'] backward).
      change (actions_equiv_dir [Areg x] [Areg x'] backward) in EQUIV_x.
      change (actions_equiv_dir [Areg y] [Areg y'] backward) in EQUIV_y.
      apply app_eq_both with (a1 := [Areg y]) (a2 := [Areg y']) (b1 := [Areg x]) (b2 := [Areg x']); auto.
  Qed.

  Corollary seq_equiv:
    forall x x' y y', x ≅ x' -> y ≅ y' -> Sequence x y ≅ Sequence x' y'.
  Proof.
    intros x x' y y' EQUIV_x EQUIV_y []; auto using seq_equiv_dir.
  Qed.
End Utilities.

Section Examples.
  Context {char: Parameters.Character.class}.
  Context {unicodeProp: Parameters.Property.class Parameters.Character}.

  Lemma sequence_epsilon_left_equiv r:
    Sequence Epsilon r ≅ r.
  Proof.
    red; destruct dir; tree_equiv_inv.
    all: try apply (is_tree_skip_epsilon_r [Areg r]); eauto using compute_tr_is_tree.
    all: reflexivity.
  Qed.

  Lemma sequence_epsilon_right_equiv r:
    Sequence r Epsilon ≅ r.
  Proof.
    red; destruct dir; tree_equiv_inv.
    all: try apply (is_tree_skip_epsilon_r [Areg r]); eauto using compute_tr_is_tree.
    all: reflexivity.
  Qed.

  Lemma quantified_zero_equiv r:
    def_groups r = [] ->
    forall greedy, Quantified greedy 0 (NoI.N 0) r ≅ Epsilon.
  Proof.
    tree_equiv_rw; compute_tr_simpl.
    reflexivity.
  Qed.

  Lemma quantified_S_equiv_forward n:
    forall delta r greedy,
      def_groups r = [] ->
      (Quantified greedy (S n) delta r)
        ≅[forward] (Sequence (Quantified greedy 1 (NoI.N 0) r) (Quantified greedy n delta r)).
  Proof.
    split. 1: { simpl. rewrite H. reflexivity. }
    intros i gm tr1 tr2 TREE1 TREE2.
    inversion TREE1; subst. inversion TREE2; subst. simpl in CONT. inversion CONT; subst.
    clear TREE1 TREE2 CONT.
    unfold tree_equiv_tr_dir. simpl.
    remember (GroupMap.reset (def_groups r) gm) as gm'.
    clear gm Heqgm'.
    revert i gm' titer titer0 ISTREE1 ISTREE0.
    change (actions_equiv_dir [Areg r; Areg (Quantified greedy n delta r)] [Areg r; Areg (Quantified greedy 0 (NoI.N 0) r); Areg (Quantified greedy n delta r)] forward).
    apply app_eq_left with (acts := [Areg r]).
    unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE2; subst.
    2: { destruct plus; discriminate. }
    replace t2 with t1 by eauto using is_tree_determ. reflexivity.
  Qed.

  Lemma quantified_S_equiv_backward n:
    forall delta r greedy,
      def_groups r = [] ->
      (Quantified greedy (S n) delta r)
        ≅[backward] (Sequence (Quantified greedy n delta r) (Quantified greedy 1 (NoI.N 0) r)).
  Proof.
    split. 1: { simpl. rewrite H. reflexivity. }
    intros i gm tr1 tr2 TREE1 TREE2.
    inversion TREE1; subst. inversion TREE2; subst. simpl in CONT. inversion CONT; subst.
    clear TREE1 TREE2 CONT.
    unfold tree_equiv_tr_dir. simpl.
    remember (GroupMap.reset (def_groups r) gm) as gm'.
    clear gm Heqgm'.
    revert i gm' titer titer0 ISTREE1 ISTREE0.
    change (actions_equiv_dir [Areg r; Areg (Quantified greedy n delta r)] [Areg r; Areg (Quantified greedy 0 (NoI.N 0) r); Areg (Quantified greedy n delta r)] backward).
    apply app_eq_left with (acts := [Areg r]).
    unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE2; subst.
    2: { destruct plus; discriminate. }
    replace t2 with t1 by eauto using is_tree_determ. reflexivity.
  Qed.

  Lemma quantified_delta0_greedy_irrelevant r:
    forall n,
      Quantified true n 0 r ≅ Quantified false n 0 r.
  Proof.
    induction n as [|n IHn].
    - tree_equiv_rw; compute_tr_simpl. reflexivity.
    - intro dir. specialize (IHn dir).
      split. 1: reflexivity.
      intros i gm tr1 tr2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst. clear TREE1 TREE2.
      unfold tree_equiv_tr_dir. simpl.
      remember (GroupMap.reset _ gm) as gm'. clear gm Heqgm'.
      revert i gm' titer titer0 ISTREE1 ISTREE0.
      change (actions_equiv_dir [Areg r; Areg (Quantified true n 0 r)] [Areg r; Areg (Quantified false n 0 r)] dir).
      apply app_eq_left with (acts := [Areg r]).
      unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
      apply IHn; auto.
  Qed.
End Examples.
