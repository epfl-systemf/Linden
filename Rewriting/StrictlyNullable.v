(** * Correctness of the STrictly Nullable Optimization *)
(* replacing r* with epsilon when r can only match the empty string *)

From Linden.Rewriting Require Import ProofSetup.
From Linden Require Import ExampleRegexes FailRegex.

Section StrictlyNullable.
  Context {params: LindenParameters}.

  (* TODO Adapt after fixing FailRegex *)

  (* The following function is a static under-approximation  of when is a regex striclty nullable. *)
  (* this definition is adapted from the warblre definition *)

Fixpoint strictly_nullable (r:regex) : bool :=
  match r with
  | Epsilon | Lookaround _ _ | Anchor _ => true
  | Character _ | Backreference _ => false
  | Disjunction r1 r2 | Sequence r1 r2 => andb (strictly_nullable r1) (strictly_nullable r2)
  | Quantified _ _ _ r1 | Group _ r1 => strictly_nullable r1
  end.

  Definition strictly_nullable_prop (r: regex): Prop :=
    forall inp gm dir t, is_tree [Areg r] inp gm dir t ->
      Forall (fun lf => fst lf = inp) (tree_leaves t gm inp dir).
  
  Lemma strictly_nullable_leaves_no_adv_quant_0:
    forall r, strictly_nullable_prop r ->
      forall greedy delta, strictly_nullable_prop (Quantified greedy 0 delta r).
  Proof.
    intros r SN greedy delta. unfold strictly_nullable_prop in *.
    intros inp gm dir t TREE.
    inversion TREE; subst.
    - (* No repetition *)
      inversion SKIP; subst. simpl. auto.
    - (* At least one repetition, but the checks will never pass *)
      inversion SKIP; subst.
      assert (ITER_LEAVES: Forall (fun lf => fst lf = inp) (tree_leaves (GroupAction (Reset (def_groups r)) titer) gm inp dir)). {
        simpl.
        assert (TREEr: exists tr, is_tree [Areg r] inp (GroupMap.reset (def_groups r) gm) dir tr). { eexists; eapply compute_tr_is_tree. }
        destruct TREEr as [tr TREEr].
        pose proof leaves_concat _ _ _ [Areg r] [Acheck inp; Areg (Quantified greedy 0 plus r)] _ _ ISTREE1 TREEr as CONCAT.
        apply SN in TREEr.
        remember (act_from_leaf _ dir) as f.
        induction CONCAT; subst f; auto.
        apply Forall_app; split.
        - inversion HEAD; subst. inversion TREE0; subst; simpl; auto.
          inversion TREEr; subst. exfalso. apply (StrictSuffix.ss_neq _ _ _ PROGRESS eq_refl).
        - apply IHCONCAT; auto. now inversion TREEr.
      }
      destruct greedy; simpl.
      + apply Forall_app; split; auto.
      + constructor; auto.
  Qed.

  Lemma strictly_nullable_leaves_no_adv_quant:
    forall r, strictly_nullable_prop r ->
      forall greedy min delta, strictly_nullable_prop (Quantified greedy min delta r).
  Proof.
    intros r SN greedy min delta. induction min.
    - apply strictly_nullable_leaves_no_adv_quant_0; auto.
    - unfold strictly_nullable_prop. intros inp gm dir t TREE.
      inversion TREE; subst.
      assert (exists tr, is_tree [Areg r] inp (GroupMap.reset (def_groups r) gm) dir tr). { eexists. eapply compute_tr_is_tree. }
      destruct H as [tr TREEr].
      pose proof leaves_concat _ _ _ [Areg r] [Areg (Quantified greedy min delta r)] _ _ ISTREE1 TREEr as CONCAT.
      apply SN in TREEr.
      remember (act_from_leaf _ dir) as f. simpl. induction CONCAT; auto.
      subst f. apply Forall_app; split.
      + inversion HEAD; subst. unfold strictly_nullable_prop in IHmin.
        inversion TREEr; subst. apply IHmin. auto.
      + apply IHCONCAT; auto. now inversion TREEr.
  Qed.


  Lemma strictly_nullable_leaves_no_adv:
    forall r, strictly_nullable r = true ->
      strictly_nullable_prop r.
  Proof.
    intros r SN. unfold strictly_nullable_prop. induction r; simpl in *; try discriminate.
    - (* Epsilon *)
      intros inp gm dir t TREE. inversion TREE; subst. inversion ISTREE; subst.
      simpl. constructor; constructor.
    - (* Disjunction *)
      apply Bool.andb_true_iff in SN. destruct SN as [SN1 SN2].
      intros inp gm dir t TREE. inversion TREE; subst.
      simpl. apply IHr1 in ISTREE1; auto. apply IHr2 in ISTREE2; auto.
      apply Forall_app; auto.
    - (* Sequence *)
      apply Bool.andb_true_iff in SN. destruct SN as [SN1 SN2].
      intros inp gm dir t TREE. inversion TREE; subst.
      rewrite app_nil_r in CONT. destruct dir; simpl in *.
      + (* Forward *)
        assert (exists t1, is_tree [Areg r1] inp gm forward t1). { exists (compute_tr [Areg r1] inp gm forward). apply compute_tr_is_tree. }
        destruct H as [t1 TREE1].
        pose proof leaves_concat _ _ _ [Areg r1] [Areg r2] _ _ CONT TREE1 as CONCAT.
        apply IHr1 in TREE1; auto.
        remember (tree_leaves t1 gm inp forward) as l1. clear Heql1.
        remember (act_from_leaf [Areg r2] forward) as f. induction CONCAT.
        1: constructor.
        subst f.
        apply Forall_app; split.
        * inversion HEAD; subst. inversion TREE1; subst. apply IHr2; auto.
        * apply IHCONCAT; auto. now inversion TREE1.
      + (* Backward; more or less the same, just swap 1 and 2 *)
        assert (exists t2, is_tree [Areg r2] inp gm backward t2). { exists (compute_tr [Areg r2] inp gm backward). apply compute_tr_is_tree. }
        destruct H as [t2 TREE2].
        pose proof leaves_concat _ _ _ [Areg r2] [Areg r1] _ _ CONT TREE2 as CONCAT.
        apply IHr2 in TREE2; auto.
        remember (tree_leaves t2 gm inp backward) as l2. clear Heql2.
        remember (act_from_leaf [Areg r1] backward) as f. induction CONCAT.
        1: constructor.
        subst f.
        apply Forall_app; split.
        * inversion HEAD; subst. inversion TREE2; subst. apply IHr1; auto.
        * apply IHCONCAT; auto. now inversion TREE2.
    - (* Quantified *)
      apply strictly_nullable_leaves_no_adv_quant. exact (IHr SN).
    - (* Lookaround *)
      intros inp gm dir t TREE. clear IHr.
      inversion TREE; subst; simpl in *.
      + inversion TREECONT; subst; simpl.
        destruct positivity; destruct tree_leaves; auto. destruct l; auto.
      + auto.
    - (* Group *)
      intros inp gm dir t TREE. inversion TREE; subst.
      assert (exists tr, is_tree [Areg r] inp (GroupMap.open (idx inp) id gm) dir tr). {
        eexists. eapply compute_tr_is_tree.
      }
      destruct H as [tr TREEr].
      pose proof leaves_concat _ _ _ [Areg r] [Aclose id] _ _ TREECONT TREEr as CONCAT.
      apply IHr in TREEr; auto.
      remember (act_from_leaf [Aclose id] dir) as f. simpl.
      induction CONCAT; auto.
      subst f.
      apply Forall_app; split.
      + inversion TREEr; subst. inversion HEAD; subst. inversion TREE0; subst. inversion TREECONT0; subst.
        simpl. auto.
      + apply IHCONCAT; auto. now inversion TREEr.
    - (* Anchor *)
      intros inp gm dir t TREE.
      inversion TREE; subst; simpl; auto.
      inversion TREECONT; subst; simpl; auto.
  Qed.

  Theorem strictly_nullable_correct:
    forall r, strictly_nullable r = true -> def_groups r = [] ->
         Quantified true 0 NoI.Inf r ≅ Epsilon.
  Proof.
    intros r SN NO_GROUPS. unfold tree_equiv.
    intro dir. unfold tree_equiv_dir.
    split. { auto. }
    intros i gm t1 t2 TREE1 TREE2.
    unfold tree_equiv_tr_dir. inversion TREE2; subst. inversion ISTREE; subst. simpl.
    clear ISTREE TREE2.
    inversion TREE1; subst. simpl.
    inversion SKIP; subst. simpl. clear SKIP.
    replace (tree_leaves _ _ _ _) with (nil (A := leaf)). 1: reflexivity.
    symmetry.
    assert (exists tr, is_tree [Areg r] i (GroupMap.reset (def_groups r) gm) dir tr). { eexists (compute_tr [Areg r] i _ dir). eapply compute_tr_is_tree. }
    destruct H as [tr TREEr].
    pose proof leaves_concat _ _ _ [Areg r] [Acheck i; Areg (Quantified true 0 plus r)] _ _ ISTREE1 TREEr as CONCAT.
    apply strictly_nullable_leaves_no_adv in TREEr; auto.
    remember (tree_leaves titer _ i dir) as leavesiter. remember (tree_leaves tr _ i dir) as leavesr.
    clear Heqleavesiter Heqleavesr.
    remember (act_from_leaf _ dir) as f.
    induction CONCAT. 1: reflexivity.
    subst f. replace lmapped with (nil (A := leaf)).
    2: { symmetry. apply IHCONCAT; auto. now inversion TREEr. }
    replace ly with (nil (A := leaf)).
    1: reflexivity.
    symmetry. inversion HEAD; subst. inversion TREE; subst.
    2: reflexivity.
    inversion TREEr; subst. exfalso. apply (StrictSuffix.ss_neq _ _ _ PROGRESS eq_refl).
  Qed.

  Section FailRegex.
    Fixpoint empty_groups (groups: list group_id): regex :=
      match groups with
      | [] => Epsilon
      | gid::q => Sequence (Group gid Epsilon) (empty_groups q)
      end.
    
    Lemma empty_groups_def_groups:
      forall groups,
        def_groups (empty_groups groups) = groups.
    Proof.
      induction groups. 1: reflexivity.
      simpl. f_equal. auto.
    Qed.

    Definition epsilon_fail (r: regex): regex :=
      Disjunction Epsilon (Sequence (empty_groups (def_groups r)) fail_regex).

    Lemma epsilon_fail_leaves_r:
      forall r inp gm dir t,
        is_tree [Areg (Sequence (empty_groups (def_groups r)) fail_regex)] inp gm dir t ->
        tree_leaves t gm inp dir = [].
    Proof.
      intros r inp gm dir t TREE.
      inversion TREE; subst. rewrite app_nil_r in CONT. destruct dir; simpl in *.
      - (* Forward *)
        assert (exists t', is_tree [Areg (empty_groups (def_groups r))] inp gm forward t') by
          (eexists; eapply compute_tr_is_tree).
        destruct H as [t' TREE'].
        pose proof leaves_concat _ _ _ [Areg (empty_groups (def_groups r))] [Areg fail_regex] _ _ CONT TREE' as CONCAT.
        remember (act_from_leaf _ forward) as f.
        induction CONCAT.
        + reflexivity.
        + subst f.
          rewrite IHCONCAT by reflexivity.
          inversion HEAD; subst. rewrite fail_regex_fail by auto. reflexivity.
      - (* Backward *)
        assert (exists t', is_tree [Areg fail_regex] inp gm backward t') by
          (eexists; eapply compute_tr_is_tree).
        destruct H as [t' TREE'].
        pose proof leaves_concat _ _ _ [Areg fail_regex] [Areg (empty_groups (def_groups r))] _ _ CONT TREE' as CONCAT.
        rewrite fail_regex_fail in CONCAT by auto.
        inversion CONCAT; reflexivity.
    Qed.

    Theorem strictly_nullable_correct':
      forall r, strictly_nullable r = true ->
          Quantified true 0 NoI.Inf r ≅ epsilon_fail r.
    Proof.
      intros r SN. unfold tree_equiv, epsilon_fail.
      intro dir. unfold tree_equiv_dir.
      split. { simpl. rewrite empty_groups_def_groups, app_nil_r. reflexivity. }
      intros i gm t1 t2 TREE1 TREE2.
      unfold tree_equiv_tr_dir. inversion TREE2; subst. inversion ISTREE1; subst.
      inversion ISTREE; subst. simpl.
      rewrite epsilon_fail_leaves_r with (r := r) (t := t3); auto.
      clear ISTREE ISTREE2 TREE2.
      inversion TREE1; subst. simpl.
      inversion SKIP; subst. simpl. clear SKIP.
      replace (tree_leaves _ _ _ _) with (nil (A := leaf)). 1: reflexivity.
      symmetry.
      assert (exists tr, is_tree [Areg r] i (GroupMap.reset (def_groups r) gm) dir tr). { eexists (compute_tr [Areg r] i _ dir). eapply compute_tr_is_tree. }
      destruct H as [tr TREEr].
      pose proof leaves_concat _ _ _ [Areg r] [Acheck i; Areg (Quantified true 0 plus r)] _ _ ISTREE0 TREEr as CONCAT.
      apply strictly_nullable_leaves_no_adv in TREEr; auto.
      remember (tree_leaves titer _ i dir) as leavesiter. remember (tree_leaves tr _ i dir) as leavesr.
      clear Heqleavesiter Heqleavesr.
      remember (act_from_leaf _ dir) as f.
      induction CONCAT. 1: reflexivity.
      subst f. replace lmapped with (nil (A := leaf)).
      2: { symmetry. apply IHCONCAT; auto. now inversion TREEr. }
      replace ly with (nil (A := leaf)).
      1: reflexivity.
      symmetry. inversion HEAD; subst. inversion TREE; subst.
      2: reflexivity.
      inversion TREEr; subst. exfalso. apply (StrictSuffix.ss_neq _ _ _ PROGRESS eq_refl).
    Qed.
  End FailRegex.
End StrictlyNullable.
