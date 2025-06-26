From Linden.Rewriting Require Import ProofSetup.

(** * Proving Associativity of disjunction and concatenation  *)


Section DisjAssoc.
    Context {char: Parameters.Character.class}.
    Context {unicodeProp: Parameters.Property.class Parameters.Character}.

    Theorem disj_assoc:
      forall r1 r2 r3,
        Disjunction r1 (Disjunction r2 r3) ≅ Disjunction (Disjunction r1 r2) r3.
    Proof.
      unfold tree_equiv, tree_equiv_dir, tree_equiv_tr_dir. intros r1 r2 r3 dir. split; intros.
      { simpl. rewrite app_assoc. auto. }
      inversion H; inversion H0. inversion ISTREE2; inversion ISTREE0; subst.
      eapply is_tree_determ in ISTREE1, ISTREE4, ISTREE3; eauto. subst.
      simpl. rewrite app_assoc. apply leaves_equiv_rel_Reflexive.
    Qed.

End DisjAssoc.

Section SeqAssoc.
    Context {char: Parameters.Character.class}.
    Context {unicodeProp: Parameters.Property.class Parameters.Character}.

    Theorem seq_assoc_actions_fwd:
      forall r1 r2 r3,
        actions_equiv_dir [Areg r1; Areg (Sequence r2 r3)] [Areg r1; Areg r2; Areg r3] forward.
    Proof.
      intros r1 r2 r3. rewrite app_cons. rewrite app_cons with (l:=[Areg r2; Areg r3]). apply app_eq_left.
      unfold actions_equiv_dir. intros. inversion TREE1; subst. simpl in CONT.
      eapply is_tree_determ in TREE2; eauto. subst. apply leaves_equiv_rel_Reflexive.
    Qed.

    Theorem seq_assoc_actions_bwd:
      forall r1 r2 r3,
        actions_equiv_dir [Areg r3; Areg r2; Areg r1] [Areg r3; Areg (Sequence r1 r2)] backward.
    Proof.
      intros r1 r2 r3. rewrite app_cons. rewrite app_cons with (l:=[Areg (Sequence r1 r2)]). apply app_eq_left.
      unfold actions_equiv_dir. intros. inversion TREE2; subst. simpl in CONT.
      eapply is_tree_determ in TREE1; eauto. subst. apply leaves_equiv_rel_Reflexive.
    Qed.
    
    Theorem seq_assoc:
      forall r1 r2 r3,
        Sequence r1 (Sequence r2 r3) ≅ Sequence (Sequence r1 r2) r3.
    Proof.
      unfold tree_equiv, tree_equiv_dir, tree_equiv_tr_dir. intros r1 r2 r3 dir. split; intros.
      { simpl. rewrite app_assoc. auto. }
      destruct dir.
      - inversion H; inversion H0. inversion CONT0; subst. simpl in *.
        pose proof (seq_assoc_actions_fwd r1 r2 r3). auto.
      - inversion H; inversion H0. inversion CONT; subst. simpl in *.
        pose proof (seq_assoc_actions_bwd r1 r2 r3). auto.
    Qed.

End SeqAssoc.
