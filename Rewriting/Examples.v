From Linden Require Import ProofSetup.

Section Utilities.
  Context {char: Parameters.Character.class}.
  Context {unicodeProp: Parameters.Property.class Parameters.Character}.

  Lemma sequence_assoc_equiv r0 r1 r2:
    Sequence r0 (Sequence r1 r2) ≅ Sequence (Sequence r0 r1) r2.
  Proof.
    (* autounfold with tree_equiv; destruct dir; tree_equiv_inv. *)
    tree_equiv_rw; destruct dir; compute_tr_simpl.
  Admitted.

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

  Lemma seq_equiv: forall x x' y y', x ≅ x' -> y ≅ y' -> Sequence x y ≅ Sequence x' y'.
  Admitted.
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
    Quantified true 0 (NoI.N 0) r ≅ Epsilon.
  Proof.
    tree_equiv_rw; compute_tr_simpl.
    reflexivity.
  Qed.

  Lemma quantified_S_equiv n:
    forall delta r,
      def_groups r = [] ->
      (Quantified true (S n) delta r)
        ≅ (Sequence (Quantified true 1 (NoI.N 0) r) (Quantified true n delta r)).
  Proof.
    induction n; intros.
    - (*tree_equiv_inv.*)
      all: admit.
    -
      tree_equiv_rw. destruct dir; compute_tr_simpl.
      all: admit.
      (* autounfold with tree_equiv; intros * Hf He. *)
      (* erewrite is_tree_determ with (1 := Hf). *)
      (* erewrite is_tree_determ with (1 := He). *)
      (* 2, 3: repeat (econstructor; simpl; rewrite ?app_nil_r; unfold seq_list); *)
      (* eapply compute_tr_is_tree. *)
  Admitted.
End Examples.
