(** * Forced quantifier greediness *)
(* r{n} is equivalent to r{n}? *)

From Linden.Rewriting Require Import ProofSetup.
From Linden Require Import Equivalence.


Section ForcedQuant.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (* TODO: I'm not sure this is how we should proceed. *)
  (* Or if this is, we are lacking better lemmas to relate actions_equiv_dir to tree_equiv *)

  Theorem forced_actions:
    forall r n dir,
      actions_equiv_dir rer dir [Areg (Quantified true n (NoI.N 0) r)] [Areg (Quantified false n (NoI.N 0) r)].
  Proof.
    intros r n dir.
    induction n.
    - unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst; try solve[destruct plus; inversion H1].
      inversion TREE2; subst; try solve[destruct plus; inversion H1].
      eapply is_tree_determ in SKIP; eauto. subst. apply leaves_equiv_rel_Reflexive.
    - unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; inversion TREE2; subst.
      apply app_eq_left with (acts:=[Areg r]) in IHn.
      unfold actions_equiv_dir in IHn. simpl in IHn.
      specialize (IHn _ _ _ _ ISTREE1 ISTREE0). auto.
  Qed.

  Theorem forced_equiv:
    forall r n,
      (Quantified true n (NoI.N 0) r) ≅[rer] (Quantified false n (NoI.N 0) r).
  Proof.
    unfold tree_equiv, tree_equiv_dir. intros. split; auto. apply forced_actions.
  Qed.

End ForcedQuant.
