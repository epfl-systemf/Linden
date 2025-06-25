From Linden.Rewriting Require Import ProofSetup.

Module Right.
  Section EquivalenceProof.
    Context {char: Parameters.Character.class}.
    Context {unicodeProp: Parameters.Property.class Parameters.Character}.

    Context (x0 x1 y: regex).
    Context (NO_GROUPS_IN_Y: def_groups y = []).

    Definition factored: regex :=
      Sequence (Disjunction x0 x1) y.

    Definition expanded: regex :=
      Disjunction (Sequence x0 y) (Sequence x1 y).

    Hint Rewrite NO_GROUPS_IN_Y : tree_equiv.

    Theorem factored_expanded_right_equiv: (* Proof using inversion on the is_tree predicate *)
      factored ≅[forward] expanded.
    Proof.
      tree_equiv_inv; eauto using compute_tr_is_tree.
      reflexivity.
    Qed.

    Theorem factored_expanded_right_equiv_symb: (* Proof using symbolic evaluation *)
      factored ≅[forward] expanded.
    Proof.
      tree_equiv_rw.
      compute_tr_simpl.
      reflexivity.
    Qed.
  End EquivalenceProof.
End Right.

Module LeftBackward.
  Section EquivalenceProof.
    Context {char: Parameters.Character.class}.
    Context {unicodeProp: Parameters.Property.class Parameters.Character}.

    Context (x y0 y1: regex).
    Context (NO_GROUPS_IN_X: def_groups x = []).

    Definition factored: regex :=
      Sequence x (Disjunction y0 y1).

    Definition expanded: regex :=
      Disjunction (Sequence x y0) (Sequence x y1).

    Hint Rewrite NO_GROUPS_IN_X : tree_equiv.

    Theorem factored_expanded_left_equiv: (* Proof using inversion on the is_tree predicate *)
      factored ≅[backward] expanded.
    Proof.
      tree_equiv_inv; eauto using compute_tr_is_tree.
      reflexivity.
    Qed.

    Theorem factored_expanded_left_equiv_symb: (* Proof using symbolic evaluation *)
      factored ≅[backward] expanded.
    Proof.
      tree_equiv_rw.
      compute_tr_simpl.
      reflexivity.
    Qed.
  End EquivalenceProof.
End LeftBackward.

Module LeftForward.
  Section Counterexample.
    Context {char: Parameters.Character.class}.
    Context {unicodeProp: Parameters.Property.class Parameters.Character}.
    Context (c: Parameters.Character).

    Let capture n := Group n (Character (CdSingle c)).

    Definition x := Disjunction (capture 1) Epsilon.
    Definition y0 := capture 2.
    Definition y1 := Epsilon.

    Definition factored: regex :=
      Sequence x (Disjunction y0 y1).

    Definition expanded: regex :=
      Disjunction (Sequence x y0) (Sequence x y1).

    Definition input := init_input [c].

    Theorem factored_expanded_left_nequiv:
      factored ≇ expanded.
    Proof.
      tree_equiv_rw.
      exists forward, input, GroupMap.empty.
      compute_tr_cbv.
      inversion 1.
    Qed.
  End Counterexample.
End LeftForward.
