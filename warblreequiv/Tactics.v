Ltac specialize_prove_impl H tac :=
  lazymatch type of H with
  | ?A -> ?B =>
      let Hint := fresh in
      assert A as Hint; [tac|specialize (H Hint); clear Hint]
  end.

Tactic Notation "specialize_prove" constr(H) := specialize_prove_impl H idtac.
Tactic Notation "specialize_prove" constr(H) "by" tactic1(tac) := specialize_prove_impl H tac.

(*Goal (1+1=2->True) -> True.
Proof.
  intro H.
  specialize_prove H by (simpl; reflexivity).
Abort.*)
