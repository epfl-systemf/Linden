(** * Custom tactics *)

(* A tactic that, when given a hypothesis H: P -> Q, asks to prove P in one branch (running tactic tac first) and specializes H with the proven property in the other branch. *)
Ltac specialize_prove_impl H tac :=
  lazymatch type of H with
  | ?A -> ?B =>
      let Hint := fresh in
      assert A as Hint; [tac|specialize (H Hint); clear Hint]
  end.

Tactic Notation "specialize_prove" constr(H) := specialize_prove_impl H idtac.
Tactic Notation "specialize_prove" constr(H) "by" tactic1(tac) := specialize_prove_impl H tac.
