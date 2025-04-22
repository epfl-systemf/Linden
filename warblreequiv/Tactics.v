Ltac specialize_prove H :=
  lazymatch type of H with
  | ?A -> ?B =>
      let Hint := fresh in
      assert A as Hint; [|specialize (H Hint); clear Hint]
  end.
