From Coq Require Import List.
From Warblre Require Import Base.
From Linden Require Import Regex Chars Groups Tree Semantics FunctionalSemantics.
Import ListNotations.

Section Utilities.
  Context {char: Parameters.Character.class}.

  Lemma compute_tree_is_tree {actions i gm dir f tr} :
    compute_tree actions i gm dir f = Some tr ->
    is_tree actions i gm dir tr.
  Admitted.

  Definition compute_tr (act: actions) (inp: input) (gm: group_map) (dir: Direction): tree :=
    match compute_tree act inp gm dir (S (actions_fuel act inp dir)) with
    | Some tr => tr
    | None => Mismatch
    end.

  Lemma compute_tr_is_tree {actions i gm dir} :
    is_tree actions i gm dir (compute_tr actions i gm dir).
  Proof.
    unfold compute_tr.
    pose proof functional_terminates actions i gm dir _ (PeanoNat.Nat.lt_succ_diag_r _).
    destruct compute_tree eqn:Htr; try contradiction.
    eauto using compute_tree_is_tree.
  Qed.

  Lemma compute_tr_ind {actions i gm dir P} :
    P (compute_tr actions i gm dir) ->
    forall {tr}, is_tree actions i gm dir tr -> P tr.
  Proof.
    intros HP tr Htr.
    erewrite is_tree_determ with (1 := Htr) (2 := compute_tr_is_tree).
    assumption.
  Qed.

  Definition compute_tr_dep (act: actions) (inp: input) (gm: group_map) (dir: Direction): tree :=
    let fuel := S (actions_fuel act inp dir) in
    let opt := compute_tree act inp gm dir fuel in
    match opt as o return opt = o -> tree with
    | Some tr =>
        fun _ => tr
    | None =>
        fun Heq => False_rect _ (functional_terminates act inp gm dir fuel (PeanoNat.Nat.lt_succ_diag_r _) Heq)
    end eq_refl.

  Lemma compute_tr_dep_is_tree {actions i gm dir} :
    is_tree actions i gm dir (compute_tr_dep actions i gm dir).
  Proof.
    unfold compute_tr_dep.
    set (functional_terminates _ _ _ _ _ _) as fn; clearbody fn.
    destruct compute_tree eqn:Htr; try contradiction.
    eauto using compute_tree_is_tree.
  Qed.
End Utilities.
