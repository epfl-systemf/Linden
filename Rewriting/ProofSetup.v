From Coq Require Export List.
From Warblre Require Export Base.
From Linden Require Export Regex Chars Groups Tree Semantics FunctionalSemantics FunctionalUtils ComputeIsTree.
From Linden.Rewriting Require Export Equivalence.

Export ListNotations.

#[export]
Hint Unfold
  tree_equiv
  tree_equiv_dir
  tree_equiv_tr_dir
  tree_equiv_compute
  tree_equiv_compute_dir
  tree_equiv_counterexample
  tree_nequiv
  tree_nequiv_dir
  tree_nequiv_tr_dir
  tree_nequiv_compute
  tree_nequiv_compute_dir
  tree_nequiv_counterexample
  : tree_equiv.
