From Coq Require Export Bool Arith List Equivalence Lia.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import Regex Chars Groups Tree Semantics
  FunctionalSemantics FunctionalUtils ComputeIsTree Parameters
  LWParameters LeavesEquivalence FlatMap.

Export ListNotations.

Section Definitions.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).


  (* Equivalence and non-equivalence definitions using is_tree *)
  Section IsTree.
    (** * Observational equivalence *)
    Definition observ_equiv (r1 r2: regex): Prop :=
      forall inp t1 t2
        (TREE1: is_tree rer [Areg r1] inp GroupMap.empty forward t1)
        (TREE2: is_tree rer [Areg r2] inp GroupMap.empty forward t2),
        first_leaf t1 inp = first_leaf t2 inp.


    (** * Equivalence and non-equivalence of trees *)

    (* Equivalence: when the lists of leaves of the trees are equivalent *)
    Definition tree_equiv_tr_dir i gm dir tr1 tr2 :=
      leaves_equiv [] (tree_leaves tr1 gm i dir) (tree_leaves tr2 gm i dir).

    (* Non-equivalence: when the first leaves are different *)
    Definition tree_nequiv_tr_dir i gm dir tr1 tr2 :=
      tree_res tr1 gm i dir <> tree_res tr2 gm i dir.


    (** * Actions equivalence *)

    (* When for all inputs, they have the same leaves in the same order (with possible duplicates) *)
    (* We first state equivalence for one given direction, e.g. rewritings involving sequences may only be valid in one direction *)
    Definition actions_equiv_dir (dir: Direction) (acts1 acts2: actions): Prop :=
      forall inp gm t1 t2
        (TREE1: is_tree rer acts1 inp gm dir t1)
        (TREE2: is_tree rer acts2 inp gm dir t2),
        tree_equiv_tr_dir inp gm dir t1 t2.
    
    Definition actions_equiv_dir_cond (dir: Direction) (P: leaf -> Prop) (acts1 acts2: actions): Prop :=
      forall lf, P lf ->
      forall t1 t2
        (TREE1: is_tree rer acts1 (fst lf) (snd lf) dir t1)
        (TREE2: is_tree rer acts2 (fst lf) (snd lf) dir t2),
        tree_equiv_tr_dir (fst lf) (snd lf) dir t1 t2.
    
    (* Stating for all directions *)
    Definition actions_equiv (acts1 acts2: actions): Prop :=
      forall dir, actions_equiv_dir dir acts1 acts2.


    (** * Regex equivalence *)

    (* Two regexes are equivalent when they define the same groups and
      yield equivalent lists of leaves when matched on the same input. *)
    Definition tree_equiv_dir dir r1 r2 :=
      def_groups r1 = def_groups r2 /\
      actions_equiv_dir dir [Areg r1] [Areg r2].
    
    (* Stating for all directions *)
    Definition tree_equiv r1 r2 :=
      forall dir, tree_equiv_dir dir r1 r2.

    (* Two regexes are non-equivalent when there exist an input and group map
       such that matching the regexes on the input and group map yield
       (observationally) different results. *)
    Definition tree_nequiv_dir dir r1 r2 :=
      exists i gm tr1 tr2,
        is_tree rer [Areg r1] i gm dir tr1 /\
        is_tree rer [Areg r2] i gm dir tr2 /\
        tree_nequiv_tr_dir i gm dir tr1 tr2.

    (* Stating for all directions *)
    Definition tree_nequiv r1 r2 :=
      exists dir, tree_nequiv_dir dir r1 r2.

  End IsTree.


  (** * Equivalence and non-equivalence definitions using compute_tr *)
  Section ComputeTree.
    Definition tree_equiv_compute_dir dir r1 r2 :=
      def_groups r1 = def_groups r2 /\
      forall i gm,
        tree_equiv_tr_dir
          i gm dir
          (compute_tr rer [Areg r1] i gm dir)
          (compute_tr rer [Areg r2] i gm dir).

    Definition tree_equiv_compute r1 r2 :=
      forall dir, tree_equiv_compute_dir dir r1 r2.

    Definition tree_nequiv_compute_dir dir r1 r2 :=
      exists i gm,
        tree_nequiv_tr_dir
          i gm dir
          (compute_tr rer [Areg r1] i gm dir)
          (compute_tr rer [Areg r2] i gm dir).

    Definition tree_nequiv_compute r1 r2 :=
      exists dir, tree_nequiv_compute_dir dir r1 r2.
  End ComputeTree.


  (** * Regex contexts *)
  Section Contexts.
    Inductive regex_ctx: Type :=
    | CHole

    | CDisjunctionL (r1 : regex) (c2 : regex_ctx)
    | CDisjunctionR (c1 : regex_ctx) (r2 : regex)

    | CSequenceL (r1 : regex) (c2 : regex_ctx)
    | CSequenceR (c1 : regex_ctx) (r2 : regex)

    | CQuantified (greedy: bool) (min: nat) (delta: non_neg_integer_or_inf) (c1 : regex_ctx)
    | CLookaround (lk : lookaround) (c1 : regex_ctx)
    | CGroup (gid : group_id) (c1 : regex_ctx)
    .


    Fixpoint plug_ctx (c : regex_ctx) (r : regex) : regex :=
      match c with
      | CHole => r
      | CDisjunctionL r1 c2 => Disjunction r1 (plug_ctx c2 r)
      | CDisjunctionR c1 r2 => Disjunction (plug_ctx c1 r) r2
      | CSequenceL r1 c2 => Sequence r1 (plug_ctx c2 r)
      | CSequenceR c1 r2 => Sequence (plug_ctx c1 r) r2
      | CQuantified greedy min delta c1 => Quantified greedy min delta (plug_ctx c1 r)
      | CLookaround lk c1 => Lookaround lk (plug_ctx c1 r)
      | CGroup gid c1 => Group gid (plug_ctx c1 r)
      end.

    (* Direction of contexts *)
    Inductive contextdir: Type := Forward | Backward | Same.

    Fixpoint ctx_dir (ctx: regex_ctx): contextdir :=
      match ctx with
      | CHole => Same
      | CDisjunctionL _ c | CDisjunctionR c _ | CSequenceL _ c | CSequenceR c _ => ctx_dir c
      | CQuantified _ _ _ c | CGroup _ c => ctx_dir c
      | CLookaround lk c =>
        let override_dir := match lk_dir lk with
        | forward => Forward
        | backward => Backward
        end in
        match ctx_dir c with
        | Same => override_dir
        | d => d
        end
      end.
  
  End Contexts.


  (* Lemmas relating the is_tree and compute_tr versions of the definitions. *)
  Section ComputeTreeIsTree.
    Lemma tree_equiv_compute_dir_iff {dir r1 r2} :
      tree_equiv_dir dir r1 r2 <-> tree_equiv_compute_dir dir r1 r2.
    Proof.
      unfold tree_equiv_dir, tree_equiv_compute_dir, actions_equiv_dir, tree_equiv_tr_dir; split.
      - intros [DEF_GROUPS EQUIV]. eauto 6 using compute_tr_is_tree.
      - intros [DEF_GROUPS Heq]; split; auto. intros * H1 H2.
        pattern t1; eapply compute_tr_ind with (2 := H1); eauto.
        pattern t2; eapply compute_tr_ind with (2 := H2); eauto.
    Qed.

    Lemma tree_equiv_compute_iff {r1 r2} :
      tree_equiv r1 r2 <-> tree_equiv_compute r1 r2.
    Proof.
      unfold tree_equiv, tree_equiv_compute; split; intros;
        apply tree_equiv_compute_dir_iff; eauto.
    Qed.

    Lemma tree_nequiv_compute_dir_iff r1 r2 dir :
      tree_nequiv_dir dir r1 r2 <-> tree_nequiv_compute_dir dir r1 r2.
    Proof.
      unfold tree_nequiv_dir, tree_nequiv_compute_dir, tree_nequiv_tr_dir.
      split.
      - intros (i & gm & tr1 & tr2 & Htr1 & Htr2 & Hneq).
        rewrite (is_tree_eq_compute_tr rer Htr1), (is_tree_eq_compute_tr rer Htr2) in Hneq.
        eauto.
      - intros (i & gm & Hneq).
        eauto 7 using compute_tr_is_tree.
    Qed.

    Lemma tree_nequiv_compute_iff {r1 r2} :
      tree_nequiv r1 r2 <-> tree_nequiv_compute r1 r2.
    Proof.
      unfold tree_nequiv, tree_nequiv_compute.
      pose proof tree_nequiv_compute_dir_iff r1 r2.
      split; intros (dir & Hneq); exists dir; specialize (H dir); intuition.
    Qed.
  End ComputeTreeIsTree.


End Definitions.


(** * Automation *)
#[export]
Hint Unfold
  tree_equiv
  tree_equiv_dir
  tree_equiv_tr_dir
  tree_equiv_compute
  tree_equiv_compute_dir
  actions_equiv
  actions_equiv_dir
  tree_nequiv
  tree_nequiv_dir
  tree_nequiv_tr_dir
  tree_nequiv_compute
  tree_nequiv_compute_dir
  : tree_equiv.

Hint Rewrite app_nil_l app_nil_r : tree_equiv.
Hint Rewrite <- app_assoc : tree_equiv.

Hint Unfold seq_list : tree_equiv_simpl.

Ltac tree_equiv_simpl :=
  repeat progress (
      autounfold with tree_equiv tree_equiv_simpl;
      autorewrite with tree_equiv;
      simpl; intros
    ).

Ltac tree_equiv_prepare :=
  tree_equiv_simpl;
  try (apply conj; [ try congruence | ]).

Ltac tree_equiv_rw :=
  try setoid_rewrite tree_equiv_compute_dir_iff;
  try setoid_rewrite tree_equiv_compute_iff;
  try setoid_rewrite tree_nequiv_compute_dir_iff;
  try setoid_rewrite tree_nequiv_compute_iff;
  tree_equiv_prepare; [ .. | intros ].

Ltac tree_inv H :=
  erewrite is_tree_determ with (1 := H);
  [ | repeat (econstructor; tree_equiv_simpl) ].

Ltac tree_equiv_inv :=
  tree_equiv_prepare;
  [ .. | intros * Hl Hr; tree_inv Hl; [ tree_inv Hr | .. ] ].

Hint Unfold
     compute_tr
     anchor_satisfied is_boundary is_input_boundary
     read_char word_char
     andb orb negb xorb
  : tree_equiv_symbex.

Hint Rewrite
  PeanoNat.Nat.leb_le
  PeanoNat.Nat.leb_nle
  : tree_equiv_symbex.

Ltac tree_equiv_symbex_step :=
  match goal with
  | _ => progress autorewrite with tree_equiv_symbex in *
  | _ => progress autounfold with tree_equiv_symbex
  | _ => progress simpl
  | [  |- context[match ?x with _ => _ end] ] =>
      lazymatch x with
      | context[match _ with _ => _ end] => fail
      | _ => destruct x eqn:?
      end
  end.

Ltac tree_equiv_symbex :=
  repeat tree_equiv_symbex_step.


Ltac leaves_equiv_step :=
  first [ apply equiv_nil
        | apply equiv_cons'
        | (apply equiv_seen_left + apply equiv_seen_right);
          [ apply is_seen_spec; unfold In; tauto | ] ].

Ltac leaves_equiv_t :=
  first [ reflexivity | repeat leaves_equiv_step ].

Hint Rewrite
  @CharSet.CharSetExt.exist_canonicalized_equiv
  @CharSet.CharSetExt.exist_spec
  @CharSet.CharSetExt.exist_false_iff
  @CharSet.CharSetExt.contains_spec
  @CharSet.CharSetExt.contains_false_iff
  @CharSet.CharSetExt.range_spec
  EqDec.inversion_false
  EqDec.inversion_true
  Bool.andb_true_iff
  Bool.andb_false_iff
  Bool.orb_true_iff
  Bool.orb_false_iff
  Bool.negb_true_iff
  Bool.negb_false_iff
  : charset.

Hint Unfold CharSet.CharSetExt.Exists
  : charset.

Hint Extern 1 => lia : lia.



(** * The tree and leaves equivalence relations are indeed equivalence relations. *)
Section Relation.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).


  Ltac eqv := repeat red; tree_equiv_rw; solve [congruence | intuition | firstorder].


  (* Tree equivalence *)
  Section TreeEquivTr.
    Context (i: input) (gm: group_map) (dir: Direction).

    Lemma tree_equiv_tr_dir_refl:
      Relation_Definitions.reflexive tree (tree_equiv_tr_dir i gm dir).
    Proof.
      unfold Relation_Definitions.reflexive, tree_equiv_tr_dir. reflexivity.
    Qed.

    Lemma tree_equiv_tr_dir_sym:
      Relation_Definitions.symmetric tree (tree_equiv_tr_dir i gm dir).
    Proof.
      unfold Relation_Definitions.symmetric, tree_equiv_tr_dir. intros x y H. symmetry. auto.
    Qed.

    Lemma tree_equiv_tr_dir_trans:
      Relation_Definitions.transitive tree (tree_equiv_tr_dir i gm dir).
    Proof.
      unfold Relation_Definitions.transitive, tree_equiv_tr_dir. intros x y z Hxy Hyz.
      etransitivity; eauto.
    Qed.

    #[global] Add Relation tree (tree_equiv_tr_dir i gm dir)
          reflexivity proved by tree_equiv_tr_dir_refl
          symmetry proved by tree_equiv_tr_dir_sym
          transitivity proved by tree_equiv_tr_dir_trans
          as tree_equiv_tr_dir_rel.
  End TreeEquivTr.


  (* Actions equivalence *)
  Section Actions.
    Section DirSpecific.
      Context (dir: Direction).

      Lemma actions_equiv_dir_refl:
        Relation_Definitions.reflexive actions (actions_equiv_dir rer dir).
      Proof.
        unfold Relation_Definitions.reflexive, actions_equiv_dir. intros. specialize (is_tree_determ rer _ _ _ _ _ _ TREE1 TREE2).
        intros <-. reflexivity.
      Qed.

      Lemma actions_equiv_dir_sym:
        Relation_Definitions.symmetric actions (actions_equiv_dir rer dir).
      Proof.
        unfold Relation_Definitions.symmetric, actions_equiv_dir. intros a1 a2 H inp gm t1 t2 TREE1 TREE2.
        symmetry; auto.
      Qed.

      Lemma actions_equiv_dir_trans:
        Relation_Definitions.transitive actions (actions_equiv_dir rer dir).
      Proof.
        unfold Relation_Definitions.transitive, actions_equiv_dir. intros a1 a2 a3 H H0 inp gm t1 t3 TREE1 TREE3.
        assert (exists t2, is_tree rer a2 inp gm dir t2).
        { exists (compute_tr rer a2 inp gm dir). apply compute_tr_is_tree. }
        (* otherwise any regex is equivalent to a regex without tree *)
        destruct H1 as [t2 TREE2].
        etransitivity; eauto.
      Qed.

      #[global] Add Relation actions (actions_equiv_dir rer dir)
          reflexivity proved by actions_equiv_dir_refl
          symmetry proved by actions_equiv_dir_sym
          transitivity proved by actions_equiv_dir_trans
          as actions_equiv_dir_rel.
    End DirSpecific.


    Lemma actions_equiv_refl:
      Relation_Definitions.reflexive actions (actions_equiv rer).
    Proof.
      unfold Relation_Definitions.reflexive, actions_equiv. intros acts dir. reflexivity.
    Qed.

    Lemma actions_equiv_sym:
      Relation_Definitions.symmetric actions (actions_equiv rer).
    Proof.
      unfold Relation_Definitions.symmetric, actions_equiv. intros a1 a2 H dir. symmetry. auto.
    Qed.

    Lemma actions_equiv_trans:
      Relation_Definitions.transitive actions (actions_equiv rer).
    Proof.
      unfold Relation_Definitions.transitive, actions_equiv. intros a1 a2 a3 H12 H23 dir. transitivity a2; auto.
    Qed.

    #[global] Add Relation actions (actions_equiv rer)
        reflexivity proved by actions_equiv_refl
        symmetry proved by actions_equiv_sym
        transitivity proved by actions_equiv_trans
        as actions_equiv_rel.
  
  End Actions.


  (* Regex equivalence *)

  Section DirSpecific.
    Context (dir: Direction).
      
    (* tree_equiv_dir *)
    Lemma tree_equiv_dir_reflexive:
      Relation_Definitions.reflexive regex (tree_equiv_dir rer dir).
    Proof.
      unfold Relation_Definitions.reflexive, tree_equiv_dir.
      intros x; split; auto. reflexivity.
    Qed.

    Lemma tree_equiv_dir_symmetric:
      Relation_Definitions.symmetric regex (tree_equiv_dir rer dir).
    Proof.
      unfold Relation_Definitions.symmetric, tree_equiv_dir.
      intros x y [DEF_GROUPS Hequiv]; split; try solve[congruence].
      symmetry. auto.
    Qed.

    Lemma tree_equiv_dir_transitive:
      Relation_Definitions.transitive regex (tree_equiv_dir rer dir).
    Proof.
      unfold Relation_Definitions.transitive, tree_equiv_dir.
      intros x y z [DEF_GROUPS12 H12] [DEF_GROUPS23 H23]; split; try solve[congruence].
      transitivity [Areg y]; auto.
    Qed.

    #[global] Add Relation regex (tree_equiv_dir rer dir)
        reflexivity proved by tree_equiv_dir_reflexive
        symmetry proved by tree_equiv_dir_symmetric
        transitivity proved by tree_equiv_dir_transitive
        as tree_equiv_dir_rel.


    (* tree_equiv_compute_dir *)
    Lemma tree_equiv_compute_dir_reflexive:
      Relation_Definitions.reflexive regex (tree_equiv_compute_dir rer dir).
    Proof.
      unfold Relation_Definitions.reflexive, tree_equiv_compute_dir.
      intros x; split; auto. reflexivity.
    Qed.

    Lemma tree_equiv_compute_dir_symmetric:
      Relation_Definitions.symmetric regex (tree_equiv_compute_dir rer dir).
    Proof.
      unfold Relation_Definitions.symmetric, tree_equiv_compute_dir, tree_equiv_tr_dir.
      intros x y [DEF_GROUPS Hequiv]; split; try solve[congruence].
      symmetry. auto.
    Qed.

    Lemma tree_equiv_compute_dir_transitive:
      Relation_Definitions.transitive regex (tree_equiv_compute_dir rer dir).
    Proof.
      unfold Relation_Definitions.transitive, tree_equiv_compute_dir, tree_equiv_tr_dir.
      intros x y z [DEF_GROUPSxy Hxy] [DEF_GROUPSyz Hyz]; split; try solve[congruence].
      intros i gm.
      etransitivity; eauto.
    Qed.

    #[global] Add Relation regex (tree_equiv_compute_dir rer dir)
        reflexivity proved by tree_equiv_compute_dir_reflexive
        symmetry proved by tree_equiv_compute_dir_symmetric
        transitivity proved by tree_equiv_compute_dir_transitive
        as tree_equiv_compute_dir_rel.
  End DirSpecific.


  (* tree_equiv *)
  Lemma tree_equiv_reflexive:
    Relation_Definitions.reflexive regex (tree_equiv rer).
  Proof.
    unfold Relation_Definitions.reflexive, tree_equiv.
    intros x dir. reflexivity.
  Qed.

  Lemma tree_equiv_symmetric:
    Relation_Definitions.symmetric regex (tree_equiv rer).
  Proof.
    unfold Relation_Definitions.symmetric, tree_equiv.
    intros x y H dir. symmetry. auto.
  Qed.

  Lemma tree_equiv_transitive:
    Relation_Definitions.transitive regex (tree_equiv rer).
  Proof.
    unfold Relation_Definitions.transitive, tree_equiv.
    intros x y z Hxy Hyz dir. transitivity y; auto.
  Qed.

  #[global] Add Relation regex (tree_equiv rer)
      reflexivity proved by tree_equiv_reflexive
      symmetry proved by tree_equiv_symmetric
      transitivity proved by tree_equiv_transitive
      as tree_equiv_rel.
      

  (* tree_equiv_compute *)
  Lemma tree_equiv_compute_reflexive:
    Relation_Definitions.reflexive regex (tree_equiv_compute rer).
  Proof.
    unfold Relation_Definitions.reflexive, tree_equiv_compute. reflexivity.
  Qed.

  Lemma tree_equiv_compute_symmetric:
    Relation_Definitions.symmetric regex (tree_equiv_compute rer).
  Proof.
    unfold Relation_Definitions.symmetric, tree_equiv_compute.
    intros x y Hxy dir. symmetry. auto.
  Qed.

  Lemma tree_equiv_compute_transitive:
    Relation_Definitions.transitive regex (tree_equiv_compute rer).
  Proof.
    unfold Relation_Definitions.transitive, tree_equiv_compute.
    intros x y z Hxy Hyz dir.
    transitivity y; auto.
  Qed.

  #[global] Add Relation regex (tree_equiv_compute rer)
      reflexivity proved by tree_equiv_compute_reflexive
      symmetry proved by tree_equiv_compute_symmetric
      transitivity proved by tree_equiv_compute_transitive
      as tree_equiv_compute_rel.

  (* Non-equivalence is irreflexive and symmetric *)
  Section Nequiv.
    Section DirSpecific.
      Context (dir: Direction).

      #[global] Instance tree_nequiv_dir_irrefl: Irreflexive (tree_nequiv_dir rer dir).
      Proof.
        unfold Irreflexive, Reflexive, complement, tree_nequiv_dir.
        tree_equiv_rw. destruct H as [i [gm H]]. apply H. auto.
      Qed.

      Lemma tree_nequiv_dir_sym:
        Relation_Definitions.symmetric regex (tree_nequiv_dir rer dir).
      Proof.
        unfold Relation_Definitions.symmetric, tree_nequiv_dir.
        tree_equiv_rw. destruct H as [i [gm H]]. exists i. exists gm.
        symmetry. auto.
      Qed.
      
      #[global] Add Relation regex (tree_nequiv_dir rer dir)
          symmetry proved by tree_nequiv_dir_sym
          as tree_nequiv_dir_rel.


      #[global] Instance tree_nequiv_compute_dir_irrefl : Irreflexive (tree_nequiv_compute_dir rer dir).
      Proof.
        unfold Irreflexive, Reflexive, complement, tree_nequiv_compute_dir.
        tree_equiv_rw. destruct H as [i [gm H]]. apply H. auto.
      Qed.

      Lemma tree_nequiv_compute_dir_sym:
        Relation_Definitions.symmetric regex (tree_nequiv_compute_dir rer dir).
      Proof.
        unfold Relation_Definitions.symmetric, tree_nequiv_compute_dir.
        tree_equiv_rw. destruct H as [i [gm H]].
        exists i. exists gm. symmetry. auto.
      Qed.

      #[global] Add Relation regex (tree_nequiv_compute_dir rer dir)
          symmetry proved by tree_nequiv_compute_dir_sym
          as tree_nequiv_compute_dir_rel.
    End DirSpecific.

    #[global] Instance tree_nequiv_irrefl: Irreflexive (tree_nequiv rer).
    Proof.
      unfold Irreflexive, Reflexive, complement, tree_nequiv.
      intros x [dir0 H].
      pose proof tree_nequiv_dir_irrefl. unfold Irreflexive, Reflexive, complement in H0.
      eauto.
    Qed.
    
    Lemma tree_nequiv_sym:
      Relation_Definitions.symmetric regex (tree_nequiv rer).
    Proof.
      unfold Relation_Definitions.symmetric, tree_nequiv. intros x y [dir H].
      exists dir. symmetry. auto.
    Qed.
      
    #[global] Add Relation regex (tree_nequiv rer)
        symmetry proved by tree_nequiv_sym
        as tree_nequiv_rel.

    #[global] Instance tree_nequiv_compute_irrefl: Irreflexive (tree_nequiv_compute rer).
    Proof.
      unfold Irreflexive, Reflexive, complement, tree_nequiv_compute.
      intros x [dir H].
      pose proof tree_nequiv_compute_dir_irrefl. unfold Irreflexive, Reflexive, complement in H0.
      eauto.
    Qed.

    Lemma tree_nequiv_compute_sym:
      Relation_Definitions.symmetric regex (tree_nequiv_compute rer).
    Proof.
      unfold Relation_Definitions.symmetric, tree_nequiv_compute.
      intros x y [dir H]. exists dir. symmetry. auto.
    Qed.

    #[global] Add Relation regex (tree_nequiv_compute rer)
        symmetry proved by tree_nequiv_compute_sym
         as tree_nequiv_compute_rel.
  End Nequiv.
End Relation.



Notation "r1 ≅[ rer ][ dir ] r2" := (tree_equiv_dir rer dir r1 r2) (at level 70, format "r1  ≅[ rer ][ dir ]  r2").
Notation "r1 ≅[ rer ] r2" := (tree_equiv rer r1 r2) (at level 70, format "r1  ≅[ rer ]  r2").
Notation "r1 ≇[ rer ][ dir ] r2" := (tree_nequiv_dir rer dir r1 r2) (at level 70, format "r1  ≇[ rer ][ dir ]  r2").
Notation "r1 ≇[ rer ] r2" := (tree_nequiv rer r1 r2) (at level 70, format "r1  ≇[ rer ]  r2").


Section Congruence.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (** * Observational Consequence on Backtracking Results  *)

  Theorem observe_equivalence:
    forall r1 r2
      (EQUIV: tree_equiv_dir rer forward r1 r2),
      observ_equiv rer r1 r2.
  Proof.
    intros r1 r2 EQUIV inp t1 t2 TREE1 TREE2.
    unfold tree_equiv_dir in EQUIV. destruct EQUIV as [_ EQUIV].
    specialize (EQUIV _ _ _ _ TREE1 TREE2).
    unfold first_leaf. rewrite first_tree_leaf. rewrite first_tree_leaf.
    apply equiv_head. auto.
  Qed.


  (* getting the leaves of a continuation applied to a particular leaf *)
  Inductive act_from_leaf : actions -> Direction -> leaf -> list leaf -> Prop :=
  | afl:
    forall act dir l t
      (TREE: is_tree rer act (fst l) (snd l) dir t),
      act_from_leaf act dir l (tree_leaves t (snd l) (fst l) dir).


  (* The two following lemmas should probably be moved somewhere else *)
  Lemma read_char_success_advance:
    forall cd inp dir c nextinp,
      read_char rer cd inp dir = Some (c, nextinp) ->
      advance_input inp dir = Some nextinp.
  Proof.
    intros. destruct inp as [next pref]. destruct dir; simpl in *.
    - (* Forward *)
      destruct next as [|h next']; try discriminate.
      destruct char_match; try discriminate. now injection H as <- <-.
    - (* Backward *)
      destruct pref as [|h pref']; try discriminate.
      destruct char_match; try discriminate. now injection H as <- <-.
  Qed.

  Lemma read_backref_success_advance:
    forall gm gid inp dir br_str nextinp,
      read_backref rer gm gid inp dir = Some (br_str, nextinp) ->
      nextinp = advance_input_n inp (length br_str) dir.
  Proof.
    intros gm gid inp dir br_str nextinp H.
    unfold read_backref in H. unfold advance_input_n.
    destruct GroupMap.find as [[startIdx [endIdx|]]|].
    - destruct inp as [next pref]. destruct dir.
      + (* Forward *)
        destruct Nat.leb eqn:Hinb; try discriminate.
        rewrite PeanoNat.Nat.leb_gt in Hinb.
        destruct EqDec.eqb eqn:Hsubeq; try discriminate.
        injection H as H <-.
        rewrite EqDec.inversion_true in Hsubeq.
        replace (length br_str) with (endIdx - startIdx). 1: reflexivity.
        rewrite <- H. apply (f_equal (length (A := Parameters.Character))) in Hsubeq.
        do 2 rewrite map_length in Hsubeq. rewrite firstn_length. lia.
      + (* Backward *)
        destruct Nat.leb eqn:Hinb; try discriminate.
        rewrite PeanoNat.Nat.leb_gt in Hinb.
        destruct EqDec.eqb eqn:Hsubeq; try discriminate.
        injection H as H <-.
        rewrite EqDec.inversion_true in Hsubeq.
        replace (length br_str) with (endIdx - startIdx). 1: reflexivity.
        rewrite <- H. apply (f_equal (length (A := Parameters.Character))) in Hsubeq.
        do 2 rewrite map_length in Hsubeq. rewrite rev_length, firstn_length. lia.
    - injection H as <- <-. simpl. now destruct inp, dir.
    - injection H as <- <-. simpl. now destruct inp, dir.
  Qed.

  (* adding new things to the continuation is the same as extending each leaf of the tree with these new things *)
  Theorem leaves_concat:
    forall inp gm dir act1 act2 tapp t1
      (TREE_APP: is_tree rer (act1 ++ act2) inp gm dir tapp)
      (TREE_1: is_tree rer act1 inp gm dir t1),
      FlatMap (tree_leaves t1 gm inp dir) (act_from_leaf act2 dir) (tree_leaves tapp gm inp dir).
  Proof.
    intros. generalize dependent tapp.
    induction TREE_1; intros; simpl in *.
    - (* Done *)
      rewrite <- app_nil_r. constructor; constructor. auto.
    
    - (* Check pass *)
      inversion TREE_APP; subst. 2: contradiction.
      simpl. apply IHTREE_1. auto.
    
    - (* Check fail *)
      inversion TREE_APP; subst. 1: contradiction.
      simpl. constructor.
    
    - (* Close *)
      inversion TREE_APP; subst. simpl.
      apply IHTREE_1. auto.
    
    - (* Epsilon *)
      inversion TREE_APP; subst. auto.

    - (* Read char success *)
      inversion TREE_APP; subst. 2: congruence.
      simpl.
      rewrite READ in READ0. injection READ0 as <- <-.
      rewrite advance_input_success with (nexti := nextinp).
      2: eauto using read_char_success_advance.
      auto.
    
    - (* Read char fail *)
      inversion TREE_APP; subst. 1: congruence.
      simpl. constructor.
    
    - (* Disjunction *)
      inversion TREE_APP; subst.
      simpl. apply FlatMap_app; auto.
    
    - (* Sequence *)
      inversion TREE_APP; subst.
      rewrite app_assoc in CONT. auto.
    
    - (* Forced quantifier *)
      inversion TREE_APP; subst. simpl.
      auto.
    
    - (* Done quantifier *)
      inversion TREE_APP; subst.
      2: { destruct plus; discriminate. }
      auto.
    
    - (* Free quantifier *)
      inversion TREE_APP; subst.
      1: { destruct plus; discriminate. }
      assert (plus0 = plus). {
        destruct plus0; destruct plus; try discriminate; try reflexivity.
        injection H1 as <-. auto.
      }
      subst plus0.
      unfold greedy_choice. destruct greedy.
      + (* Greedy *)
        simpl. apply FlatMap_app; auto.
      + (* Lazy *)
        simpl. apply FlatMap_app; auto.
      
    - (* Group *)
      inversion TREE_APP; subst. simpl.
      auto.
    
    - (* Lookaround success *)
      inversion TREE_APP; subst;
        assert (treelk0 = treelk) by (eapply is_tree_determ; eauto); subst.
      2: { rewrite RES_LK in FAIL_LK. inversion FAIL_LK. }
      rewrite RES_LK in RES_LK0. injection RES_LK0 as <-.
      destruct positivity eqn:Hpos.
      + unfold lk_result in RES_LK. rewrite Hpos in RES_LK.
        pose proof first_tree_leaf treelk gm inp (lk_dir lk) as LK_FIRST.
        destruct (tree_res treelk gm inp (lk_dir lk)) as [[inplk gmlk']|] eqn:TREERES_LK; try discriminate.
        injection RES_LK as ->.
        destruct (tree_leaves treelk gm inp (lk_dir lk)) as [|[inplk' gmlk'] q] eqn:TREELEAVES_LK; try discriminate.
        simpl in *. injection LK_FIRST as <- <-. rewrite Hpos.
        rewrite TREELEAVES_LK. auto.
      + unfold lk_result in RES_LK. rewrite Hpos in RES_LK.
        destruct (tree_res treelk gm inp (lk_dir lk)) eqn:TREERES; inversion RES_LK. subst.
        assert (tree_leaves treelk gmlk inp (lk_dir lk) = []).
        { apply leaves_group_map_indep with (gm1 := gmlk) (inp1 := inp) (dir1 := lk_dir lk).
          apply hd_error_none_nil. rewrite <- first_tree_leaf. auto. }
        simpl. rewrite Hpos, H. auto.
  
    - (* Lookaround failure *)
      inversion TREE_APP; subst;
        assert (treelk0 = treelk) by (eapply is_tree_determ; eauto); subst.
      { rewrite RES_LK in FAIL_LK. inversion FAIL_LK. }
      simpl. constructor.
    
    - (* Anchor *)
      inversion TREE_APP; subst.
      2: congruence.
      simpl. auto.
    
    - (* Anchor fail *)
      inversion TREE_APP; subst.
      1: congruence.
      simpl. constructor.
    
    - (* Backref *)
      inversion TREE_APP; subst.
      2: congruence.
      rewrite READ_BACKREF in READ_BACKREF0. injection READ_BACKREF0 as <- <-.
      simpl.
      replace (advance_input_n _ _ _) with nextinp.
      2: eauto using read_backref_success_advance.
      auto.
    
    - (* Backref fail *)
      inversion TREE_APP; subst.
      1: congruence.
      simpl. constructor.
  Qed.

  (* There are many ways to rephrase this if needed. *)
  (* We don't need the generic FlatMap: we could specialize it to X=Y=leaf, and to f=cont_from_leaf *)
  (* We could also use the functional flat_map, but this would require proving that there is a function that associates a tree to each regex and input *)
  (* I don't really like this solution, because I don't believe the proof relies on that property *)

  (** * Continuation Lemmas  *)

  (* building up to contextual equivalence *)
  (* to reason about the leaves of an app, we use the flatmap result *)



  Lemma act_from_leaf_determ: forall act dir, determ (act_from_leaf act dir).
  Proof.
    intros act dir x y1 y2 Hxy1 Hxy2.
    inversion Hxy1; subst. inversion Hxy2; subst.
    assert (t0 = t) by eauto using is_tree_determ. subst t0. reflexivity.
  Qed.


  Lemma app_eq_right:
    forall a1 a2 acts dir
      (ACTS_EQ: actions_equiv_dir rer dir a1 a2),
      actions_equiv_dir rer dir (a1 ++ acts) (a2 ++ acts).
  Proof.
    intros. unfold actions_equiv_dir in *.
    intros inp gm t1acts t2acts TREE1acts TREE2acts.
    assert (exists t1, is_tree rer a1 inp gm dir t1). {
      exists (compute_tr rer a1 inp gm dir). apply compute_tr_is_tree.
    }
    assert (exists t2, is_tree rer a2 inp gm dir t2). {
      exists (compute_tr rer a2 inp gm dir). apply compute_tr_is_tree.
    }
    destruct H as [t1 TREE1]. destruct H0 as [t2 TREE2].
    pose proof leaves_concat inp gm dir a1 acts t1acts t1 TREE1acts TREE1.
    pose proof leaves_concat inp gm dir a2 acts t2acts t2 TREE2acts TREE2.
    specialize (ACTS_EQ inp gm t1 t2 TREE1 TREE2).
    unfold tree_equiv_tr_dir.
    eauto using flatmap_leaves_equiv_l, act_from_leaf_determ.
  Qed.

  Definition equiv_leaffuncts (f g: leaf -> list leaf -> Prop): Prop :=
    forall lf yf yg,
      f lf yf -> g lf yg ->
      leaves_equiv [] yf yg.
    
  Lemma flatmap_leaves_equiv_r:
    forall leaves f g leavesf leavesg,
      determ f -> determ g -> equiv_leaffuncts f g ->
      FlatMap leaves f leavesf ->
      FlatMap leaves g leavesg ->
      leaves_equiv [] leavesf leavesg.
  Proof.
    intros leaves f g leavesf leavesg DETF DETG FGEQUIV FMF FMG.
    generalize dependent leavesg.
    induction FMF; intros; inversion FMG; subst.
    { apply leaves_equiv_refl. }
    apply leaves_equiv_app2.
    - eapply FGEQUIV; eauto.
    - rewrite app_nil_r. apply IHFMF in FM; auto.
      eapply leaves_equiv_monotony with (seen1:=[]); eauto.
      { intros x0 H. simpl in H. inversion H. }
  Qed.

  Definition equiv_leaffuncts_cond (f g: leaf -> list leaf -> Prop) (P: leaf -> Prop): Prop :=
    forall l, P l ->
      forall yf yg, f l yf -> g l yg -> leaves_equiv [] yf yg.
  
  Lemma flatmap_leaves_equiv_r_prop:
    forall l f g fl gl P,
      determ f -> determ g ->
      equiv_leaffuncts_cond f g P ->
      Forall P l ->
      FlatMap l f fl ->
      FlatMap l g gl ->
      leaves_equiv [] fl gl.
  Proof.
    intros l f g fl gl P DETF DETG EQFG PL FMF FMG.
    generalize dependent gl.
    induction FMF; intros; inversion FMG; subst.
    - reflexivity.
    - apply leaves_equiv_app2.
      + eapply EQFG; eauto. now inversion PL.
      + rewrite app_nil_r. apply IHFMF in FM; auto.
        * eapply leaves_equiv_monotony with (seen1 := []); eauto.
          intros x0 H. simpl in H. inversion H.
        * now inversion PL.
  Qed.

  
  Lemma app_eq_left:
    forall a1 a2 acts dir
      (ACTS_EQ: actions_equiv_dir rer dir a1 a2),
      actions_equiv_dir rer dir (acts ++ a1) (acts ++ a2).
  Proof.
    intros. unfold actions_equiv_dir in *.
    intros inp gm t1acts t2acts TREE1acts TREE2acts.
    assert (exists tacts, is_tree rer acts inp gm dir tacts). {
      exists (compute_tr rer acts inp gm dir). apply compute_tr_is_tree.
    }
    destruct H as [tacts TREEacts].
    pose proof leaves_concat inp gm dir acts a1 t1acts tacts TREE1acts TREEacts.
    pose proof leaves_concat inp gm dir acts a2 t2acts tacts TREE2acts TREEacts.
    eapply flatmap_leaves_equiv_r; eauto.
    1,2: apply act_from_leaf_determ.
    (* Now act_from_leaf a1 dir and act_from_leaf a2 dir are morally equivalent *)
    unfold equiv_leaffuncts. intros lf yf yg Hyf Hyg.
    inversion Hyf; subst. inversion Hyg; subst. apply ACTS_EQ; auto.
  Qed.
  
  Lemma app_eq_both:
    forall a1 a2 b1 b2 dir
      (A_EQ: actions_equiv_dir rer dir a1 a2)
      (B_EQ: actions_equiv_dir rer dir b1 b2),
      actions_equiv_dir rer dir (a1 ++ b1) (a2 ++ b2).
  Proof.
    intros. transitivity (a1++b2).
    - apply app_eq_left. auto.
    - apply app_eq_right. auto.
  Qed.

  Definition actions_respect_prop_dir (acts: actions) (dir: Direction) (P: leaf -> Prop): Prop :=
    forall inp gm t
      (TREE: is_tree rer acts inp gm dir t),
      Forall P (tree_leaves t gm inp dir).

  Lemma actions_equiv_interm_prop:
    forall (a1 a2 b1 b2: actions) (P: leaf -> Prop) (dir: Direction),
      actions_equiv_dir rer dir a1 a2 ->
      actions_respect_prop_dir a1 dir P ->
      actions_respect_prop_dir a2 dir P ->
      actions_equiv_dir_cond rer dir P b1 b2 ->
      actions_equiv_dir rer dir (a1 ++ b1) (a2 ++ b2).
  Proof.
    intros a1 a2 b1 b2 P dir EQUIV_a PROP1 PROP2 EQUIV_b.
    transitivity (a1 ++ b2).
    - unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
      assert (exists ta1, is_tree rer a1 inp gm dir ta1). { exists (compute_tr rer a1 inp gm dir). apply compute_tr_is_tree. }
      destruct H as [ta1 TREEa1].
      pose proof leaves_concat _ _ _ _ _ _ _ TREE1 TREEa1 as CONCAT1.
      pose proof leaves_concat _ _ _ _ _ _ _ TREE2 TREEa1 as CONCAT2.
      unshelve eapply (flatmap_leaves_equiv_r_prop _ _ _ _ _ P _ _ _ _ CONCAT1 CONCAT2); auto.
      1,2: apply act_from_leaf_determ.
      unfold equiv_leaffuncts_cond. intros. inversion H0; subst. inversion H1; subst.
      apply EQUIV_b; auto.
    - apply app_eq_right. auto.
  Qed.

  Lemma actions_respect_prop_add_left:
    forall (a b: actions) (P: leaf -> Prop) (dir: Direction),
      actions_respect_prop_dir b dir P ->
      actions_respect_prop_dir (a ++ b) dir P.
  Proof.
    intros a b P dir PROPb.
    unfold actions_respect_prop_dir. intros inp gm t TREE.
    assert (exists ta, is_tree rer a inp gm dir ta). {
      exists (compute_tr rer a inp gm dir). apply compute_tr_is_tree.
    }
    destruct H as [ta TREEa].
    pose proof leaves_concat _ _ _ _ _ _ _ TREE TREEa as CONCAT.
    unfold actions_respect_prop_dir in PROPb.
    remember (act_from_leaf b dir) as f.
    induction CONCAT. 1: constructor.
    apply Forall_app. split; auto. subst f.
    inversion HEAD; subst. apply PROPb. auto.
  Qed.

  Definition actions_no_leaves (a: actions) (dir: Direction): Prop :=
    forall inp gm t,
      is_tree rer a inp gm dir t ->
      tree_leaves t gm inp dir = [].

  Lemma actions_prop_False_no_leaves:
    forall (a: actions) (dir: Direction) (P: leaf -> Prop),
      actions_respect_prop_dir a dir P ->
      (forall lf, ~P lf) ->
      actions_no_leaves a dir.
  Proof.
    intros a dir P RESPECT PROP_FALSE.
    unfold actions_no_leaves. intros inp gm t TREE.
    unfold actions_respect_prop_dir in RESPECT. apply RESPECT in TREE.
    destruct tree_leaves; try reflexivity.
    inversion TREE; subst. exfalso. apply (PROP_FALSE l H1).
  Qed.

  Lemma actions_no_leaves_prop_False:
    forall (a: actions) (dir: Direction),
      actions_no_leaves a dir ->
      actions_respect_prop_dir a dir (fun _ => False).
  Proof.
    intros a dir NO_LEAVES.
    unfold actions_respect_prop_dir. unfold actions_no_leaves in NO_LEAVES.
    intros. rewrite NO_LEAVES; auto.
  Qed.

  Lemma actions_no_leaves_add_left:
    forall a b dir,
      actions_no_leaves b dir ->
      actions_no_leaves (a ++ b) dir.
  Proof.
    intros a b dir NO_LEAVES.
    apply actions_no_leaves_prop_False in NO_LEAVES.
    apply actions_respect_prop_add_left with (a := a) in NO_LEAVES.
    apply actions_prop_False_no_leaves with (P := fun _ => False); auto.
  Qed.

  Lemma actions_no_leaves_add_right:
    forall a b dir,
      actions_no_leaves a dir ->
      actions_no_leaves (a ++ b) dir.
  Proof.
    intros a b dir NO_LEAVES.
    unfold actions_no_leaves in *. intros inp gm t TREEab.
    assert (exists ta, is_tree rer a inp gm dir ta). {
      exists (compute_tr rer a inp gm dir). apply compute_tr_is_tree.
    }
    destruct H as [ta TREEa].
    pose proof leaves_concat _ _ _ _ _ _ _ TREEab TREEa as FLAT_MAP.
    rewrite NO_LEAVES in FLAT_MAP by assumption. inversion FLAT_MAP. reflexivity.
  Qed.


  (* Lemma for quantifiers *)
  Lemma check_actions_prop:
    forall inp dir,
      actions_respect_prop_dir [Acheck inp] dir
        (fun lf : input * group_map => StrictSuffix.strict_suffix (fst lf) inp dir).
  Proof.
    intros inp dir. unfold actions_respect_prop_dir.
    intros inp' gm t TREE. inversion TREE; subst; simpl.
    - inversion TREECONT; subst. simpl. constructor; auto.
    - constructor.
  Qed.

  Definition remaining_length (inp: input) (dir: Direction): nat :=
    let '(Input next pref) := inp in
    match dir with
    | forward => length next
    | backward => length pref
    end.

  Lemma regex_equiv_quant_forced:
    forall r1 r2 dir,
      tree_equiv_dir rer dir r1 r2 ->
      forall greedy delta,
        tree_equiv_dir rer dir (Quantified greedy 0 delta r1) (Quantified greedy 0 delta r2) ->
        forall min,
          tree_equiv_dir rer dir (Quantified greedy min delta r1) (Quantified greedy min delta r2).
  Proof.
    intros r1 r2 dir EQUIV greedy delta EQUIV_ZERO.
    destruct EQUIV_ZERO as [DEF_GROUPS EQUIV_ZERO]. simpl in DEF_GROUPS.
    induction min as [|min' IH]. 1: split; assumption.
    unfold tree_equiv_dir. split; try assumption. intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1; subst; inversion TREE2; subst.
    rewrite <- DEF_GROUPS in *.
    unfold tree_equiv_tr_dir. simpl.
    apply app_eq_both with (a1 := [Areg r1]) (a2 := [Areg r2]) (b1 := [Areg (Quantified greedy min' delta r1)]) (b2 := [Areg (Quantified greedy min' delta r2)]).
    - unfold actions_equiv_dir. unfold tree_equiv_dir in EQUIV.
      apply EQUIV.
    - unfold actions_equiv_dir. unfold tree_equiv_dir in IH.
      apply IH.
    - simpl. apply ISTREE1.
    - simpl. apply ISTREE0.
  Qed.

  Lemma regex_equiv_quant_done:
    forall r1 r2 dir greedy,
      def_groups r1 = def_groups r2 ->
      tree_equiv_dir rer dir (Quantified greedy 0 (NoI.N 0) r1) (Quantified greedy 0 (NoI.N 0) r2).
  Proof.
    intros. unfold tree_equiv_dir.
    split; auto. intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1; subst; inversion TREE2; subst.
    - inversion SKIP; subst; inversion SKIP0; subst. unfold tree_equiv_tr_dir. reflexivity.
    - destruct plus; discriminate.
    - destruct plus; discriminate.
    - destruct plus; discriminate.
  Qed.

  Lemma strict_suffix_remaining_length:
    forall inp' inp dir,
      StrictSuffix.strict_suffix inp' inp dir ->
      remaining_length inp' dir < remaining_length inp dir.
  Proof.
    intros [next1 pref1] [next2 pref2] [] STRICT_SUFFIX.
    - (* Forward *)
      apply StrictSuffix.ss_fwd_diff in STRICT_SUFFIX.
      destruct STRICT_SUFFIX as [diff [DIFF_NOTNIL [Heqnext2 Heqpref1]]]. simpl.
      rewrite Heqnext2, app_length.
      destruct diff; try contradiction. simpl. lia.
    - (* Backward *)
      apply StrictSuffix.ss_bwd_diff in STRICT_SUFFIX.
      destruct STRICT_SUFFIX as [diff [DIFF_NOTNIL [Heqnext1 Heqpref2]]]. simpl.
      rewrite Heqpref2, app_length, rev_length.
      destruct diff; try contradiction. simpl. lia.
  Qed.

  Lemma check_end_no_leaves:
    forall inp dir,
      remaining_length inp dir = 0 ->
      actions_no_leaves [Acheck inp] dir.
  Proof.
    intros inp dir END.
    apply actions_prop_False_no_leaves with (P := fun lf => StrictSuffix.strict_suffix (fst lf) inp dir).
    - apply check_actions_prop.
    - intros lf ABS. apply strict_suffix_remaining_length in ABS. lia.
  Qed.

  Lemma regex_quant_free_induction:
    forall n greedy plus r1 r2 dir,
      (forall (inp : input) (gm : group_map),
      remaining_length inp dir <= n ->
      forall (delta : non_neg_integer_or_inf) (t1 t2 : tree),
      is_tree rer [Areg (Quantified greedy 0 delta r1)] inp gm dir t1 ->
      is_tree rer [Areg (Quantified greedy 0 delta r2)] inp gm dir t2 ->
      tree_equiv_tr_dir inp gm dir t1 t2) ->
      forall inp,
        remaining_length inp dir <= S n ->
        actions_equiv_dir_cond rer dir
          (fun lf : input * group_map => StrictSuffix.strict_suffix (fst lf) inp dir)
          [Areg (Quantified greedy 0 plus r1)]
          [Areg (Quantified greedy 0 plus r2)].
  Proof.
    intros. unfold actions_equiv_dir_cond.
    intros [inp' gm'] STRICT_SUFFIX t1 t2 TREE1 TREE2. simpl in *.
    apply H with (delta := plus); auto.
    pose proof strict_suffix_remaining_length _ _ _ STRICT_SUFFIX. lia.
  Qed.

  Lemma regex_equiv_quant_free:
    forall r1 r2 dir,
      tree_equiv_dir rer dir r1 r2 ->
      forall greedy delta,
        tree_equiv_dir rer dir (Quantified greedy 0 delta r1) (Quantified greedy 0 delta r2).
  Proof.
    intros r1 r2 dir Hequiv greedy delta.
    destruct Hequiv as [DEF_GROUPS Hequiv].
    split; auto. intros inp gm t1 t2 TREE1. remember (remaining_length inp dir) as n.
    assert (remaining_length inp dir <= n) as Hle_n by lia. clear Heqn.
    revert inp gm Hle_n delta t1 t2 TREE1. induction n.
    - (* At end of input *)
      intros inp gm Hend delta t1 t2 TREE1 TREE2.
      inversion TREE1; subst; inversion TREE2; subst.
      + inversion SKIP; subst. inversion SKIP0; subst. unfold tree_equiv_tr_dir. reflexivity.
      + destruct plus; discriminate.
      + destruct plus; discriminate.
      + assert (plus = plus0). { destruct plus0; destruct plus; congruence. }
        subst plus0. clear H1.
        inversion SKIP; subst inp0 gm0 dir0 tskip. inversion SKIP0; subst inp0 gm0 dir0 tskip0.
        unfold tree_equiv_tr_dir.
        assert (NO_LEAVES: actions_no_leaves [Areg r1; Acheck inp; Areg (Quantified greedy 0 plus r1)] dir). {
          apply actions_no_leaves_add_left with (a := [Areg r1]).
          apply actions_no_leaves_add_right with (a := [Acheck inp]) (b := [Areg (Quantified greedy 0 plus r1)]).
          apply check_end_no_leaves. lia.
        }
        assert (NO_LEAVES0: actions_no_leaves [Areg r2; Acheck inp; Areg (Quantified greedy 0 plus r2)] dir). {
          apply actions_no_leaves_add_left with (a := [Areg r2]).
          apply actions_no_leaves_add_right with (a := [Acheck inp]) (b := [Areg (Quantified greedy 0 plus r2)]).
          apply check_end_no_leaves. lia.
        }
        unfold actions_no_leaves in NO_LEAVES, NO_LEAVES0.
        destruct greedy; simpl.
        * rewrite NO_LEAVES by auto. rewrite NO_LEAVES0 by auto. reflexivity.
        * rewrite NO_LEAVES by auto. rewrite NO_LEAVES0 by auto. reflexivity.
    - (* Not at the end of input *)
      intros inp gm Hremlength delta t1 t2 TREE1 TREE2.
      inversion TREE1; subst; inversion TREE2; subst.
      + inversion SKIP; inversion SKIP0. unfold tree_equiv_tr_dir. reflexivity.
      + destruct plus; discriminate.
      + destruct plus; discriminate.
      + assert (plus = plus0). { destruct plus0; destruct plus; congruence. }
        subst plus0. clear H1.
        inversion SKIP; subst inp0 gm0 dir0 tskip. inversion SKIP0; subst inp0 gm0 dir0 tskip0.
        unfold tree_equiv_tr_dir.
        rewrite <- DEF_GROUPS in *.
        destruct greedy; simpl.
        * (* Greedy *)
          apply leaves_equiv_app. 2: reflexivity.
          eapply actions_equiv_interm_prop with
            (a1 := [Areg r1; Acheck inp]) (a2 := [Areg r2; Acheck inp])
            (P := fun lf => StrictSuffix.strict_suffix (fst lf) inp dir).
          5: apply ISTREE1. 5: apply ISTREE0.
          -- apply app_eq_right with (a1 := [Areg r1]) (a2 := [Areg r2]) (acts := [Acheck inp]).
             unfold actions_equiv_dir. intros. apply Hequiv; auto.
          -- apply actions_respect_prop_add_left with (a := [Areg r1]) (b := [Acheck inp]).
             apply check_actions_prop.
          -- apply actions_respect_prop_add_left with (a := [Areg r2]) (b := [Acheck inp]).
             apply check_actions_prop.
          -- (* Apply IHn *)
             eauto using regex_quant_free_induction.
        * (* Lazy *)
          apply leaves_equiv_app with (p1 := [(inp, gm)]) (p2 := [(inp, gm)]). 1: reflexivity.
          (* Copy-pasting from greedy case... *)
          eapply actions_equiv_interm_prop with
            (a1 := [Areg r1; Acheck inp]) (a2 := [Areg r2; Acheck inp])
            (P := fun lf => StrictSuffix.strict_suffix (fst lf) inp dir).
          5: apply ISTREE1. 5: apply ISTREE0.
          -- apply app_eq_right with (a1 := [Areg r1]) (a2 := [Areg r2]) (acts := [Acheck inp]).
             unfold actions_equiv_dir. intros. apply Hequiv; auto.
          -- apply actions_respect_prop_add_left with (a := [Areg r1]) (b := [Acheck inp]).
             apply check_actions_prop.
          -- apply actions_respect_prop_add_left with (a := [Areg r2]) (b := [Acheck inp]).
             apply check_actions_prop.
          -- (* Apply IHn *)
             eauto using regex_quant_free_induction.
  Qed.

  Theorem regex_equiv_quant:
    forall r1 r2 dir,
      tree_equiv_dir rer dir r1 r2 ->
      forall greedy min delta,
        tree_equiv_dir rer dir (Quantified greedy min delta r1) (Quantified greedy min delta r2).
  Proof.
    intros r1 r2 dir EQUIV greedy min delta.
    destruct min.
    - apply regex_equiv_quant_free. auto.
    - auto using regex_equiv_quant_forced, regex_equiv_quant_free.
  Qed.

  Lemma ctx_dir_lookaround_not_Same:
    forall lk ctx, ctx_dir (CLookaround lk ctx) <> Same.
  Proof.
    intros lk ctx. destruct lk; simpl; destruct (ctx_dir ctx); discriminate.
  Qed.

  (** * Main theorems: regex equivalence is preserved by plugging into a context *)
  Theorem regex_equiv_ctx_samedir:
    forall r1 r2 dir,
      r1 ≅[rer][dir] r2 ->
      forall ctx,
        ctx_dir ctx = Same ->
        tree_equiv_dir rer dir (plug_ctx ctx r1) (plug_ctx ctx r2).
  Proof.
    intros r1 r2 dir Hequiv ctx Hctxdir.
    induction ctx.
    - (* Hole *) auto.
    - (* Disjunction left *)
      simpl in *. unfold tree_equiv_dir, actions_equiv_dir in *. specialize (IHctx Hctxdir).
      destruct IHctx as [IHgroups IHctx]. split.
      1: { simpl. f_equal. auto. }
      intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      unfold tree_equiv_tr_dir in *.
      simpl. apply leaves_equiv_app; auto.
      assert (t1 = t0) by (eapply is_tree_determ; eauto). subst t1. apply leaves_equiv_refl.
    
    - (* Disjunction right *)
      simpl in *. unfold tree_equiv_dir, actions_equiv_dir in *. specialize (IHctx Hctxdir).
      destruct IHctx as [IHgroups IHctx]. split.
      1: { simpl. f_equal. auto. }
      intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      unfold tree_equiv_tr_dir in *.
      simpl. apply leaves_equiv_app; auto.
      assert (t4 = t3) by (eapply is_tree_determ; eauto). subst t4. apply leaves_equiv_refl.

    - (* Sequence left *)
      simpl in *. unfold tree_equiv_dir in *. specialize (IHctx Hctxdir).
      destruct IHctx as [IHgroups IHctx]. split.
      1: { simpl. f_equal. auto. }
      intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      destruct dir.
      + (* Forward *)
        simpl in *. pose proof app_eq_left _ _ [Areg r0] forward IHctx.
        unfold actions_equiv_dir in H. simpl in H. unfold tree_equiv_tr_dir in *. auto.
      + (* Backward *)
        simpl in *. pose proof app_eq_right _ _ [Areg r0] backward IHctx.
        unfold actions_equiv_dir in H. simpl in H. unfold tree_equiv_tr_dir in *. auto.
      
    - (* Sequence right *)
      simpl in *. unfold tree_equiv_dir, actions_equiv_dir in *. specialize (IHctx Hctxdir).
      destruct IHctx as [IHgroups IHctx]. split.
      1: { simpl. f_equal. auto. }
      intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      destruct dir.
      + (* Forward *)
        simpl in *. pose proof app_eq_right _ _ [Areg r0] forward IHctx.
        unfold actions_equiv_dir in H. simpl in H. unfold tree_equiv_tr_dir in *. auto.
      + (* Backward *)
        simpl in *. pose proof app_eq_left _ _ [Areg r0] backward IHctx.
        unfold actions_equiv_dir in H. simpl in H. unfold tree_equiv_tr_dir in *. auto.
      
    - (* Quantified *)
      simpl in *. specialize (IHctx Hctxdir). apply regex_equiv_quant. auto.

    - (* Lookaround: direction of context is never Same *)
      exfalso. exact (ctx_dir_lookaround_not_Same _ _ Hctxdir).

    - (* Group *)
      simpl in *. unfold tree_equiv_dir, actions_equiv_dir in *. specialize (IHctx Hctxdir).
      destruct IHctx as [IHgroups IHctx]. split.
      1: { simpl. f_equal. auto. }
      intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      unfold tree_equiv_tr_dir in *. simpl.
      assert (TREE1': exists t1, is_tree rer [Areg (plug_ctx ctx r1)] inp (GroupMap.open (idx inp) gid gm) dir t1). {
        exists (compute_tr rer [Areg (plug_ctx ctx r1)] inp (GroupMap.open (idx inp) gid gm) dir). apply compute_tr_is_tree.
      }
      assert (TREE2': exists t2, is_tree rer [Areg (plug_ctx ctx r2)] inp (GroupMap.open (idx inp) gid gm) dir t2). {
        exists (compute_tr rer [Areg (plug_ctx ctx r2)] inp (GroupMap.open (idx inp) gid gm) dir). apply compute_tr_is_tree.
      }
      destruct TREE1' as [t1 TREE1']. destruct TREE2' as [t2 TREE2'].
      change [Areg ?A; Aclose gid] with ([Areg A] ++ [Aclose gid]) in TREECONT.
      change [Areg ?A; Aclose gid] with ([Areg A] ++ [Aclose gid]) in TREECONT0.
      pose proof leaves_concat _ _ _ _ _ _ _ TREECONT TREE1' as APP1.
      pose proof leaves_concat _ _ _ _ _ _ _ TREECONT0 TREE2' as APP2.
      eapply flatmap_leaves_equiv_l. 3: apply APP1. 3: apply APP2. 2: auto. apply act_from_leaf_determ.
  Qed.

  Lemma tree_leaves_nil_no_first_branch:
    forall t gm inp dir str,
      tree_leaves t gm inp dir = [] ->
      ~(exists res, first_branch t str = Some res).
  Proof.
    intros * LEAVES_NIL.
    intro ABS. destruct ABS as [res ABS].
    unfold first_branch in ABS.
    apply (f_equal (hd_error (A := leaf))) in LEAVES_NIL.
    rewrite <- first_tree_leaf in LEAVES_NIL. simpl in LEAVES_NIL.
    apply res_group_map_indep with (gm2 := GroupMap.empty) (inp2 := init_input str) (dir2 := forward) in LEAVES_NIL.
    congruence.
  Qed.

  Lemma tree_leaves_notnil_first_branch:
    forall t gm inp dir str,
      tree_leaves t gm inp dir <> [] ->
      exists res, first_branch t str = Some res.
  Proof.
    intros * LEAVES_NIL.
    destruct (first_branch t str) as [res|] eqn:FIRST_BRANCH.
    1: eexists; eauto.
    exfalso. destruct tree_leaves eqn:LEAVES; try contradiction.
    apply (f_equal (hd_error (A := leaf))) in LEAVES.
    rewrite <- first_tree_leaf in LEAVES. simpl in LEAVES.
    unfold first_branch in FIRST_BRANCH.
    apply res_group_map_indep with (gm2 := gm) (inp2 := inp) (dir2 := dir) in FIRST_BRANCH. congruence.
  Qed.

  Lemma regex_equiv_ctx_lookahead:
    forall r1 r2,
      tree_equiv_dir rer forward r1 r2 ->
      forall dir,
        tree_equiv_dir rer dir (Lookaround LookAhead r1) (Lookaround LookAhead r2).
  Proof.
    intros r1 r2 EQUIV dir. unfold tree_equiv_dir in *.
    destruct EQUIV as [DEF_GROUPS EQUIV]. split; auto.
    intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1; subst; inversion TREE2; subst.
    - (* Both lookaheads succeed *)
      specialize (EQUIV _ _ _ _ TREELK TREELK0) as EQUIV_LK.
      unfold lk_result in RES_LK, RES_LK0. simpl in *.
      unfold tree_equiv_tr_dir in *. simpl.
      rewrite first_tree_leaf in RES_LK, RES_LK0.
      inversion EQUIV_LK; subst; auto.
      + reflexivity.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + rewrite <- H1 in RES_LK. rewrite <- H2 in RES_LK0. simpl in *.
        injection RES_LK as ->. injection RES_LK0 as <-. inversion TREECONT; subst. inversion TREECONT0; subst.
        simpl. reflexivity.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      destruct (tree_res treelk gm inp forward) as [[inp1 res1]|] eqn:RES1; inversion RES_LK; subst.
      destruct (tree_res treelk0 gm inp forward) as [[inp2 res2]|] eqn:RES2; inversion FAIL_LK; subst.
      clear RES_LK FAIL_LK. rewrite first_tree_leaf in RES1, RES2.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + rewrite <- H1 in RES1. inversion RES1.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + rewrite <- H2 in RES2. inversion RES2.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      destruct (tree_res treelk gm inp forward) as [[inp1 res1]|] eqn:RES1; inversion FAIL_LK; subst.
      destruct (tree_res treelk0 gm inp forward) as [[inp2 res2]|] eqn:RES2; inversion RES_LK; subst.
      clear RES_LK FAIL_LK. rewrite first_tree_leaf in RES1, RES2.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + rewrite <- H2 in RES2. inversion RES2.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + rewrite <- H1 in RES1. inversion RES1.
    - (* Both lookaheads fail *)
      unfold tree_equiv_tr_dir. simpl. reflexivity.
  Qed.

  Lemma regex_equiv_ctx_lookbehind:
    forall r1 r2,
      tree_equiv_dir rer backward r1 r2 ->
      forall dir,
        tree_equiv_dir rer dir (Lookaround LookBehind r1) (Lookaround LookBehind r2).
  Proof. (* Almost exactly the same proof as above; LATER factorize? *)
    intros r1 r2 EQUIV dir. unfold tree_equiv_dir in *.
    destruct EQUIV as [DEF_GROUPS EQUIV]. split; auto.
    intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1; subst; inversion TREE2; subst.
    - (* Both lookaheads succeed *)
      specialize (EQUIV _ _ _ _ TREELK TREELK0) as EQUIV_LK.
      unfold lk_result in RES_LK, RES_LK0. simpl in *.
      unfold tree_equiv_tr_dir in *. simpl.
      rewrite first_tree_leaf in RES_LK, RES_LK0.
      inversion EQUIV_LK; subst; auto.
      + reflexivity.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + rewrite <- H1 in RES_LK. rewrite <- H2 in RES_LK0. simpl in *.
        injection RES_LK as ->. injection RES_LK0 as <-. inversion TREECONT; subst. inversion TREECONT0; subst.
        simpl. reflexivity.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      destruct (tree_res treelk gm inp backward) as [[inp1 res1]|] eqn:RES1; inversion RES_LK; subst.
      destruct (tree_res treelk0 gm inp backward) as [[inp2 res2]|] eqn:RES2; inversion FAIL_LK; subst.
      clear RES_LK FAIL_LK. rewrite first_tree_leaf in RES1, RES2.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + rewrite <- H1 in RES1. inversion RES1.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + rewrite <- H2 in RES2. inversion RES2.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      destruct (tree_res treelk gm inp backward) as [[inp1 res1]|] eqn:RES1; inversion FAIL_LK; subst.
      destruct (tree_res treelk0 gm inp backward) as [[inp2 res2]|] eqn:RES2; inversion RES_LK; subst.
      clear RES_LK FAIL_LK. rewrite first_tree_leaf in RES1, RES2.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + rewrite <- H2 in RES2. inversion RES2.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + rewrite <- H1 in RES1. inversion RES1.
    - (* Both lookaheads fail *)
      unfold tree_equiv_tr_dir. simpl. reflexivity.
  Qed.

  Lemma regex_equiv_ctx_neglookahead:
    forall r1 r2,
      tree_equiv_dir rer forward r1 r2 ->
      forall dir,
        tree_equiv_dir rer dir (Lookaround NegLookAhead r1) (Lookaround NegLookAhead r2).
  Proof.
    intros r1 r2 EQUIV dir. unfold tree_equiv_dir in *.
    destruct EQUIV as [DEF_GROUPS EQUIV]. split; auto.
    intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1; subst; inversion TREE2; subst.
    - (* Both lookaheads succeed *)
      unfold tree_equiv_tr_dir. simpl.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + inversion TREECONT; subst. inversion TREECONT0; subst. reflexivity.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + reflexivity.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      destruct (tree_res treelk gm inp forward) as [[inp1 res1]|] eqn:RES1; inversion RES_LK; subst.
      destruct (tree_res treelk0 gmlk inp forward) as [[inp2 res2]|] eqn:RES2; inversion FAIL_LK; subst.
      clear RES_LK FAIL_LK. rewrite first_tree_leaf in RES1, RES2.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + rewrite <- H2 in RES2. inversion RES2.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + rewrite <- H1 in RES1. inversion RES1.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      destruct (tree_res treelk gm inp forward) as [[inp1 res1]|] eqn:RES1; inversion FAIL_LK; subst.
      destruct (tree_res treelk0 gm inp forward) as [[inp2 res2]|] eqn:RES2; inversion RES_LK; subst.
      clear RES_LK FAIL_LK. rewrite first_tree_leaf in RES1, RES2.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + rewrite <- H1 in RES1. inversion RES1.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + rewrite <- H2 in RES2. inversion RES2.
    - (* Both lookaheads fail *)
      unfold tree_equiv_tr_dir. simpl. reflexivity.
  Qed.

  Lemma regex_equiv_ctx_neglookbehind:
    forall r1 r2,
      tree_equiv_dir rer backward r1 r2 ->
      forall dir,
        tree_equiv_dir rer dir (Lookaround NegLookBehind r1) (Lookaround NegLookBehind r2).
  Proof. (* Almost exactly the same proof as above *)
    intros r1 r2 EQUIV dir. unfold tree_equiv_dir in *.
    destruct EQUIV as [DEF_GROUPS EQUIV]. split; auto.
    intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1; subst; inversion TREE2; subst.
    - (* Both lookaheads succeed *)
      unfold tree_equiv_tr_dir. simpl.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + inversion TREECONT; subst. inversion TREECONT0; subst. reflexivity.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + reflexivity.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      destruct (tree_res treelk gm inp backward) as [[inp1 res1]|] eqn:RES1; inversion RES_LK; subst.
      destruct (tree_res treelk0 gmlk inp backward) as [[inp2 res2]|] eqn:RES2; inversion FAIL_LK; subst.
      clear RES_LK FAIL_LK. rewrite first_tree_leaf in RES1, RES2.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + rewrite <- H2 in RES2. inversion RES2.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + rewrite <- H1 in RES1. inversion RES1.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      destruct (tree_res treelk gm inp backward) as [[inp1 res1]|] eqn:RES1; inversion FAIL_LK; subst.
      destruct (tree_res treelk0 gm inp backward) as [[inp2 res2]|] eqn:RES2; inversion RES_LK; subst.
      clear RES_LK FAIL_LK. rewrite first_tree_leaf in RES1, RES2.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + rewrite <- H1 in RES1. inversion RES1.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + rewrite <- H2 in RES2. inversion RES2.
    - (* Both lookaheads fail *)
      unfold tree_equiv_tr_dir. simpl. reflexivity.
  Qed.

  Lemma ctx_dir_lookahead_fwd_inv:
    forall ctx,
      ctx_dir (CLookaround LookAhead ctx) = Forward ->
      ctx_dir ctx = Forward \/ ctx_dir ctx = Same.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.
  
  Lemma ctx_dir_lookahead_bwd_inv:
    forall ctx,
      ctx_dir (CLookaround LookAhead ctx) = Backward ->
      ctx_dir ctx = Backward.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.

  Lemma ctx_dir_lookbehind_fwd_inv:
    forall ctx,
      ctx_dir (CLookaround LookBehind ctx) = Forward ->
      ctx_dir ctx = Forward.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.

  Lemma ctx_dir_lookbehind_bwd_inv:
    forall ctx,
      ctx_dir (CLookaround LookBehind ctx) = Backward ->
      ctx_dir ctx = Backward \/ ctx_dir ctx = Same.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.

  Lemma ctx_dir_neglookahead_fwd_inv:
    forall ctx,
      ctx_dir (CLookaround NegLookAhead ctx) = Forward ->
      ctx_dir ctx = Forward \/ ctx_dir ctx = Same.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.
  
  Lemma ctx_dir_neglookahead_bwd_inv:
    forall ctx,
      ctx_dir (CLookaround NegLookAhead ctx) = Backward ->
      ctx_dir ctx = Backward.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.

  Lemma ctx_dir_neglookbehind_fwd_inv:
    forall ctx,
      ctx_dir (CLookaround NegLookBehind ctx) = Forward ->
      ctx_dir ctx = Forward.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.

  Lemma ctx_dir_neglookbehind_bwd_inv:
    forall ctx,
      ctx_dir (CLookaround NegLookBehind ctx) = Backward ->
      ctx_dir ctx = Backward \/ ctx_dir ctx = Same.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.

  Lemma regex_equiv_ctx_forward:
    forall r1 r2,
      tree_equiv_dir rer forward r1 r2 ->
      forall ctx, ctx_dir ctx = Forward ->
        forall dir, tree_equiv_dir rer dir (plug_ctx ctx r1) (plug_ctx ctx r2).
  Proof.
    intros r1 r2 EQUIV ctx Hctxforward.
    induction ctx.
    - discriminate.
    - specialize (IHctx Hctxforward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CDisjunctionL _ CHole); auto.
    - specialize (IHctx Hctxforward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CDisjunctionR CHole _); auto.
    - specialize (IHctx Hctxforward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CSequenceL _ CHole); auto.
    - specialize (IHctx Hctxforward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CSequenceR CHole _); auto.
    - specialize (IHctx Hctxforward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CQuantified _ _ _ CHole); auto.
    - destruct lk.
      + simpl. apply regex_equiv_ctx_lookahead.
        apply ctx_dir_lookahead_fwd_inv in Hctxforward. destruct Hctxforward.
        * auto.
        * apply regex_equiv_ctx_samedir; auto.
      + simpl. apply regex_equiv_ctx_lookbehind.
        apply ctx_dir_lookbehind_fwd_inv in Hctxforward. auto.
      + simpl. apply regex_equiv_ctx_neglookahead.
        apply ctx_dir_neglookahead_fwd_inv in Hctxforward. destruct Hctxforward.
        * auto.
        * apply regex_equiv_ctx_samedir; auto.
      + simpl. apply regex_equiv_ctx_neglookbehind.
        apply ctx_dir_neglookbehind_fwd_inv in Hctxforward. auto.
    - specialize (IHctx Hctxforward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CGroup _ CHole); auto.
  Qed.

  Lemma regex_equiv_ctx_backward:
    forall r1 r2,
      tree_equiv_dir rer backward r1 r2 ->
      forall ctx, ctx_dir ctx = Backward ->
        forall dir, tree_equiv_dir rer dir (plug_ctx ctx r1) (plug_ctx ctx r2).
  Proof.
    intros r1 r2 EQUIV ctx Hctxbackward.
    induction ctx.
    - discriminate.
    - specialize (IHctx Hctxbackward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CDisjunctionL _ CHole); auto.
    - specialize (IHctx Hctxbackward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CDisjunctionR CHole _); auto.
    - specialize (IHctx Hctxbackward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CSequenceL _ CHole); auto.
    - specialize (IHctx Hctxbackward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CSequenceR CHole _); auto.
    - specialize (IHctx Hctxbackward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CQuantified _ _ _ CHole); auto.
    - destruct lk; try discriminate.
      + simpl. apply regex_equiv_ctx_lookahead.
        apply ctx_dir_lookahead_bwd_inv in Hctxbackward. auto.
      + simpl. apply regex_equiv_ctx_lookbehind.
        apply ctx_dir_lookbehind_bwd_inv in Hctxbackward. destruct Hctxbackward.
        * auto.
        * apply regex_equiv_ctx_samedir; auto.
      + simpl. apply regex_equiv_ctx_neglookahead.
        apply ctx_dir_neglookahead_bwd_inv in Hctxbackward. auto.
      + simpl. apply regex_equiv_ctx_neglookbehind.
        apply ctx_dir_neglookbehind_bwd_inv in Hctxbackward. destruct Hctxbackward.
        * auto.
        * apply regex_equiv_ctx_samedir; auto.
    - specialize (IHctx Hctxbackward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CGroup _ CHole); auto.
  Qed.

End Congruence.
