From Coq Require Export List Equivalence Lia.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import Regex Chars Groups Tree Semantics
  FunctionalSemantics FunctionalUtils ComputeIsTree Parameters
  LWParameters.

Export ListNotations.

Section Definitions.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).


  (** * Observational equivalence *)
  Definition observ_equiv (r1 r2: regex): Prop :=
    forall inp res1 res2
      (RES1: highestprio_result_inp rer r1 inp res1)
      (RES2: highestprio_result_inp rer r2 inp res2),
      res1 = res2.


  (** ** Preparation for list of leaves equivalence *)
  Definition input_eqb (i1 i2: input): bool :=
    if input_eq_dec i1 i2 then true else false.

  Existing Instance GroupMap.EqDec_t.
  Definition gm_eqb (gm1 gm2: group_map): bool :=
    if EqDec.eq_dec gm1 gm2 then true else false.

  Lemma input_eqb_true:
    forall i1 i2, input_eqb i1 i2 = true <-> i1 = i2.
  Proof.
    unfold input_eqb. intros i1 i2.
    split; intros H; destruct (input_eq_dec i1 i2); subst; auto.
    inversion H.
  Qed.

  Lemma gm_eqb_true:
    forall gm1 gm2, gm_eqb gm1 gm2 = true <-> gm1 = gm2.
  Proof.
    unfold gm_eqb. intros gm1 gm2.
    split; intros H; destruct (EqDec.eq_dec); subst; auto.
    inversion H.
  Qed.

  Definition leaf_eqb (leaf1 leaf2: leaf): bool :=
    match leaf1, leaf2 with
    | (i1, gm1), (i2, gm2) => input_eqb i1 i2 && gm_eqb gm1 gm2
    end.

  Lemma leaf_eqb_true:
    forall leaf1 leaf2, leaf_eqb leaf1 leaf2 = true -> leaf1 = leaf2.
  Proof.
    intros leaf1 leaf2 H. unfold leaf_eqb in H.
    destruct leaf1 as [i1 gm1]. destruct leaf2 as [i2 gm2].
    apply Bool.andb_true_iff in H as [Hinp Hgm].
    f_equal.
    - now apply input_eqb_true.
    - now apply gm_eqb_true.
  Qed.

  Lemma leaf_eqb_reflb:
    forall leaf, leaf_eqb leaf leaf = true.
  Proof.
    intros [inp gm]. unfold leaf_eqb.
    apply Bool.andb_true_iff. split.
    - unfold input_eqb. destruct input_eq_dec; try reflexivity. contradiction.
    - unfold gm_eqb. destruct EqDec.eq_dec; try reflexivity. contradiction.
  Qed.

  Definition is_seen (inpgm: input * group_map) (l: list (input * group_map)): bool :=
    existsb (fun x => leaf_eqb x inpgm) l.

  Lemma is_seen_spec:
    forall inpgm l, is_seen inpgm l = true <-> In inpgm l.
  Proof.
    intros. split; intro.
    - unfold is_seen in H. rewrite existsb_exists in H. destruct H as [x [Hin Heq]].
      apply leaf_eqb_true in Heq. subst x. auto.
    - induction l.
      + inversion H.
      + destruct H.
        * subst a. simpl. rewrite leaf_eqb_reflb. reflexivity.
        * simpl. rewrite IHl by assumption. rewrite Bool.orb_true_r. reflexivity.
  Qed.

  Fixpoint filter_leaves (l:list leaf) (seen: list (input * group_map)) : list leaf :=
    match l with
    | [] => []
    | (inp,gm)::l' =>
        match (is_seen (inp,gm) seen) with
        | true => filter_leaves l' seen
        | false => (inp,gm) :: (filter_leaves l' ((inp,gm)::seen)) 
        end
    end.



  (** * List of Leaves Equivalence  *)

  (* relates two ordered list of leaves when they are equivalent up to removing duplicates (that have the same input) *)
  (* the notion of duplicates should change in presence of backreferences (to also include group maps) *)
  (* the third list, seen, accumulates inputs that have already been seen and can be removed *)

  Inductive leaves_equiv: list (input * group_map) -> list leaf -> list leaf -> Prop :=
  | equiv_nil:
    forall seen,
      leaves_equiv seen [] []
  | equiv_seen_left:
    (* removing a duplicate *)
    forall seen inp gm l1 l2
      (SEEN: is_seen (inp, gm) seen = true)
      (EQUIV: leaves_equiv seen l1 l2),
      leaves_equiv seen ((inp,gm)::l1) l2
  | equiv_seen_right:
    (* removing a duplicate *)
    forall seen inp gm l1 l2
      (SEEN: is_seen (inp,gm) seen = true)
      (EQUIV: leaves_equiv seen l1 l2),
      leaves_equiv seen l1 ((inp,gm)::l2)
  | equiv_cons:
    forall seen inp gm l1 l2
      (NEW: is_seen (inp,gm) seen = false)
      (EQUIV: leaves_equiv ((inp,gm)::seen) l1 l2),
      leaves_equiv seen ((inp,gm)::l1) ((inp,gm)::l2).

  Lemma filter_decomp:
    forall l seen i g res,
      filter_leaves l seen = (i,g)::res ->
      exists l1 l2,
        l = l1 ++ (i,g)::l2 /\
          filter_leaves l1 seen = [] /\
          filter_leaves l2 ((i,g)::seen) = res.
  Proof.
    intros l seen i g res H. induction l.
    { simpl in H. inversion H. }
    simpl in H. destruct a as [inp gm].
    destruct (is_seen (inp,gm) seen) eqn:EX.
    - apply IHl in H as [l1 [l2 [HAPP [HPREF HSUF]]]].
      exists ((inp,gm)::l1). exists l2. split; try split.
      + simpl. rewrite HAPP. auto.
      + simpl. rewrite EX. auto.
      + auto.
    - injection H as <- <- <-.
      exists []. exists l. split; try split; auto.
  Qed.


  Lemma equiv_empty_right:
    forall l1 l2 seen pref,
      filter_leaves pref seen = [] ->
      leaves_equiv seen l1 l2 ->
      leaves_equiv seen l1 (pref++l2).
  Proof.
    intros l1 l2 seen pref H H0. induction pref; simpl; auto.
    destruct a as [i g]. simpl in H.
    destruct (is_seen (i, g) seen) eqn:EX.
    2: { inversion H. }
    apply equiv_seen_right; auto.
  Qed.

  Theorem equiv_nodup:
    forall l1 l2 seen,
      leaves_equiv seen l1 l2 <->
        filter_leaves l1 seen = filter_leaves l2 seen.
  Proof.
    intros l1 l2 seen. split; intros H.
    - induction H; auto.
      + simpl. rewrite SEEN. apply IHleaves_equiv.
      + simpl. rewrite SEEN. apply IHleaves_equiv.
      + simpl. rewrite NEW. rewrite IHleaves_equiv. auto.
    - generalize dependent seen. generalize dependent l2.
      induction l1; intros.
      + simpl in H. induction l2.
        * constructor.
        * destruct a. simpl in H.
          destruct (is_seen (i, g) seen) eqn:SEEN; inversion H.
          apply equiv_seen_right; auto.
      + destruct a. simpl in H.
        destruct (is_seen (i, g) seen) eqn:SEEN.
        * apply equiv_seen_left; auto.
        * symmetry in H. apply filter_decomp in H as [pref [suf [HAPP [HPREF HSUF]]]].
          rewrite HAPP. apply equiv_empty_right; auto.
          apply equiv_cons; auto.
  Qed.


  Lemma leaves_equiv_refl:
    forall l seen, leaves_equiv seen l l.
  Proof.
    intros l. induction l; intros.
    { constructor. }
    destruct a.
    destruct (is_seen (i,g) seen) eqn:SEEN.
    - apply equiv_seen_right; auto.
      apply equiv_seen_left; auto.
    - apply equiv_cons; auto.
  Qed.
  
  Lemma leaves_equiv_comm:
    forall l1 l2 seen,
      leaves_equiv seen l1 l2 ->
      leaves_equiv seen l2 l1.
  Proof.
    intros l1 l2 seen H.
    induction H; solve[constructor; auto].
  Qed.

  Lemma equiv_remove_left:
    forall l1 l2 inp gm seen
      (SEEN: is_seen (inp,gm) seen = true)
      (EQUIV: leaves_equiv seen ((inp,gm)::l1) l2),
      leaves_equiv seen l1 l2.
  Proof.
    intros l1 l2 inp gm seen SEEN EQUIV.
    remember ((inp,gm)::l1) as L1.
    induction EQUIV; inversion HeqL1; subst; auto.
    - apply equiv_seen_right; auto.
    - rewrite SEEN in NEW. inversion NEW.
  Qed.        

  Lemma leaves_equiv_trans:
    forall l1 l2 l3 seen,
      leaves_equiv seen l1 l2 ->
      leaves_equiv seen l2 l3 ->
      leaves_equiv seen l1 l3 .
  Proof.
    intros l1 l2 l3 seen H H0.
    rewrite equiv_nodup in H.
    rewrite equiv_nodup in H0.
    rewrite equiv_nodup.
    rewrite H. auto.
  Qed.


  (* adding things in the seen accumulator preserves equivalence *)
  (* this means that being equivalent under [] is the strongest form of equivalence *)
  (* Note that this also allows removing duplicates from the accumulator *)
  Lemma leaves_equiv_monotony:
    forall l1 l2 seen1 seen2
      (INCLUSION: forall x, is_seen x seen1 = true -> is_seen x seen2 = true),
      leaves_equiv seen1 l1 l2 ->
      leaves_equiv seen2 l1 l2.
  Proof.
    intros l1 l2 seen1 seen2 INCLUSION H.
    generalize dependent seen2.
    induction H; intros; try solve[constructor; auto].
    destruct (is_seen (inp, gm) seen2) eqn:EX2.
    - apply equiv_seen_right; auto.
      apply equiv_seen_left; auto.
      apply IHleaves_equiv.
      intros. simpl in H0. rewrite Bool.orb_true_iff in H0.
      destruct H0.
      + subst. fold (leaf_eqb (inp, gm) x) in H0. apply leaf_eqb_true in H0. subst. auto.
      + apply INCLUSION. auto.
    - apply equiv_cons; auto.
      apply IHleaves_equiv.
      intros x SEEN. simpl in SEEN.
      rewrite Bool.orb_true_iff in SEEN.
      destruct SEEN.
      + simpl. rewrite H0. auto.
      + simpl. apply INCLUSION in H0.
        rewrite H0. rewrite Bool.orb_true_r. auto.
  Qed.

  Lemma seen_or_not:
    forall seen inp gm l1 l2,
      leaves_equiv ((inp,gm)::seen) l1 l2 ->
      leaves_equiv seen ((inp,gm)::l1) ((inp,gm)::l2).
  Proof.
    intros seen inp gm l1 l2 H.
    destruct (is_seen (inp,gm) seen) eqn:SEEN.
    - apply equiv_seen_right; auto.
      apply equiv_seen_left; auto.
      eapply leaves_equiv_monotony with (seen1:=(inp,gm)::seen); eauto.
      intros x H0. unfold is_seen in H0. simpl in H0.
      apply Bool.orb_prop in H0. destruct H0; auto.
      fold (leaf_eqb (inp, gm) x) in H0. apply leaf_eqb_true in H0; subst; auto.
    - apply equiv_cons; auto.
  Qed.

  Lemma leaves_equiv_app:
    forall p1 p2 l1 l2,
      leaves_equiv [] p1 p2 ->
      leaves_equiv [] l1 l2 ->
      leaves_equiv [] (p1++l1) (p2++l2).
  Proof.
    intros p1 p2 l1 l2 PE LE.
    induction PE; try solve[simpl; auto; constructor; auto].
    simpl. apply equiv_cons. auto.
    apply IHPE.
    eapply leaves_equiv_monotony with (seen1:=seen); eauto.
    intros. simpl. rewrite H. rewrite Bool.orb_true_r. auto.
  Qed.

  (* we sometimes need a more generic version *)
  (* for the suffix we need to update seen with what we've seen so far *)
  Lemma leaves_equiv_app2:
    forall seen p1 p2 l1 l2,
      leaves_equiv seen p1 p2 ->
      leaves_equiv (p1++seen) l1 l2 ->
      leaves_equiv seen (p1++l1) (p2++l2).
  Proof.
    intros seen p1 p2 l1 l2 PE LE.
    induction PE; intros; simpl.
    - simpl in LE. auto.
    - constructor; auto.
      apply IHPE; auto.
      eapply leaves_equiv_monotony with (seen1:=((inp, gm) :: l0) ++ seen); eauto.
      { intros x H. rewrite is_seen_spec in H |-*. rewrite in_app_iff in H |-*. simpl in H.
        destruct H as [[HS|HI]|HL]; auto. rewrite is_seen_spec in SEEN. subst. auto. }
    - constructor; eauto.
    - apply equiv_cons; auto. apply IHPE; auto.
      eapply leaves_equiv_monotony with (seen1:=((inp, gm) :: l0) ++ seen); eauto.
      { intros x H. rewrite is_seen_spec in H |-*. rewrite in_app_iff in H |-*. simpl in H |-*.
        destruct H as [[HS|HI]|HL]; auto. }
  Qed.

  
  Lemma equiv_head:
    forall l1 l2,
      leaves_equiv [] l1 l2 ->
      hd_error l1 = hd_error l2.
  Proof.
    intros l1 l2 H. remember [] as nil.
    induction H; subst; try inversion SEEN; auto.
  Qed.

  (** * Actions Equivalence *)

  (* When for all inputs, they have the same leaves in the same order (with possible duplicates) *)
  (* We first state equivalence for one given direction, e.g. rewritings involving sequences may only be valid in one direction *)
  Definition actions_equiv_dir (acts1 acts2: actions) (dir: Direction): Prop :=
    forall inp gm t1 t2
      (TREE1: is_tree rer acts1 inp gm dir t1)
      (TREE2: is_tree rer acts2 inp gm dir t2),
      leaves_equiv [] (tree_leaves t1 gm inp dir) (tree_leaves t2 gm inp dir).
  
  Definition actions_equiv_dir_cond (acts1 acts2: actions) (dir: Direction) (P: leaf -> Prop): Prop :=
    forall lf, P lf ->
    forall t1 t2
      (TREE1: is_tree rer acts1 (fst lf) (snd lf) dir t1)
      (TREE2: is_tree rer acts2 (fst lf) (snd lf) dir t2),
      leaves_equiv [] (tree_leaves t1 (snd lf) (fst lf) dir) (tree_leaves t2 (snd lf) (fst lf) dir).

  Definition actions_respect_prop_dir (acts: actions) (dir: Direction) (P: leaf -> Prop): Prop :=
    forall inp gm t
      (TREE: is_tree rer acts inp gm dir t),
      Forall P (tree_leaves t gm inp dir).
  
  (* Stating for all directions *)
  Definition actions_equiv (acts1 acts2: actions): Prop :=
    forall inp gm dir t1 t2
      (TREE1: is_tree rer acts1 inp gm dir t1)
      (TREE2: is_tree rer acts2 inp gm dir t2),
      leaves_equiv [] (tree_leaves t1 gm inp dir) (tree_leaves t2 gm inp dir).

  (* actions_equiv_dir with both directions <-> actions_equiv *)
  Lemma actions_equiv_dir_both:
    forall acts1 acts2,
      actions_equiv acts1 acts2 <-> forall dir, actions_equiv_dir acts1 acts2 dir.
  Proof.
    intros. split; intros.
    - unfold actions_equiv_dir. intros. auto.
    - unfold actions_equiv. intros. unfold actions_equiv_dir in H. auto.
  Qed.

  (* Specialization to two regexes *)
  (*Definition regex_equiv_dir (r1 r2: regex) (dir: Direction): Prop :=
    actions_equiv_dir [Areg r1] [Areg r2] dir.*)

  (** * Equivalence Properties  *)

  Lemma equiv_refl:
    forall acts dir, actions_equiv_dir acts acts dir.
  Proof.
    unfold actions_equiv_dir. intros. specialize (is_tree_determ rer _ _ _ _ _ _ TREE1 TREE2).
    intros. subst. apply leaves_equiv_refl.
  Qed.

  Lemma equiv_trans:
    forall a1 a2 a3 dir,
      actions_equiv_dir a1 a2 dir ->
      actions_equiv_dir a2 a3 dir ->
      actions_equiv_dir a1 a3 dir.
  Proof.
    unfold actions_equiv_dir. intros a1 a2 a3 dir H H0 inp gm t1 t3 TREE1 TREE3.
    assert (exists t2, is_tree rer a2 inp gm dir t2).
    { exists (compute_tr rer a2 inp gm dir). apply compute_tr_is_tree. }
    (* otherwise any regex is equivalent to a regex without tree *)
    destruct H1 as [t2 TREE2].
    specialize (H inp gm t1 t2 TREE1 TREE2).
    specialize (H0 inp gm t2 t3 TREE2 TREE3).
    eapply leaves_equiv_trans; eauto.
  Qed.

  Lemma equiv_commut:
    forall r1 r2 dir,
      actions_equiv_dir r1 r2 dir ->
      actions_equiv_dir r2 r1 dir.
  Proof.
    unfold actions_equiv_dir. intros r1 r2 dir H inp gm t1 t2 TREE1 TREE2.
    eapply leaves_equiv_comm; eauto.
  Qed.


  (** * Regex contexts *)
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

  Definition tree_equiv_tr_dir i gm dir tr1 tr2 :=
    leaves_equiv [] (tree_leaves tr1 gm i dir) (tree_leaves tr2 gm i dir).

  Definition tree_nequiv_tr_dir i gm dir tr1 tr2 :=
    tree_res tr1 gm i dir <> tree_res tr2 gm i dir.

  Section IsTree.
    Definition tree_equiv_dir dir r1 r2 :=
      def_groups r1 = def_groups r2 /\
      forall i gm tr1 tr2,
        is_tree rer [Areg r1] i gm dir tr1 ->
        is_tree rer [Areg r2] i gm dir tr2 ->
        tree_equiv_tr_dir i gm dir tr1 tr2.

    Definition tree_equiv r1 r2 :=
      forall dir, tree_equiv_dir dir r1 r2.

    Definition tree_nequiv_dir dir r1 r2 :=
      exists i gm tr1 tr2,
        is_tree rer [Areg r1] i gm dir tr1 /\
        is_tree rer [Areg r2] i gm dir tr2 /\
        tree_nequiv_tr_dir i gm dir tr1 tr2.

    Definition tree_nequiv r1 r2 :=
      exists dir, tree_nequiv_dir dir r1 r2.
  End IsTree.

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

  Lemma tree_equiv_compute_dir_iff {dir r1 r2} :
    tree_equiv_dir dir r1 r2 <-> tree_equiv_compute_dir dir r1 r2.
  Proof.
    unfold tree_equiv_dir, tree_equiv_compute_dir, tree_equiv_tr_dir; split.
    - intros [DEF_GROUPS EQUIV]. eauto 6 using compute_tr_is_tree.
    - intros [DEF_GROUPS Heq]; split; auto. intros * H1 H2.
      pattern tr1; eapply compute_tr_ind with (2 := H1); eauto.
      pattern tr2; eapply compute_tr_ind with (2 := H2); eauto.
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
End Definitions.

#[export]
Hint Unfold
  tree_equiv
  tree_equiv_dir
  tree_equiv_tr_dir
  tree_equiv_compute
  tree_equiv_compute_dir
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
     anchor_satisfied
     is_boundary
     read_char
     word_char
     andb orb negb xorb
  : tree_equiv_symbex.

Hint Rewrite
  PeanoNat.Nat.leb_le
  PeanoNat.Nat.leb_nle
  : tree_equiv_symbex.

Ltac tree_equiv_symbex_step :=
  match goal with
  | _ => progress simpl
  | [  |- context[match ?x with _ => _ end] ] =>
      lazymatch x with
      | context[match _ with _ => _ end] => fail
      | _ => destruct x eqn:?
      end
  end.

Ltac tree_equiv_symbex_prepare :=
  repeat (autounfold with tree_equiv_symbex; simpl).

Ltac tree_equiv_symbex :=
  repeat tree_equiv_symbex_prepare;
  repeat tree_equiv_symbex_step;
  autorewrite with tree_equiv_symbex in *.

Lemma equiv_cons'
  {params: LindenParameters}
  (seen : list (input * group_map))
  (inp : input) (gm : group_map)
  (l1 l2 : list leaf) :
  leaves_equiv ((inp, gm) :: seen) l1 l2 ->
  leaves_equiv seen ((inp, gm) :: l1) ((inp, gm) :: l2).
Proof.
  intros; destruct (is_seen (inp, gm) seen) eqn:?.
  - apply equiv_seen_left, equiv_seen_right; eauto.
    eapply leaves_equiv_monotony; [ | eauto].
    intros; rewrite is_seen_spec in *; simpl in *; intuition (subst; eauto).
  - apply equiv_cons; eauto.
Qed.

Ltac leaves_equiv_step :=
  first [ apply equiv_nil
        | apply equiv_cons'
        | (apply equiv_seen_left + apply equiv_seen_right);
          [ apply is_seen_spec; unfold In; tauto | ] ].

Ltac leaves_equiv_t :=
  first [ reflexivity | repeat leaves_equiv_step ].

Section Relation.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Ltac eqv := repeat red; tree_equiv_rw; solve [congruence | intuition | firstorder].

  Section LeavesEquiv.
    Context (seen: list (input * group_map)).

    #[global] Add Relation (list leaf) (leaves_equiv seen)
        reflexivity proved by (fun l => leaves_equiv_refl l seen)
        symmetry proved by (fun l1 l2 => leaves_equiv_comm l1 l2 seen)
        transitivity proved by (fun l1 l2 l3 => leaves_equiv_trans l1 l2 l3 seen)
        as leaves_equiv_rel.
  End LeavesEquiv.

  Section DirSpecific.
    Context (dir: Direction).
      
    Lemma tree_equiv_dir_reflexive:
      Relation_Definitions.reflexive regex (tree_equiv_dir rer dir).
    Proof.
      unfold Relation_Definitions.reflexive, tree_equiv_dir, tree_equiv_tr_dir.
      intros x; split; auto. intros i gm tr1 tr2 H1 H2.
      assert (tr2 = tr1) by eauto using is_tree_determ. subst tr2.
      apply leaves_equiv_refl.
    Qed.

    Lemma tree_equiv_dir_symmetric:
      Relation_Definitions.symmetric regex (tree_equiv_dir rer dir).
    Proof.
      unfold Relation_Definitions.symmetric, tree_equiv_dir, tree_equiv_tr_dir.
      intros x y [DEF_GROUPS Hequiv]; split; try solve[congruence].
      intros i gm tr1 tr2 H1 H2.
      apply leaves_equiv_comm. auto.
    Qed.

    Lemma tree_equiv_dir_transitive:
      Relation_Definitions.transitive regex (tree_equiv_dir rer dir).
    Proof.
      unfold Relation_Definitions.transitive, tree_equiv_dir, tree_equiv_tr_dir.
      intros x y z [DEF_GROUPS12 H12] [DEF_GROUPS23 H23]; split; try solve[congruence].
      intros i gm tr1 tr3 H1 H3.
      assert (exists tr2, is_tree rer [Areg y] i gm dir tr2). {
        exists (compute_tr rer [Areg y] i gm dir). apply compute_tr_is_tree.
      }
      destruct H as [tr2 H2].
      apply leaves_equiv_trans with (l2 := tree_leaves tr2 gm i dir); auto.
    Qed.

    #[global] Add Relation regex (tree_equiv_dir rer dir)
        reflexivity proved by tree_equiv_dir_reflexive
        symmetry proved by tree_equiv_dir_symmetric
        transitivity proved by tree_equiv_dir_transitive
        as tree_equiv_dir_rel.

    Lemma tree_equiv_compute_dir_reflexive:
      Relation_Definitions.reflexive regex (tree_equiv_compute_dir rer dir).
    Proof.
      unfold Relation_Definitions.reflexive, tree_equiv_compute_dir, tree_equiv_tr_dir.
      intros x; split; auto. intros i gm.
      apply leaves_equiv_refl.
    Qed.

    Lemma tree_equiv_compute_dir_symmetric:
      Relation_Definitions.symmetric regex (tree_equiv_compute_dir rer dir).
    Proof.
      unfold Relation_Definitions.symmetric, tree_equiv_compute_dir, tree_equiv_tr_dir.
      intros x y [DEF_GROUPS Hequiv]; split; try solve[congruence].
      intros i gm.
      apply leaves_equiv_comm. auto.
    Qed.

    Lemma tree_equiv_compute_dir_transitive:
      Relation_Definitions.transitive regex (tree_equiv_compute_dir rer dir).
    Proof.
      unfold Relation_Definitions.transitive, tree_equiv_compute_dir, tree_equiv_tr_dir.
      intros x y z [DEF_GROUPSxy Hxy] [DEF_GROUPSyz Hyz]; split; try solve[congruence].
      intros i gm.
      eauto using leaves_equiv_trans.
    Qed.

    #[global] Add Relation regex (tree_equiv_compute_dir rer dir)
        reflexivity proved by tree_equiv_compute_dir_reflexive
        symmetry proved by tree_equiv_compute_dir_symmetric
        transitivity proved by tree_equiv_compute_dir_transitive
        as tree_equiv_compute_dir_rel.
  End DirSpecific.

  Lemma tree_equiv_reflexive:
    Relation_Definitions.reflexive regex (tree_equiv rer).
  Proof.
    unfold Relation_Definitions.reflexive, tree_equiv.
    intros x dir. apply tree_equiv_dir_reflexive.
  Qed.

  Lemma tree_equiv_symmetric:
    Relation_Definitions.symmetric regex (tree_equiv rer).
  Proof.
    unfold Relation_Definitions.symmetric, tree_equiv.
    intros x y H dir. apply tree_equiv_dir_symmetric. auto.
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
      
  Lemma tree_equiv_compute_reflexive:
    Relation_Definitions.reflexive regex (tree_equiv_compute rer).
  Proof.
    unfold Relation_Definitions.reflexive, tree_equiv_compute, tree_equiv_compute_dir, tree_equiv_tr_dir.
    intros x; split; try reflexivity.
  Qed.

  Lemma tree_equiv_compute_symmetric:
    Relation_Definitions.symmetric regex (tree_equiv_compute rer).
  Proof.
    unfold Relation_Definitions.symmetric, tree_equiv_compute, tree_equiv_compute_dir, tree_equiv_tr_dir.
    intros x y Hxy dir; split.
    - symmetry. apply Hxy; auto.
    - intros i gm. apply leaves_equiv_comm. apply Hxy.
  Qed.

  Lemma tree_equiv_compute_transitive:
    Relation_Definitions.transitive regex (tree_equiv_compute rer).
  Proof.
    unfold Relation_Definitions.transitive, tree_equiv_compute, tree_equiv_compute_dir, tree_equiv_tr_dir.
    intros x y z Hxy Hyz dir; split.
    - transitivity (def_groups y). + apply Hxy; auto. + apply Hyz; auto.
    - intros i gm. pose proof (proj2 (Hxy dir)). pose proof (proj2 (Hyz dir)). eauto using leaves_equiv_trans.
  Qed.

  #[global] Add Relation regex (tree_equiv_compute rer)
      reflexivity proved by tree_equiv_compute_reflexive
      symmetry proved by tree_equiv_compute_symmetric
      transitivity proved by tree_equiv_compute_transitive
      as tree_equiv_compute_rel.

  (* #[global] Instance : Irreflexive (tree_nequiv_dir dir) := ltac:(eqv). *)
  (* #[global] Add Relation regex (tree_nequiv_dir dir) *)
  (*     symmetry proved by ltac:(eqv) *)
  (*     as tree_nequiv_dir_rel. *)

  (* #[global] Instance : Irreflexive tree_nequiv := ltac:(eqv). *)
  (* #[global] Add Relation regex tree_nequiv *)
  (*     symmetry proved by ltac:(eqv) *)
  (*     as tree_nequiv_rel. *)

  (* #[global] Instance : Irreflexive (tree_nequiv_compute_dir dir) := ltac:(eqv). *)
  (* #[global] Add Relation regex (tree_nequiv_compute_dir dir) *)
  (*     symmetry proved by ltac:(eqv) *)
  (*     as tree_nequiv_compute_dir_rel. *)

  (* #[global] Instance : Irreflexive tree_nequiv_compute := ltac:(eqv). *)
  (* #[global] Add Relation regex tree_nequiv_compute *)
  (*     symmetry proved by ltac:(eqv) *)
  (*     as tree_nequiv_compute_rel. *)
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
    intros r1 r2 EQUIV inp res1 res2 RES1 RES2.
    inversion RES1. subst. inversion RES2. subst.
    unfold tree_equiv_dir in EQUIV. destruct EQUIV as [_ EQUIV].
    specialize (EQUIV _ _ _ _ TREE TREE0).
    unfold first_leaf. rewrite first_tree_leaf. rewrite first_tree_leaf.
    apply equiv_head. auto.
  Qed.
  (** * BEGIN PLAN *)

  (** * FlatMap Lemmas  *)

  (* a propositional version of flat_map *)
  (* FlatMap lbase f lmapped means that lmapped corresponds to the list lbase where each element has been replaced by its image by f *)
  Inductive FlatMap {X Y:Type} : list X -> (X -> list Y -> Prop) -> list Y -> Prop :=
  | FM_nil: forall f,
      FlatMap [] f []
  | FM_cons:
    forall lbase f lmapped x ly
      (FM: FlatMap lbase f lmapped)
      (HEAD: f x ly),
      FlatMap (x::lbase) f (ly ++ lmapped).

  (* getting the leaves of a continuation applied to a particular leaf *)
  Inductive act_from_leaf : actions -> Direction -> leaf -> list leaf -> Prop :=
  | afl:
    forall act dir l t
      (TREE: is_tree rer act (fst l) (snd l) dir t),
      act_from_leaf act dir l (tree_leaves t (snd l) (fst l) dir).

  Property FlatMap_app {X Y: Type}:
    forall (lbase1 lbase2 : list X) (f: X -> list Y -> Prop) (lmapped1 lmapped2: list Y),
      FlatMap lbase1 f lmapped1 ->
      FlatMap lbase2 f lmapped2 ->
      FlatMap (lbase1 ++ lbase2) f (lmapped1 ++ lmapped2).
  Proof.
    intros lbase1 lbase2 f lmapped1 lmapped2 FM1 FM2.
    induction FM1.
    - auto.
    - rewrite <- app_assoc, <- app_comm_cons. constructor; auto.
  Qed.


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
      2: contradiction.
      rewrite GM_LK in GM_LK0. injection GM_LK0 as <-.
      destruct positivity eqn:Hpos.
      + unfold lk_group_map in GM_LK. rewrite Hpos in GM_LK.
        pose proof first_tree_leaf treelk gm inp (lk_dir lk) as LK_FIRST.
        destruct (tree_res treelk gm inp (lk_dir lk)) as [[inplk gmlk']|] eqn:TREERES_LK; try discriminate.
        injection GM_LK as ->.
        destruct (tree_leaves treelk gm inp (lk_dir lk)) as [|[inplk' gmlk'] q] eqn:TREELEAVES_LK; try discriminate.
        simpl in *. injection LK_FIRST as <- <-. rewrite Hpos.
        rewrite TREELEAVES_LK. auto.
      + unfold lk_group_map in GM_LK. rewrite Hpos in GM_LK.
        injection GM_LK as <-.
        assert (tree_leaves treelk gm inp (lk_dir lk) = []).
        { apply leaves_group_map_indep with (gm1 := GroupMap.empty) (inp1 := init_input nil) (dir1 := forward).
          apply hd_error_none_nil. rewrite <- first_tree_leaf.
          unfold lk_result in RES_LK. rewrite Hpos in RES_LK. apply RES_LK. }
        simpl. rewrite Hpos, H. auto.
  
    - (* Lookaround failure *)
      inversion TREE_APP; subst;
        assert (treelk0 = treelk) by (eapply is_tree_determ; eauto); subst.
      1: contradiction.
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

  Definition determ {A B: Type} (f: A -> B -> Prop) :=
    forall x y1 y2, f x y1 -> f x y2 -> y1 = y2.

  Lemma act_from_leaf_determ: forall act dir, determ (act_from_leaf act dir).
  Proof.
    intros act dir x y1 y2 Hxy1 Hxy2.
    inversion Hxy1; subst. inversion Hxy2; subst.
    assert (t0 = t) by eauto using is_tree_determ. subst t0. reflexivity.
  Qed.

  Lemma FlatMap_in {A B}:
    forall (l: list A) (f: A -> list B -> Prop) fl x fx,
      determ f ->
      FlatMap l f fl ->
      In x l ->
      f x fx ->
      Forall (fun y => In y fl) fx.
  Proof.
    intros l f fl x fx DETERM FM INxl F.
    revert fl FM.
    induction l.
    1: inversion INxl.
    intros fl FM. destruct INxl.
    - subst a. inversion FM; subst.
      assert (ly = fx) by eauto (* using DETERM *). subst ly. clear HEAD FM F IHl.
      induction fx.
      + constructor.
      + constructor.
        * rewrite <- app_comm_cons. left. reflexivity.
        * eapply Forall_impl; eauto. simpl. tauto.
    - inversion FM; subst. specialize (IHl H lmapped FM0).
      eapply Forall_impl; eauto. simpl. intro. rewrite in_app_iff. tauto.
  Qed.

  Lemma FlatMap_in2:
    forall f leaf fleaf seen fseen,
      determ f -> 
      f leaf fleaf ->
      is_seen leaf seen = true ->
      FlatMap seen f fseen ->
      forall x, is_seen x fleaf = true -> is_seen x fseen = true.
  Proof.
    intros f leaf fleaf seen fseen H H0 H1 H2 x H3.
    rewrite is_seen_spec in H3, H1. rewrite is_seen_spec.
    specialize (FlatMap_in _ _ _ _ _ H H2 H1 H0).
    intros H4. rewrite Forall_forall in H4. auto.
  Qed.

  Lemma leaves_equiv_subseen:
    forall l1 l2 seen subseen,
      (forall x, is_seen x subseen = true -> is_seen x seen = true) ->
      leaves_equiv seen l1 l2 ->
      leaves_equiv seen (subseen ++ l1) l2.
  Proof.
    intros l1 l2 seen subseen SUB EQUIV.
    generalize dependent l1. generalize dependent l2.
    induction subseen; intros; auto.
    destruct a. simpl. constructor.
    - apply (SUB (i,g)). simpl. replace (input_eqb i i) with true.
      2: { symmetry. apply input_eqb_true. auto. }
      simpl. auto. replace (gm_eqb g g) with true; auto.
      { symmetry. apply gm_eqb_true. auto. }
    - apply IHsubseen; auto.
      intros x H. apply SUB. simpl. rewrite H.
      rewrite Bool.orb_true_r. auto.
  Qed.


  Lemma flatmap_leaves_equiv_l_seen:
    forall l1 l2 seen f fseen fl1 fl2,
      determ f ->
      leaves_equiv seen l1 l2 ->
      FlatMap l1 f fl1 ->
      FlatMap l2 f fl2 ->
      FlatMap seen f fseen ->
      leaves_equiv fseen fl1 fl2.
  Proof.
    intros l1 l2 seen f fseen fl1 fl2 DET EQUIV FM1 FM2 FMSEEN.
    generalize dependent fl1. generalize dependent fl2. generalize dependent fseen.
    induction EQUIV; intros.
    - inversion FM2; subst. inversion FM1; subst. apply leaves_equiv_refl.
    - inversion FM1; subst. apply leaves_equiv_subseen; auto.
      eapply FlatMap_in2; eauto.
    - inversion FM2; subst. apply leaves_equiv_rel_Symmetric.
      apply leaves_equiv_subseen; auto.
      2: { apply leaves_equiv_rel_Symmetric. auto. }
      eapply FlatMap_in2; eauto.
    - inversion FM1; inversion FM2; subst.
      specialize (DET _ _ _ HEAD HEAD0). subst.
      apply leaves_equiv_app2; auto.
      + apply leaves_equiv_refl.
      + eapply IHEQUIV; eauto. constructor; auto.
  Qed.

  Lemma flatmap_leaves_equiv_l:
    forall leaves1 leaves2 f leavesf1 leavesf2,
      determ f ->
      leaves_equiv [] leaves1 leaves2 ->
      FlatMap leaves1 f leavesf1 ->
      FlatMap leaves2 f leavesf2 ->
      leaves_equiv [] leavesf1 leavesf2.
  Proof.
    intros.
    eapply flatmap_leaves_equiv_l_seen with (seen := []); eauto. constructor.
  Qed.

  Lemma app_eq_right:
    forall a1 a2 acts dir
      (ACTS_EQ: actions_equiv_dir rer a1 a2 dir),
      actions_equiv_dir rer (a1 ++ acts) (a2 ++ acts) dir.
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
      (ACTS_EQ: actions_equiv_dir rer a1 a2 dir),
      actions_equiv_dir rer (acts ++ a1) (acts ++ a2) dir.
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
      (A_EQ: actions_equiv_dir rer a1 a2 dir)
      (B_EQ: actions_equiv_dir rer b1 b2 dir),
      actions_equiv_dir rer (a1 ++ b1) (a2 ++ b2) dir.
  Proof.
    intros. eapply equiv_trans with (a2:=a1++b2).
    - apply app_eq_left. auto.
    - apply app_eq_right. auto.
  Qed.

  Lemma actions_equiv_interm_prop:
    forall (a1 a2 b1 b2: actions) (P: leaf -> Prop) (dir: Direction),
      actions_equiv_dir rer a1 a2 dir ->
      actions_respect_prop_dir rer a1 dir P ->
      actions_respect_prop_dir rer a2 dir P ->
      actions_equiv_dir_cond rer b1 b2 dir P ->
      actions_equiv_dir rer (a1 ++ b1) (a2 ++ b2) dir.
  Proof.
    intros a1 a2 b1 b2 P dir EQUIV_a PROP1 PROP2 EQUIV_b.
    apply equiv_trans with (a2 := a1 ++ b2).
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
      actions_respect_prop_dir rer b dir P ->
      actions_respect_prop_dir rer (a ++ b) dir P.
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
      actions_respect_prop_dir rer a dir P ->
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
      actions_respect_prop_dir rer a dir (fun _ => False).
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


  (** * END PLAN *)
  (* Lemma for quantifiers *)
  Lemma check_actions_prop:
    forall inp dir,
      actions_respect_prop_dir rer [Acheck inp] dir
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
        actions_equiv_dir_cond rer [Areg (Quantified greedy 0 plus r1)]
          [Areg (Quantified greedy 0 plus r2)] dir
          (fun lf : input * group_map => StrictSuffix.strict_suffix (fst lf) inp dir).
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
      simpl in *. unfold tree_equiv_dir in *. specialize (IHctx Hctxdir).
      destruct IHctx as [IHgroups IHctx]. split.
      1: { simpl. f_equal. auto. }
      intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      unfold tree_equiv_tr_dir in *.
      simpl. apply leaves_equiv_app; auto.
      assert (t1 = t0) by (eapply is_tree_determ; eauto). subst t1. apply leaves_equiv_refl.
    
    - (* Disjunction right *)
      simpl in *. unfold tree_equiv_dir in *. specialize (IHctx Hctxdir).
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
      simpl in *. unfold tree_equiv_dir in *. specialize (IHctx Hctxdir).
      destruct IHctx as [IHgroups IHctx]. split.
      1: { simpl. f_equal. auto. }
      intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      destruct dir.
      + (* Forward *)
        simpl in *. pose proof app_eq_right _ _ [Areg r0] forward IHctx.
        unfold actions_equiv in H. simpl in H. unfold tree_equiv_tr_dir in *. auto.
      + (* Backward *)
        simpl in *. pose proof app_eq_left _ _ [Areg r0] backward IHctx.
        unfold actions_equiv in H. simpl in H. unfold tree_equiv_tr_dir in *. auto.
      
    - (* Quantified *)
      simpl in *. specialize (IHctx Hctxdir). apply regex_equiv_quant. auto.

    - (* Lookaround: direction of context is never Same *)
      exfalso. exact (ctx_dir_lookaround_not_Same _ _ Hctxdir).

    - simpl in *. unfold tree_equiv_dir in *. specialize (IHctx Hctxdir).
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
      unfold lk_group_map in GM_LK, GM_LK0. simpl in *.
      unfold tree_equiv_tr_dir in *. simpl.
      rewrite first_tree_leaf in GM_LK, GM_LK0.
      inversion EQUIV_LK; subst; auto.
      + reflexivity.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + rewrite <- H1 in GM_LK. rewrite <- H2 in GM_LK0. simpl in *.
        injection GM_LK as ->. injection GM_LK0 as <-. inversion TREECONT; subst. inversion TREECONT0; subst.
        simpl. reflexivity.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + symmetry in H1. apply tree_leaves_nil_no_first_branch with (str := []) in H1. contradiction.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + apply FAIL_LK. apply tree_leaves_notnil_first_branch with (gm := gm) (inp := inp) (dir := forward). rewrite <- H2. discriminate.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + symmetry in H2. apply tree_leaves_nil_no_first_branch with (str := []) in H2. contradiction.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + apply FAIL_LK. apply tree_leaves_notnil_first_branch with (gm := gm) (inp := inp) (dir := forward). rewrite <- H1. discriminate.
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
      unfold lk_group_map in GM_LK, GM_LK0. simpl in *.
      unfold tree_equiv_tr_dir in *. simpl.
      rewrite first_tree_leaf in GM_LK, GM_LK0.
      inversion EQUIV_LK; subst; auto.
      + reflexivity.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + rewrite <- H1 in GM_LK. rewrite <- H2 in GM_LK0. simpl in *.
        injection GM_LK as ->. injection GM_LK0 as <-. inversion TREECONT; subst. inversion TREECONT0; subst.
        simpl. reflexivity.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + symmetry in H1. apply tree_leaves_nil_no_first_branch with (str := []) in H1. contradiction.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + apply FAIL_LK. apply tree_leaves_notnil_first_branch with (gm := gm) (inp := inp) (dir := backward).
        rewrite <- H2. discriminate.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + symmetry in H2. apply tree_leaves_nil_no_first_branch with (str := []) in H2. contradiction.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + apply FAIL_LK. apply tree_leaves_notnil_first_branch with (gm := gm) (inp := inp) (dir := backward).
        rewrite <- H1. discriminate.
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
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + symmetry in H2. apply tree_leaves_nil_no_first_branch with (str := []) in H2.
        destruct (first_branch treelk0 []); try contradiction. apply H2. eexists; eauto.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + assert (exists res, first_branch treelk [] = Some res). {
          apply tree_leaves_notnil_first_branch with (gm := gm) (inp := inp) (dir := forward).
          rewrite <- H1. discriminate.
        }
        destruct H as [res H]. congruence.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + (* H1 and FAIL_LK are contradictory *)
        symmetry in H1. apply tree_leaves_nil_no_first_branch with (str := []) in H1.
        destruct (first_branch treelk []); try contradiction. apply H1. eexists; eauto.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + (* H2 and RES_LK are contradictory *)
        assert (exists res, first_branch treelk0 [] = Some res). {
          apply tree_leaves_notnil_first_branch with (gm := gm) (inp := inp) (dir := forward).
          rewrite <- H2. discriminate.
        }
        destruct H as [res H]. congruence.
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
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + (* H2 and FAIL_LK are contradictory *) symmetry in H2. apply tree_leaves_nil_no_first_branch with (str := []) in H2.
        destruct (first_branch treelk0 []); try contradiction. apply H2. eexists; eauto.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + (* H1 and RES_LK are contradictory *) assert (exists res, first_branch treelk [] = Some res). {
          apply tree_leaves_notnil_first_branch with (gm := gm) (inp := inp) (dir := backward).
          rewrite <- H1. discriminate.
        }
        destruct H as [res H]. congruence.
    - (* Impossible case *)
      exfalso.
      unfold lk_result in *. simpl in *.
      specialize (EQUIV _ _ _ _ TREELK TREELK0). unfold tree_equiv_tr_dir in EQUIV.
      inversion EQUIV; subst; auto.
      + (* H1 and FAIL_LK are contradictory *) symmetry in H1. apply tree_leaves_nil_no_first_branch with (str := []) in H1.
        destruct (first_branch treelk []); try contradiction. apply H1. eexists; eauto.
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + unfold is_seen in SEEN. rewrite existsb_exists in SEEN. destruct SEEN as [x [[] _]].
      + (* H2 and RES_LK are contradictory *) assert (exists res, first_branch treelk0 [] = Some res). {
          apply tree_leaves_notnil_first_branch with (gm := gm) (inp := inp) (dir := backward).
          rewrite <- H2. discriminate.
        }
        destruct H as [res H]. congruence.
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
