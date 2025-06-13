From Linden Require Import Tree Chars Groups Semantics Regex FunctionalUtils.
From Coq Require Import List.
From Warblre Require Import Parameters Base.
Import ListNotations.

Section Equivalence.
  Context `{characterClass: Character.class}.

  Definition input_eqb (i1 i2: input): bool :=
    if input_eq_dec i1 i2 then true else false.

  Definition gm_eqb (gm1 gm2: group_map): bool :=
    if GroupMap.eq_dec gm1 gm2 then true else false.

  Lemma input_eqb_true:
    forall i1 i2, input_eqb i1 i2 = true -> i1 = i2.
  Proof.
    intros i1 i2 H. unfold input_eqb in H.
    destruct (input_eq_dec i1 i2); auto. inversion H.
  Qed.

  Lemma gm_eqb_true:
    forall gm1 gm2, gm_eqb gm1 gm2 = true -> gm1 = gm2.
  Proof.
    intros gm1 gm2 H. unfold gm_eqb in H.
    destruct GroupMap.eq_dec; auto. discriminate.
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

  Definition is_seen (inpgm: input * group_map) (l: list (input * group_map)): bool :=
    existsb (fun x => leaf_eqb x inpgm) l.

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

  Inductive leaves_equiv: list leaf -> list leaf -> list (input * group_map) -> Prop :=
  | equiv_nil:
    forall seen,
      leaves_equiv [] [] seen
  | equiv_seen_left:
    (* removing a duplicate *)
    forall seen inp gm l1 l2
      (SEEN: is_seen (inp, gm) seen = true)
      (EQUIV: leaves_equiv l1 l2 seen),
      leaves_equiv ((inp,gm)::l1) l2 seen
  | equiv_seen_right:
    (* removing a duplicate *)
    forall seen inp gm l1 l2
      (SEEN: is_seen (inp,gm) seen = true)
      (EQUIV: leaves_equiv l1 l2 seen),
      leaves_equiv l1 ((inp,gm)::l2) seen
  | equiv_cons:
    forall seen inp gm l1 l2
      (NEW: is_seen (inp,gm) seen = false)
      (EQUIV: leaves_equiv l1 l2 ((inp,gm)::seen)),
      leaves_equiv ((inp,gm)::l1) ((inp,gm)::l2) seen.
  

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
      leaves_equiv l1 l2 seen ->
      leaves_equiv l1 (pref++l2) seen.
  Proof.
    intros l1 l2 seen pref H H0. induction pref; simpl; auto.
    destruct a as [i g]. simpl in H.
    destruct (is_seen (i, g) seen) eqn:EX.
    2: { inversion H. }
    apply equiv_seen_right; auto.
  Qed.

  Theorem equiv_nodup:
    forall l1 l2 seen,
      leaves_equiv l1 l2 seen <->
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
    forall l seen, leaves_equiv l l seen.
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
      leaves_equiv l1 l2 seen ->
      leaves_equiv l2 l1 seen.
  Proof.
    intros l1 l2 seen H.
    induction H; solve[constructor; auto].
  Qed.

  Lemma equiv_remove_left:
    forall l1 l2 inp gm seen
      (SEEN: is_seen (inp,gm) seen = true)
      (EQUIV: leaves_equiv ((inp,gm)::l1) l2 seen),
      leaves_equiv l1 l2 seen.
  Proof.
    intros l1 l2 inp gm seen SEEN EQUIV.
    remember ((inp,gm)::l1) as L1.
    induction EQUIV; inversion HeqL1; subst; auto.
    - apply equiv_seen_right; auto.
    - rewrite SEEN in NEW. inversion NEW.
  Qed.        

  Lemma leaves_equiv_trans:
    forall l1 l2 l3 seen,
      leaves_equiv l1 l2 seen ->
      leaves_equiv l2 l3 seen ->
      leaves_equiv l1 l3 seen.
  Proof.
    intros l1 l2 l3 seen H H0.
    rewrite equiv_nodup in H.
    rewrite equiv_nodup in H0.
    rewrite equiv_nodup.
    rewrite H. auto.
  Qed.


  (* adding things in the seen accumulator preserves equivalence *)
  (* this means that being equivalent under [] is the strongest form of equivalence *)
  Lemma leaves_equiv_monotony:
    forall l1 l2 seen1 seen2
      (INCLUSION: forall x, is_seen x seen1 = true -> is_seen x seen2 = true),
      leaves_equiv l1 l2 seen1 ->
      leaves_equiv l1 l2 seen2.
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
      leaves_equiv l1 l2 ((inp,gm)::seen) ->
      leaves_equiv ((inp,gm)::l1) ((inp,gm)::l2) seen.
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
      leaves_equiv p1 p2 [] ->
      leaves_equiv l1 l2 [] ->
      leaves_equiv (p1++l1) (p2++l2) [].
  Proof.
    intros p1 p2 l1 l2 PE LE.
    induction PE; try solve[simpl; auto; constructor; auto].
    simpl. apply equiv_cons. auto.
    apply IHPE.
    eapply leaves_equiv_monotony with (seen1:=seen); eauto.
    intros. simpl. rewrite H. rewrite Bool.orb_true_r. auto.
  Qed.

  Lemma equiv_head:
    forall l1 l2,
      leaves_equiv l1 l2 [] ->
      hd_error l1 = hd_error l2.
  Proof.
    intros l1 l2 H. remember [] as nil.
    induction H; subst; try inversion SEEN; auto.
  Qed.

  (** * Actions Equivalence *)

  (* When for all inputs, they have the same leaves in the same order (with possible duplicates) *)
  Definition actions_equiv (acts1 acts2: actions): Prop :=
    forall inp gm dir t1 t2
      (TREE1: is_tree acts1 inp gm dir t1)
      (TREE2: is_tree acts2 inp gm dir t2),
      leaves_equiv (tree_leaves t1 gm inp dir) (tree_leaves t2 gm inp dir) [].

  (* Specialization to two regexes *)
  Definition regex_equiv (r1 r2: regex) : Prop :=
    actions_equiv [Areg r1] [Areg r2].

  (** * Equivalence Properties  *)

  Lemma equiv_refl:
    forall acts, actions_equiv acts acts.
  Proof.
    unfold actions_equiv. intros. specialize (is_tree_determ _ _ _ _ _ _ TREE1 TREE2).
    intros. subst. apply leaves_equiv_refl.
  Qed.

  Lemma equiv_trans:
    forall a1 a2 a3,
      actions_equiv a1 a2 ->
      actions_equiv a2 a3 ->
      actions_equiv a1 a3.
  Proof.
    unfold actions_equiv. intros a1 a2 a3 H H0 inp gm dir t1 t3 TREE1 TREE3.
    assert (exists t2, is_tree a2 inp gm dir t2).
    { exists (compute_tr a2 inp gm dir). apply compute_tr_is_tree. }
    (* otherwise any regex is equivalent to a regex without tree *)
    destruct H1 as [t2 TREE2].
    specialize (H inp gm dir t1 t2 TREE1 TREE2).
    specialize (H0 inp gm dir t2 t3 TREE2 TREE3).
    eapply leaves_equiv_trans; eauto.
  Qed.

  Lemma equiv_commut:
    forall r1 r2,
      actions_equiv r1 r2 ->
      actions_equiv r2 r1.
  Proof.
    unfold actions_equiv. intros r1 r2 H inp gm dir t1 t2 TREE1 TREE2.
    eapply leaves_equiv_comm; eauto.
  Qed.

  (** * Observational Consequence on Backtracking Results  *)

  Theorem observe_equivalence:
    forall r1 r2 str res1 res2
      (EQUIV: regex_equiv r1 r2)
      (RES1: highestprio_result r1 str res1)
      (RES2: highestprio_result r2 str res2),
      res1 = res2.
  Proof.
    intros r1 r2 str res1 res2 EQUIV RES1 RES2.
    inversion RES1. subst. inversion RES2. subst.
    unfold regex_equiv, actions_equiv in EQUIV.
    specialize (EQUIV _ _ _ _ _ TREE TREE0).
    unfold first_branch. rewrite first_tree_leaf. rewrite first_tree_leaf.
    apply equiv_head. auto.
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
      (TREE: is_tree act (fst l) (snd l) dir t),
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

  (* adding new things to the continuation is the same as extending each leaf of the tree with these new things *)
  Theorem leaves_concat:
    forall inp gm dir act1 act2 tapp t1
      (TREE_APP: is_tree (act1 ++ act2) inp gm dir tapp)
      (TREE_1: is_tree act1 inp gm dir t1),
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
      2: admit.
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
      admit. (* Painful? *)
  
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
      2: admit.
      auto.
    
    - (* Backref fail *)
      inversion TREE_APP; subst.
      1: congruence.
      simpl. constructor.
  Admitted.

  (* There are many ways to rephrase this if needed. *)
  (* We don't need the generic FlatMap: we could specialize it to X=Y=leaf, and to f=cont_from_leaf *)
  (* We could also use the functional flat_map, but this would require proving that there is a function that associates a tree to each regex and input *)
  (* I don't really like this solution, because I don't believe the proof relies on that property *)

  (** * Continuation Lemmas  *)

  (* building up to contextual equivalence *)
  (* to reason about the leaves of an app, we use the flatmap result *)

  Lemma app_eq_right:
    forall a1 a2 acts
      (ACTS_EQ: actions_equiv a1 a2),
      actions_equiv (a1 ++ acts) (a2 ++ acts).
  Proof.
    intros. unfold actions_equiv in *.
    intros inp gm dir t1acts t2acts TREE1acts TREE2acts.
    assert (exists t1, is_tree a1 inp gm dir t1). {
      exists (compute_tr a1 inp gm dir). apply compute_tr_is_tree.
    }
    assert (exists t2, is_tree a2 inp gm dir t2). {
      exists (compute_tr a2 inp gm dir). apply compute_tr_is_tree.
    }
    destruct H as [t1 TREE1]. destruct H0 as [t2 TREE2].
    pose proof leaves_concat inp gm dir a1 acts t1acts t1 TREE1acts TREE1.
    pose proof leaves_concat inp gm dir a2 acts t2acts t2 TREE2acts TREE2.
    specialize (ACTS_EQ inp gm dir t1 t2 TREE1 TREE2).
    admit. (* Should now follow from some property on FlatMap and leaves_equiv *)
  Admitted.

  Lemma app_eq_left:
    forall a1 a2 acts
      (ACTS_EQ: actions_equiv a1 a2),
      actions_equiv (acts ++ a1) (acts ++ a2).
  Proof.
    intros. unfold actions_equiv in *.
    intros inp gm dir t1acts t2acts TREE1acts TREE2acts.
    assert (exists tacts, is_tree acts inp gm dir tacts). {
      exists (compute_tr acts inp gm dir). apply compute_tr_is_tree.
    }
    destruct H as [tacts TREEacts].
    pose proof leaves_concat inp gm dir acts a1 t1acts tacts TREE1acts TREEacts.
    pose proof leaves_concat inp gm dir acts a2 t2acts tacts TREE2acts TREEacts.
    (* Now act_from_leaf a1 dir and act_from_leaf a2 dir are morally equivalent *)
    admit.
  Admitted.


  (** * END PLAN *)
  (* Lemma for quantifiers *)
  (*Lemma act_quant_ind:
    forall (r: regex) (P: actions -> input -> group_map -> Direction -> tree -> Prop),
      (forall greedy inp gm dir t,
        is_tree [Areg (Quantified greedy 0 (NoI.N 0) r)] inp gm dir t ->
        P [Areg (Quantified greedy 0 (NoI.N 0) r)] inp gm dir t) ->
      (forall greedy min delta inp gm dir t,
        is_tree [Areg (Quantified greedy min delta r)] inp gm dir t ->
        P [Areg (Quantified greedy min delta r)] inp gm dir t ->
        P [Areg (Quantified greedy (S min) delta r)] inp gm dir t) ->
      (forall greedy delta inp gm dir t,
        is_tree [Areg (Quantified greedy 0 delta r)] inp gm dir t ->
        P [Areg (Quantified greedy 0 (NoI.N 1 + delta)%NoI r)] inp gm dir t) ->
      forall greedy min delta inp gm dir t,
        is_tree [Areg (Quantified greedy min delta r)] inp gm dir t ->
        P [Areg (Quantified greedy min delta r)] inp gm dir t.
  Proof.
    intros r P Hdone Hforced Hfree.
    fix Fix 8.
    intros. inversion H; subst.
  Abort.*)

  Lemma regex_equiv_quant:
    forall r1 r2,
      regex_equiv r1 r2 ->
      forall greedy min delta,
        regex_equiv (Quantified greedy min delta r1) (Quantified greedy min delta r2).
  Proof.
    intros r1 r2 Hequiv greedy min delta.
    unfold regex_equiv, actions_equiv. intros inp gm dir t1 t2 TREE1.
    remember [Areg _] as act1 in TREE1.
    induction TREE1; try discriminate.
    (*rewrite <- app_nil_l with (l := [Areg (Quantified _ _ _ r1)]) in TREE1.
    rewrite <- app_nil_l with (l := [Areg (Quantified greedy min delta r2)]).
    remember [] as act1 in TREE1 at 1. remember [] as act2 in |- * at 1.
    assert (PREF_EQUIV: actions_equiv act1 act2). {
      subst. apply equiv_refl.
    }
    clear Heqact1 Heqact2.
    remember (act1 ++ [Areg (Quantified greedy min delta r1)]) as act1r1quant. induction TREE1; try discriminate.
    - destruct act1; discriminate.
    - admit.
    - admit.
    - *)
  Abort.

  (** * Main theorem: regex equivalence is preserved by plugging into a context *)
  Theorem regex_equiv_ctx:
    forall r1 r2,
      regex_equiv r1 r2 ->
      forall ctx, regex_equiv (plug_ctx ctx r1) (plug_ctx ctx r2).
  Proof.
    intros r1 r2 Hequiv ctx.
    induction ctx.
    - (* Hole *) auto.
    - (* Disjunction left *)
      simpl. unfold regex_equiv, actions_equiv in *.
      intros inp gm dir t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      simpl. apply leaves_equiv_app; auto.
      assert (t1 = t0) by (eapply is_tree_determ; eauto). subst t1. apply leaves_equiv_refl.
    
    - (* Disjunction right *)
      simpl. unfold regex_equiv, actions_equiv in *.
      intros inp gm dir t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      simpl. apply leaves_equiv_app; auto.
      assert (t4 = t3) by (eapply is_tree_determ; eauto). subst t4. apply leaves_equiv_refl.

    - (* Sequence left *)
      simpl. unfold regex_equiv, actions_equiv in *.
      intros inp gm dir t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      destruct dir.
      + (* Forward *)
        simpl in *. pose proof app_eq_left _ _ [Areg r0] IHctx.
        unfold actions_equiv in H. simpl in H. auto.
      + (* Backward *)
        simpl in *. pose proof app_eq_right _ _ [Areg r0] IHctx.
        unfold actions_equiv in H. simpl in H. auto.
      
    - (* Sequence right *)
      simpl. unfold regex_equiv, actions_equiv in *.
      intros inp gm dir t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      destruct dir.
      + (* Forward *)
        simpl in *. pose proof app_eq_right _ _ [Areg r0] IHctx.
        unfold actions_equiv in H. simpl in H. auto.
      + (* Backward *)
        simpl in *. pose proof app_eq_left _ _ [Areg r0] IHctx.
        unfold actions_equiv in H. simpl in H. auto.
      
    - (* Quantified *)
      simpl. unfold regex_equiv, actions_equiv.
      intros inp gm dir t1 t2 TREE1 TREE2.
      remember ([Areg (Quantified _ _ _ (plug_ctx ctx r1))]) as r1quantctx.
      generalize dependent t2.
      induction TREE1; try discriminate; admit.

    - (* Lookaround *)
      simpl. unfold regex_equiv, actions_equiv in *.
      intros inp gm dir t1 t2 TREE1 TREE2.
      inversion TREE1; subst; inversion TREE2; subst.
  Admitted.

End Equivalence.
  