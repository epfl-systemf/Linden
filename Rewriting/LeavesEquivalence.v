From Linden Require Import Parameters Groups Chars Tree.
From Warblre Require Import RegExpRecord Typeclasses.
From Coq Require Import List.
Import ListNotations.


Section Preparation.
  Context {params: LindenParameters}.


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

End Preparation.

Section Def.
  Context {params: LindenParameters}.

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

End Def.

Section Lemmas.
  Context {params: LindenParameters}.

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

  Lemma equiv_cons'
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
End Lemmas.