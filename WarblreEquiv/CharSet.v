From Warblre Require Import Parameters Result RegExpRecord Typeclasses.
From Coq Require Import List.
From Linden Require Import Tactics Utils.
Import ListNotations.

Local Open Scope bool_scope.

Module CharSetExt.
  Class class `{Character.class}: Type :=
    make
      {
        (* Operations required by the CharSet typeclass *)
        type: Type;
        empty: type;
        from_list: list Character -> type;
        union: type -> type -> type;
        singleton: Character -> type;
        size: type -> nat;
        remove_all: type -> type -> type;
        is_empty: type -> bool;
        contains: type -> Character -> bool;
        range: Character -> Character -> type;
        unique: forall {F: Type} {_: Result.AssertionError F}, type -> Result Character F;
        filter: type -> (Character -> bool) -> type;
        exist: type -> (Character -> bool) -> bool;
        exist_canonicalized: RegExpRecord -> type -> Character -> bool;

        (* Extra operations *)
        elements: type -> list Character;

        (* Properties required by the CharSet class *)
        exist_canonicalized_equiv:
        forall (rer: RegExpRecord) (s: type) (c: Character),
          exist_canonicalized rer s c = exist s (fun c': Character => (Character.canonicalize rer c' ==? c)%wt);

        (* Predicates and extra properties *)
        (* Inspired by Coq.MSets.MSetInterface, unless specified otherwise *)
        In: Character -> type -> Prop;
        Equal s1 s2 := forall c, In c s1 <-> In c s2;
        Empty s := forall c, ~In c s;
        Exists (P: Character -> Prop) s := exists c, In c s /\ P c;
        empty_spec: forall c, ~ In c empty;
        from_list_spec: forall c l, In c (from_list l) <-> List.In c l; (* Custom *)
        union_spec: forall c s1 s2, In c (union s1 s2) <-> In c s1 \/ In c s2;
        singleton_spec: forall x c, In x (singleton c) <-> c = x; (* = instead of fixed equivalence relation *)
        size_spec: forall s, size s = List.length (elements s);
        remove_all_spec: forall c s1 s2, In c (remove_all s1 s2) <-> In c s1 /\ ~In c s2;
        is_empty_spec: forall s, is_empty s = true <-> Empty s; (* custom *)
        contains_spec: forall c s, contains s c = true <-> In c s;
        range_spec: forall c l h, In c (range l h) <-> Character.numeric_value l <= Character.numeric_value c /\ Character.numeric_value c <= Character.numeric_value h; (* custom *)
        unique_succ_spec: forall {F: Type} `{_: Result.AssertionError F} (c: Character) (s: type),
          unique s = Success c <-> Equal s (singleton c); (* custom *)
        unique_succ_error: forall {F: Type} {H: Result.AssertionError F} (s: type),
          (exists c, unique s = Success c) \/ unique s = Error (@Result.f F H); (* custom *)
        filter_spec: forall f c s,
          In c (filter s f) <-> In c s /\ f c = true;
        exist_spec: forall f s,
          exist s f = true <-> Exists (fun c => f c = true) s;
        elements_spec1: forall c s, List.In c (elements s) <-> In c s;
        elements_spec2: forall s, NoDup (elements s);

        canonicity: forall s1 s2: type, s1 = s2 <-> Equal s1 s2
      }.
  Notation CharSetExt := CharSetExt.type.

  Section Lemmas.
    Context `{charSetExtClass: class}.

    (** *** Equal is an equivalence relation. *)
    #[export] Instance Equal_Reflexive: RelationClasses.Reflexive Equal.
    Proof.
      unfold RelationClasses.Reflexive. intros x c. reflexivity.
    Qed.

    #[export] Instance Equal_Symmetric: RelationClasses.Symmetric Equal.
    Proof.
      unfold RelationClasses.Symmetric. intros x y Heq c. specialize (Heq c). tauto.
    Qed.

    #[export] Instance Equal_Transitive: RelationClasses.Transitive Equal.
    Proof.
      unfold RelationClasses.Transitive. intros x y z Hxy Hyz c.
      specialize (Hxy c). specialize (Hyz c). tauto.
    Qed.

    #[export] Instance Equal_Equivalence: RelationClasses.Equivalence Equal.
    Proof.
      constructor. - apply Equal_Reflexive. - apply Equal_Symmetric. - apply Equal_Transitive.
    Defined.

    (** *** Useful lemmas *)
    Lemma contains_false_iff:
      forall c s, contains s c = false <-> ~In c s.
    Proof.
      intros c s. split; intro H0.
      - intro Habs. rewrite <- contains_spec in Habs. congruence.
      - destruct (contains s c) eqn:Hcontains; try reflexivity.
        rewrite contains_spec in Hcontains. contradiction.
    Qed.

    Lemma empty_contains:
      forall c, contains empty c = false.
    Proof.
      intro c. apply contains_false_iff. apply empty_spec.
    Qed.

    Lemma from_list_contains:
      forall (c: Character) (l: list Character), contains (from_list l) c = true <-> List.In c l.
    Proof.
      intros c l. rewrite contains_spec. apply from_list_spec.
    Qed.

    Lemma union_contains:
      forall (c: Character) (s t: type),
        contains (union s t) c = contains s c || contains t c.
    Proof.
      intros c s t. apply Bool.eq_true_iff_eq.
      rewrite Bool.orb_true_iff.
      do 3 rewrite contains_spec. apply union_spec.
    Qed.

    Lemma remove_all_contains:
      forall (c: Character) (s t: type),
        contains (remove_all s t) c = contains s c && negb (contains t c).
    Proof.
      intros c s t. apply Bool.eq_true_iff_eq.
      rewrite Bool.andb_true_iff.
      rewrite Bool.negb_true_iff. do 2 rewrite contains_spec. rewrite contains_false_iff.
      apply remove_all_spec.
    Qed.

    Lemma filter_contains:
    forall (s: type) (f: Character -> bool) (c: Character),
      contains (filter s f) c = contains s c && f c.
    Proof.
      intros s f c. apply Bool.eq_true_iff_eq.
      rewrite Bool.andb_true_iff.
      do 2 rewrite contains_spec.
      apply filter_spec.
    Qed.

    Lemma exist_iff:
    forall (s: type) (f: Character -> bool),
      exist s f = true <-> exists c: Character, contains s c = true /\ f c = true.
    Proof.
      intros s f. rewrite exist_spec. unfold Exists.
      split; intros [c H0].
      - exists c. rewrite contains_spec. apply H0.
      - exists c. rewrite <- contains_spec. apply H0.
    Qed.

    (* Lemmas following from above lemmas *)
    Lemma exist_false_iff:
      forall (s: type) (f: Character -> bool),
        exist s f = false <-> forall c: Character, contains s c = false \/ f c = false.
    Proof.
      intros s f. split.
      - intros H0 c. destruct contains eqn:Hcontains; destruct f eqn:Hfilter; auto.
        assert (exists c, contains s c = true /\ f c = true) as Hexist. { exists c. auto. }
        rewrite <- exist_iff in Hexist. congruence.
      - intro H0. destruct exist eqn:Hexist; auto.
        rewrite exist_iff in Hexist. destruct Hexist as [c [Hcontains Hfilter]].
        specialize (H0 c). destruct H0; congruence.
    Qed.

    Lemma from_list_contains_inb: forall (c: Character) (l: list Character), contains (from_list l) c = List.inb c l.
    Proof.
      intros c l.
      apply <- Bool.eq_iff_eq_true. rewrite List.inb_spec. apply from_list_contains.
    Qed.

    Lemma union_empty_Equal:
      forall s, Equal (union s empty) s.
    Proof.
      intros s c.
      rewrite union_spec.
      pose proof empty_spec c. tauto.
    Qed.

    Lemma union_empty:
      forall s, union s empty = s.
    Proof.
      intro s.
      apply canonicity. apply union_empty_Equal.
    Qed.

    Lemma contains_singleton_self:
      forall c, contains (singleton c) c = true.
    Proof.
      intro c. rewrite contains_spec, singleton_spec. reflexivity.
    Qed.


    Lemma contains_singleton:
      forall c chr, contains (singleton c) chr = (chr ==? c)%wt.
    Proof.
      intros c chr.
      apply Bool.eq_true_iff_eq. split.
      - intro Hcontains. rewrite contains_spec, singleton_spec in Hcontains. subst chr. apply EqDec.reflb.
      - intro Heq. rewrite EqDec.inversion_true in Heq. subst chr. apply contains_singleton_self.
    Qed.



    
    (** *** Lemmas required by Warblre's CharSet typeclass. *)

    Lemma singleton_in_elements: forall c, List.In c (elements (singleton c)).
    Proof.
      intro c. rewrite elements_spec1, singleton_spec. reflexivity.
    Qed.

    Lemma singleton_in_elements_only: forall c c', List.In c' (elements (singleton c)) -> c' = c.
    Proof.
      intros c c' Hin. rewrite elements_spec1, singleton_spec in Hin. congruence.
    Qed.
    
    Lemma singleton_elements: forall c, elements (singleton c) = [c].
    Proof.
      intros c. destruct (elements (singleton c)) as [|x l] eqn:Heqelts.
      - pose proof singleton_in_elements c as Hin. rewrite Heqelts in Hin. inversion Hin.
      - pose proof singleton_in_elements c as Hin. pose proof singleton_in_elements_only c as Hinonly. rewrite Heqelts in Hinonly.
        assert (Hxc: x = c). {
          apply Hinonly. constructor. reflexivity.
        }
        subst x.
        pose proof elements_spec2 (singleton c) as Hnodup. rewrite Heqelts in Hnodup.
        inversion Hnodup as [|x l0 Hnotintl Hnoduptl Heqx]. subst x l0.
        destruct l as [|x l']. 1: reflexivity.
        assert (Hxc: x = c). {
          apply Hinonly. constructor; constructor; reflexivity.
        }
        exfalso. apply Hnotintl. subst x. constructor; reflexivity.
    Qed.

    Lemma singleton_size: forall c, size (singleton c) = 1.
    Proof.
      intro c.
      rewrite size_spec.
      replace (elements (singleton c)) with [c].
      2: { symmetry. apply singleton_elements. }
      reflexivity.
    Qed.

    Lemma singleton_exist: forall c p, exist (singleton c) p = p c.
    Proof.
      intros c p. apply Bool.eq_true_iff_eq.
      rewrite exist_spec. unfold Exists. split.
      - intros [c0 [Hin Hp]]. rewrite singleton_spec in Hin. subst c0. apply Hp.
      - intro Hp. exists c. split. + now apply singleton_spec. + apply Hp.
    Qed.

    Lemma singleton_unique: forall {F: Type} {af: Result.AssertionError F} c, @unique _ _ F af (singleton c) = Success c.
    Proof.
      intros F af c. apply unique_succ_spec. unfold Equal. reflexivity.
    Qed.
  End Lemmas.
End CharSetExt.
