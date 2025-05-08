From Warblre Require Import Parameters Typeclasses RegExpRecord Patterns Result Errors.
From Linden Require Import Chars Utils CharSet.
From Coq Require Import List.
Import ListNotations.
Import Result.Notations.
Import Utils.List.

Local Open Scope bool_scope.


(** * Instantiation of Warblre typeclasses String, Property (Unicode) *)

Section LindenParameters.
  Context `{characterClass: Character.class}.
  

  (* As per the ECMA specification (22.2.2.7.3 Canonicalize ( rer, ch )), when we do not ignore case, canonicalization is the identity function. *)
  Axiom canonicalize_casesenst: forall rer chr, RegExpRecord.ignoreCase rer = false -> Character.canonicalize rer chr = chr.


  (** ** Strings *)

  (* Adapted from String.substring: returns the substring of s starting at index n and of length m (or less if the string is not long enough). *)
  Fixpoint substring (s: string) (n m: nat): string :=
    match n, m, s with
    | 0, 0, _ => nil
    | 0, S m', nil => s
    | 0, S m', c::s' => c::substring s' 0 m'
    | S n', _, nil => s
    | S n', _, c::s' => substring s' n' m
    end.

  Definition advanceStringIndex (s: string) (i: nat) := S i.
  Definition getStringIndex (s: string) (i: nat) := i.
  (* Linden strings are just lists of characters *)
  Definition to_char_list (s: string): list Character := s.

  #[export] Instance string_String: String.class Character := {|
    String.type := string;
    String.eqdec := string_EqDec;
    String.length := @List.length Character;
    String.substring := substring;
    String.advanceStringIndex := advanceStringIndex;
    String.getStringIndex := getStringIndex;
    String.to_char_list := to_char_list
  |}.



  (** ** Unicode properties *)
  (* We don't support Unicode properties *)
  Inductive NoProperty: Type := .

  Definition NoProp_code_points_for (p: NoProperty): list Character := match p with end.

  #[refine,export] Instance NoPropertyProp: Property.class Character := {|
    Property.type := NoProperty;
    Property.code_points_for := NoProp_code_points_for
  |}.
  Proof.
    constructor. decide equality.
  Defined.



  (** ** Type markers *)
  #[export] Instance char_marker: CharacterMarker Character := mk_character_marker Character.

  #[export] Instance string_marker: StringMarker string := mk_string_marker string.

  #[export] Instance empty_unicode_marker: UnicodePropertyMarker NoProperty := mk_unicode_property_marker NoProperty.


  (** ** CharSets *)
  Parameter charsetext_class: @CharSetExt.class characterClass.
  #[export] Instance charsetext_classinst: CharSetExt.class := charsetext_class.

  #[export,refine] Instance linden_set_class: CharSet.class :=
    {|
      CharSet.type := CharSetExt.type;
      CharSet.empty := CharSetExt.empty;
      CharSet.from_list := CharSetExt.from_list;
      CharSet.union := CharSetExt.union;
      CharSet.singleton := CharSetExt.singleton;
      CharSet.size := CharSetExt.size;
      CharSet.remove_all := CharSetExt.remove_all;
      CharSet.is_empty := CharSetExt.is_empty;
      CharSet.contains := CharSetExt.contains;
      CharSet.range := CharSetExt.range;
      CharSet.unique := @CharSetExt.unique _ _;
      CharSet.filter := CharSetExt.filter;
      CharSet.exist := CharSetExt.exist;
      CharSet.exist_canonicalized := CharSetExt.exist_canonicalized;
      CharSet.exist_canonicalized_equiv := CharSetExt.exist_canonicalized_equiv
    |}.
  Proof.
    - apply CharSetExt.singleton_size.
    - apply CharSetExt.singleton_exist.
    - apply @CharSetExt.singleton_unique.
  Defined.

  (** ** Parameters class *)

  #[export] Instance LindenParameters: Parameters := {|
      Parameters.character_class := characterClass;

      Parameters.set_class := linden_set_class;
      Parameters.string_class := string_String;
      Parameters.unicode_property_class := NoPropertyProp;

      Parameters.character_marker := char_marker;
      Parameters.string_marker := string_marker;
      Parameters.unicode_property_marker := empty_unicode_marker
    |}.

  (* Lemmas following from above axioms *)
  (*Lemma charset_exist_false_iff:
    forall (s: CharSet) (f: Character -> bool),
      CharSet.exist s f = false <-> forall c: Character, CharSet.contains s c = false \/ f c = false.
  Proof.
    intros s f. split.
    - intros H c. destruct CharSet.contains eqn:Hcontains; destruct f eqn:Hfilter; auto.
      assert (exists c, CharSet.contains s c = true /\ f c = true) as Hexist. { exists c. auto. }
      rewrite <- charset_exist_iff in Hexist. congruence.
    - intro H. destruct CharSet.exist eqn:Hexist; auto.
      rewrite charset_exist_iff in Hexist. destruct Hexist as [c [Hcontains Hfilter]].
      specialize (H c). destruct H; congruence.
  Qed.

  Lemma charset_from_list_contains_inb: forall (c: Character) (l: list Character), CharSet.contains (CharSet.from_list l) c = inb c l.
  Proof.
    intros c l.
    apply <- Bool.eq_iff_eq_true. rewrite inb_spec. apply charset_from_list_contains.
  Qed.

  Lemma charset_union_empty:
    forall s, CharSet.union s CharSet.empty = s.
  Proof.
    intro s. apply <- charset_ext. intro c.
    rewrite charset_union_contains, charset_empty_contains. apply Bool.orb_false_r.
  Qed.

  Lemma charset_contains_singleton_self:
    forall c, CharSet.contains (CharSet.singleton c) c = true.
  Proof.
    intro c.
    set (p := fun chr => (chr ==? c)%wt).
    assert (Hexist: CharSet.exist (CharSet.singleton c) p = true). {
      rewrite CharSet.singleton_exist. unfold p. apply EqDec.reflb.
    }
    rewrite charset_exist_iff in Hexist. destruct Hexist as [chr [Hcontains Heq]].
    unfold p in Heq. rewrite EqDec.inversion_true in Heq. subst chr. assumption.
  Qed.


  Lemma charset_contains_singleton:
    forall c chr, CharSet.contains (CharSet.singleton c) chr = (chr ==? c)%wt.
  Proof.
    intros c chr.
    apply Bool.eq_true_iff_eq. split.
    - intro Hcontains. set (f := fun c' => (chr ==? c')%wt).
      assert (H: exists chr0, CharSet.contains (CharSet.singleton c) chr0 = true /\ f chr0 = true). {
        exists chr. split; auto. unfold f. apply EqDec.reflb.
      }
      rewrite <- charset_exist_iff in H. rewrite CharSet.singleton_exist in H.
      apply H.
    - intro Heq. rewrite EqDec.inversion_true in Heq. subst chr. apply charset_contains_singleton_self.
  Qed.*)

End LindenParameters.
