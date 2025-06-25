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
  Context {unicodeProp: Parameters.Property.class Parameters.Character}.
  

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



  (** ** Type markers *)
  #[export] Instance char_marker: CharacterMarker Character := mk_character_marker Character.

  #[export] Instance string_marker: StringMarker string := mk_string_marker string.

  #[export] Instance unicode_marker: UnicodePropertyMarker Property := mk_unicode_property_marker Property.


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
      Parameters.unicode_property_class := unicodeProp;

      Parameters.character_marker := char_marker;
      Parameters.string_marker := string_marker;
      Parameters.unicode_property_marker := unicode_marker
    |}.
  

  (* Some lemmas *)
  Lemma contains_all:
    forall c, CharSet.contains Characters.all c = true.
  Proof.
    intro c. setoid_rewrite CharSetExt.contains_spec. setoid_rewrite CharSetExt.from_list_spec. apply char_all_in.
  Qed.

End LindenParameters.
