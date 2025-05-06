From Warblre Require Import Parameters Typeclasses RegExpRecord Patterns Result Errors.
From Linden Require Import Chars.
From Coq Require Import List.
Import ListNotations.
Import Result.Notations.

Local Open Scope bool_scope.


(** * Instantiation of Warblre typeclasses Character, String, Property (Unicode) with Linden types *)

(** ** Characters *)

(* We axiomatize most required parameters *)
Instance char_eqdec: EqDec Char := {| EqDec.eq_dec := char_eq_dec |}.
Parameter char_from_numeric_value: nat -> Char.
Parameter char_numeric_value: Char -> nat.
Parameter char_canonicalize: RegExpRecord -> Char -> Char.
Parameter char_all: list Char.
Parameter char_line_terminators: list Char.
Parameter char_digits: list Char.
Parameter char_white_spaces: list Char.
Parameter char_ascii_word_characters: list Char.
Parameter char_numeric_pseudo_bij: forall c, char_from_numeric_value (char_numeric_value c) = c.
Parameter char_numeric_round_trip_order: forall l r, l <= r -> (char_numeric_value (char_from_numeric_value l)) <= (char_numeric_value (char_from_numeric_value r)).

(* As per the ECMA specification (22.2.2.7.3 Canonicalize ( rer, ch )), when we do not ignore case, canonicalization is the identity function. *)
Axiom canonicalize_casesenst: forall rer chr, RegExpRecord.ignoreCase rer = false -> char_canonicalize rer chr = chr.

Instance CharCharacter: Character.class :=
  Character.make Char char_eqdec char_from_numeric_value char_numeric_value
  char_canonicalize char_all char_line_terminators char_digits
  char_white_spaces char_ascii_word_characters char_numeric_pseudo_bij
  char_numeric_round_trip_order.



(** ** Strings *)

Instance string_eqdec: EqDec string := {| EqDec.eq_dec := string_eq_dec |}.

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
Definition to_char_list (s: string): list Char := s.

Instance string_String: String.class Char := {|
  String.type := string;
  String.eqdec := string_eqdec;
  String.length := @List.length Char;
  String.substring := substring;
  String.advanceStringIndex := advanceStringIndex;
  String.getStringIndex := getStringIndex;
  String.to_char_list := to_char_list
|}.



(** ** Unicode properties *)
(* We don't support Unicode properties *)
Inductive NoProperty: Type := .

Definition NoProp_code_points_for (p: NoProperty): list Char := match p with end.

#[refine] Instance NoPropertyProp: Property.class Char := {|
  Property.type := NoProperty;
  Property.code_points_for := NoProp_code_points_for
|}.
Proof.
  constructor. decide equality.
Defined.



(** ** Type markers *)
Instance char_marker: CharacterMarker Char := mk_character_marker Char.

Instance string_marker: StringMarker string := mk_string_marker string.

Instance empty_unicode_marker: UnicodePropertyMarker NoProperty := mk_unicode_property_marker NoProperty.


(** ** Parameters typeclass *)
Parameter linden_set_class: @CharSet.class CharCharacter.

Instance LindenParameters: Parameters := {|
    Parameters.character_class := CharCharacter;

    Parameters.set_class := linden_set_class;
    Parameters.string_class := string_String;
    Parameters.unicode_property_class := NoPropertyProp;

    Parameters.character_marker := char_marker;
    Parameters.string_marker := string_marker;
    Parameters.unicode_property_marker := empty_unicode_marker
  |}.

(** ** Axiomatization of word_char *)
Axiom word_char_warblre: forall c: Char, word_char c = CharSet.contains (Characters.ascii_word_characters) c.


(** ** Axiomatization of CharSet *)
Axiom charset_empty_contains: forall c: Char, CharSet.contains CharSet.empty c = false.
Axiom charset_from_list_contains: forall (c: Char) (l: list Char), CharSet.contains (CharSet.from_list l) c = true <-> In c l.
Axiom charset_union_contains: forall (c: Char) (s t: CharSet), CharSet.contains (CharSet.union s t) c = CharSet.contains s c || CharSet.contains t c.
(* Singleton? *)
(* Size? *)
(* Remove all? *)
Axiom charset_is_empty_iff: forall s: CharSet, CharSet.is_empty s = true <-> s = CharSet.empty.
(* Range? *)
Axiom charset_unique_iff:
  forall {F: Type} {af: Result.AssertionError F} (s: CharSet) (c: Char),
    @CharSet.unique _ _ F af s = Success c <-> forall c': Char, CharSet.contains s c' = true <-> c' = c.
Axiom charset_filter_contains:
  forall (s: CharSet) (f: Char -> bool) (c: Char),
    CharSet.contains (CharSet.filter s f) c = CharSet.contains s c && f c.
Axiom charset_exist_iff:
  forall (s: CharSet) (f: Char -> bool),
    CharSet.exist s f = true <-> exists c: Char, CharSet.contains s c = true /\ f c = true.

(* Do we need extensionality? *)
Axiom charset_ext:
  forall s t: CharSet,
    s = t <-> forall c: Char, CharSet.contains s c = CharSet.contains t c.
