From Warblre Require Import Parameters Typeclasses RegExpRecord Patterns.
From Linden Require Import Chars.
From Coq Require Import List.
Import ListNotations.


(** We assume that these types can be used in Warblre *)

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

Instance CharCharacter: Character.class :=
  Character.make Char char_eqdec char_from_numeric_value char_numeric_value
  char_canonicalize char_all char_line_terminators char_digits
  char_white_spaces char_ascii_word_characters char_numeric_pseudo_bij
  char_numeric_round_trip_order.

Instance string_eqdec: EqDec string := {| EqDec.eq_dec := string_eq_dec |}.

(* Adapted from String.substring *)
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

Instance char_marker: CharacterMarker Char := mk_character_marker Char.

Instance string_marker: StringMarker string := mk_string_marker string.

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

Instance empty_unicode_marker: UnicodePropertyMarker NoProperty := mk_unicode_property_marker NoProperty.

(* Character descriptors *)
Parameter char_descr_to_regex: char_descr -> Patterns.Regex.

Axiom single_Char: forall c: Char, char_descr_to_regex (single c) = Patterns.Char c.
Axiom dot_Dot: char_descr_to_regex dot = Patterns.Dot.
