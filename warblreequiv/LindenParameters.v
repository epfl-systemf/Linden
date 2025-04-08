From Warblre Require Import Parameters.
From Linden Require Import CharsWarblre.

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