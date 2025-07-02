From Warblre Require Import Parameters RegExpRecord.
From Linden Require Import CharSet.
From Coq Require Import List.

Class LindenParameters := make {
  #[global] char:: Character.class;
  #[global] unicodeProp:: Parameters.Property.class (@Parameters.Character char);
  #[global] charsetext_class:: @CharSetExt.class char;

  (* As per the ECMA specification (22.2.2.7.3 Canonicalize ( rer, ch )), when we do not ignore case, canonicalization is the identity function. *)
  canonicalize_casesenst: forall rer chr, RegExpRecord.ignoreCase rer = false -> Character.canonicalize rer chr = chr;
  (* char_all contains all characters. Should be in Warblre as stated in mechanization/spec/Parameters.v, lines 50-51. *)
  char_all_in: forall c, In c (@Character.all char)
}.