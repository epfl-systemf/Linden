From Linden Require Import Chars LindenParameters.
From Warblre Require Import Parameters.

Definition equiv_cd_charset (cd: char_descr) (charset: CharSet) :=
  forall c: Char, char_match c cd = CharSet.contains charset c.

(* Lemma for character descriptor inversion *)
Lemma equiv_cd_inv:
  forall cd s, equiv_cd_charset cd s -> equiv_cd_charset (CdInv cd) (CharSet.remove_all Characters.all s).
Proof.
  intros cd s H c.
  rewrite charset_remove_all_contains. simpl. specialize (H c).
  unfold Characters.all, Character.all. simpl. rewrite charset_from_list_contains_inb, char_all_inb. simpl. now f_equal.
Qed.

(* Lemmas for various character descriptors *)
Lemma equiv_cd_digits:
  equiv_cd_charset CdDigits Characters.digits.
Proof.
  intro c. simpl. unfold Characters.digits. now rewrite charset_from_list_contains_inb.
Qed.

Lemma equiv_cd_whitespace:
  equiv_cd_charset CdWhitespace (CharSet.union Characters.white_spaces Characters.line_terminators).
Proof.
  intro c. simpl. unfold Characters.white_spaces, Characters.line_terminators. rewrite charset_union_contains. now do 2 rewrite charset_from_list_contains_inb.
Qed.

Lemma equiv_cd_wordchar:
  equiv_cd_charset CdWordChar Characters.ascii_word_characters.
Proof.
  intro c. simpl. unfold Characters.ascii_word_characters. now rewrite charset_from_list_contains_inb.
Qed.

Lemma equiv_cd_single:
  forall c, equiv_cd_charset (CdSingle c) (CharSet.singleton c).
Proof.
  intros c chr. simpl. symmetry. apply charset_contains_singleton.
Qed.
