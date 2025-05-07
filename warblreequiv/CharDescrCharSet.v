From Linden Require Import Chars LindenParameters RegexpTranslation.
From Warblre Require Import Parameters Semantics Result.
Import Result.Notations.

Local Open Scope result_flow.

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

(* Lemma for character descriptor union *)
Lemma equiv_cd_union:
  forall cd1 cd2 s1 s2,
    equiv_cd_charset cd1 s1 -> equiv_cd_charset cd2 s2 ->
    equiv_cd_charset (CdUnion cd1 cd2) (CharSet.union s1 s2).
Proof.
  intros cd1 cd2 s1 s2 Hequiv1 Hequiv2 c.
  simpl. rewrite charset_union_contains. rewrite Hequiv1. rewrite Hequiv2. reflexivity.
Qed.

(* Lemmas for various character descriptors *)
Lemma equiv_cd_empty:
  equiv_cd_charset CdEmpty CharSet.empty.
Proof.
  intro c. simpl. rewrite charset_empty_contains. reflexivity.
Qed.

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

(* TODO Take dotAll flag into account *)
Lemma equiv_cd_dot:
  equiv_cd_charset CdDot Characters.all.
Proof.
  intro c. simpl. unfold Characters.all, Character.all. simpl.
  rewrite charset_from_list_contains_inb. symmetry. apply char_all_inb.
Qed.

Lemma equiv_cd_single:
  forall c, equiv_cd_charset (CdSingle c) (CharSet.singleton c).
Proof.
  intros c chr. simpl. symmetry. apply charset_contains_singleton.
Qed.

(* Lemmas for ClassRanges *)
Lemma equiv_cd_ClassAtom:
  forall ca cacd rer,
    equiv_ClassAtom ca cacd ->
    exists a, Semantics.compileToCharSet_ClassAtom ca rer = Success a /\ equiv_cd_charset cacd a.
Proof.
  intros ca cacd rer Hequiv.
  inversion Hequiv as [c Heqca Heqcacd | esc cd Hequiv' Heqca Heqcacd]; simpl.
  - unfold Coercions.Coercions.wrap_CharSet. eexists. split. + reflexivity. + apply equiv_cd_single.
  - admit.
Admitted.
  

Lemma equiv_cd_ClassRanges:
  forall crs cd rer,
    equiv_ClassRanges crs cd ->
    exists a, Semantics.compileToCharSet crs rer = Success a /\
           equiv_cd_charset cd a.
Proof.
  intros crs cd rer Hequiv.
  induction Hequiv as [|ca cacd t tcd Hequiv' Hequiv IH | l h cl ch t tcd Hequivl Hequivh Hl_le_h Hequiv IH].
  - simpl. unfold Coercions.Coercions.wrap_CharSet.
    eexists. split. + reflexivity. + apply equiv_cd_empty.
  - simpl. pose proof equiv_cd_ClassAtom ca cacd rer Hequiv' as [A [HeqA Hequivatom]].
    rewrite HeqA. simpl.
    destruct IH as [B [HeqB IH]]. rewrite HeqB. simpl.
    unfold Coercions.Coercions.wrap_CharSet. eexists. split. + reflexivity. + now apply equiv_cd_union.
  - simpl.
    pose proof equiv_cd_ClassAtom l (CdSingle cl) rer Hequivl as [A [HeqA Hequivatoml]].
    pose proof equiv_cd_ClassAtom h (CdSingle ch) rer Hequivh as [B [HeqB Hequivatomh]].
    rewrite HeqA, HeqB. simpl.
    destruct IH as [C [HeqC IH]]. rewrite HeqC. simpl.
    unfold Semantics.characterRange.
    admit.
Admitted.
