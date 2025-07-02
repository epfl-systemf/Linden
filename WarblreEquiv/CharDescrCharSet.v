From Linden Require Import Chars LWParameters Parameters RegexpTranslation WarblreLemmas CharSet.
From Warblre Require Import Parameters Semantics Result Patterns RegExpRecord Typeclasses.
Import Result.Notations.
Import Patterns.
From Coq Require Import Lia.

Local Open Scope result_flow.

Section CharDescrCharSet.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (* In CharSet equivalences, we do not want to ignore case. This is so that
  each character descriptor is made equivalent to the CharSet passed to
  Semantics.characterSetMatcher for the corresponding Warblre character
  descriptor. *)
  Definition rer_noi : RegExpRecord := {|
    RegExpRecord.ignoreCase := false;
    RegExpRecord.multiline := RegExpRecord.multiline rer;
    RegExpRecord.dotAll := RegExpRecord.dotAll rer;
    RegExpRecord.unicode := tt;
    RegExpRecord.capturingGroupsCount := RegExpRecord.capturingGroupsCount rer
  |}.
  
  Definition equiv_cd_charset (cd: char_descr) (charset: CharSet) :=
    forall c: Character, char_match rer_noi c cd = CharSet.contains charset c.

  (* Lemma for character descriptor inversion *)
  Lemma equiv_cd_inv:
    forall cd s, equiv_cd_charset cd s -> equiv_cd_charset (CdInv cd) (CharSet.remove_all Characters.all s).
  Proof.
    intros cd s H c. specialize (H c).
    simpl. apply Bool.eq_true_iff_eq.
    rewrite CharSetExt.remove_all_contains. rewrite H.
    setoid_rewrite contains_all. simpl. reflexivity.
  Qed.

  (* Lemma for character descriptor union *)
  Lemma equiv_cd_union:
    forall cd1 cd2 s1 s2,
      equiv_cd_charset cd1 s1 -> equiv_cd_charset cd2 s2 ->
      equiv_cd_charset (CdUnion cd1 cd2) (CharSet.union s1 s2).
  Proof.
    intros cd1 cd2 s1 s2 Hequiv1 Hequiv2 c.
    simpl. setoid_rewrite CharSetExt.union_contains. rewrite Hequiv1. rewrite Hequiv2. reflexivity.
  Qed.

  (* Inversion lemma for singletons *)
  Lemma equiv_cd_singleton_invn:
    forall c s,
      equiv_cd_charset (CdSingle c) s -> CharSetExt.Equal s (CharSet.singleton c).
  Proof.
    intros c s Hequiv chr.
    specialize (Hequiv chr). simpl in Hequiv.
    do 2 rewrite canonicalize_casesenst in Hequiv by reflexivity.
    apply Bool.eq_iff_eq_true in Hequiv.
    rewrite CharSetExt.contains_spec in Hequiv.
    rewrite Typeclasses.EqDec.inversion_true in Hequiv.
    setoid_rewrite CharSetExt.singleton_spec. rewrite <- Hequiv. split; congruence.
  Qed.

  (* Lemmas for various character descriptors *)
  Lemma equiv_cd_empty:
    equiv_cd_charset CdEmpty CharSet.empty.
  Proof.
    intro c. simpl. setoid_rewrite CharSetExt.empty_contains. reflexivity.
  Qed.

  Lemma equiv_cd_digits:
    equiv_cd_charset CdDigits Characters.digits.
  Proof.
    intro c. simpl. rewrite inb_canonicalized_casesenst by reflexivity.
    unfold Characters.digits. now setoid_rewrite CharSetExt.from_list_contains_inb.
  Qed.

  Lemma equiv_cd_whitespace:
    equiv_cd_charset CdWhitespace (CharSet.union Characters.white_spaces Characters.line_terminators).
  Proof.
    intro c. simpl. do 2 rewrite inb_canonicalized_casesenst by reflexivity.
    unfold Characters.white_spaces, Characters.line_terminators. setoid_rewrite CharSetExt.union_contains. now setoid_rewrite CharSetExt.from_list_contains_inb.
  Qed.

  Lemma equiv_cd_wordchar:
    equiv_cd_charset CdWordChar Characters.ascii_word_characters.
  Proof.
    intro c. simpl. rewrite inb_canonicalized_casesenst by reflexivity.
    unfold Characters.ascii_word_characters. now setoid_rewrite CharSetExt.from_list_contains_inb.
  Qed.

  Lemma equiv_cd_range:
    forall cl ch,
      Character.numeric_value cl <= Character.numeric_value ch ->
      equiv_cd_charset (CdRange cl ch) (CharSet.range cl ch).
  Proof.
    intros cl ch Hle c. simpl.
    rewrite inb_canonicalized_casesenst by reflexivity.
    apply Bool.eq_true_iff_eq.
    rewrite Utils.List.inb_spec, CharSetExt.contains_spec, CharSetExt.range_spec.
    rewrite List.filter_In, Bool.andb_true_iff, PeanoNat.Nat.leb_le, PeanoNat.Nat.leb_le.
    pose proof char_all_in c. tauto.
  Qed.

  Lemma equiv_cd_dot_dotAll:
    RegExpRecord.dotAll rer = true ->
    equiv_cd_charset CdDot Characters.all.
  Proof.
    intros HdotAll c. simpl. rewrite HdotAll. symmetry. apply contains_all.
  Qed.

  Lemma equiv_cd_dot_noDotAll:
    RegExpRecord.dotAll rer = false ->
    equiv_cd_charset CdDot (CharSet.remove_all Characters.all Characters.line_terminators).
  Proof.
    intros HnoDotAll c. simpl. rewrite HnoDotAll.
    rewrite inb_canonicalized_casesenst by reflexivity.
    apply Bool.eq_true_iff_eq.
    rewrite CharSetExt.remove_all_contains. 
    setoid_rewrite contains_all. simpl.
    unfold Characters.line_terminators. setoid_rewrite CharSetExt.from_list_contains_inb.
    reflexivity.
  Qed.
    
  Lemma equiv_cd_single:
    forall c, equiv_cd_charset (CdSingle c) (CharSet.singleton c).
  Proof.
    intros c chr. simpl. do 2 rewrite canonicalize_casesenst by reflexivity. symmetry. apply CharSetExt.contains_singleton.
  Qed.

  Lemma equiv_cd_unicodeprop:
    forall p, equiv_cd_charset (CdUnicodeProp p) (CharSetExt.from_list (Property.code_points_for p)).
  Proof.
    intros p c. simpl. rewrite inb_canonicalized_casesenst by reflexivity. now setoid_rewrite CharSetExt.from_list_contains_inb.
  Qed.

  (* Lemma for CharacterClassEscapes *)
  Lemma equiv_cd_CharacterClassEscape:
    forall esc cd rer,
      RegExpRecord.ignoreCase rer = false ->
      equiv_CharacterClassEscape esc cd ->
      exists a, Semantics.compileToCharSet_ClassAtom (ClassEsc (CCharacterClassEsc esc)) rer = Success a /\
             equiv_cd_charset cd a.
  Proof.
    intros esc cd rer Hcasesenst Hequiv.
    inversion Hequiv as [Heqesc Heqcd | Heqesc Heqcd | Heqesc Heqcd | Heqesc Heqcd | Heqesc Heqcd | Heqesc Heqcd | p Heqesc Heqcd | p Heqesc Heqcd ]; simpl; unfold Coercions.Coercions.wrap_CharSet; eexists; split; try solve[reflexivity].
    - apply equiv_cd_digits.
    - apply equiv_cd_inv. apply equiv_cd_digits.
    - apply equiv_cd_whitespace.
    - apply equiv_cd_inv. apply equiv_cd_whitespace.
    - pose proof wordCharacters_casesenst_eq rer Hcasesenst. unfold Semantics.wordCharacters, Coercions.Coercions.wrap_CharSet in H. simpl in H.
      injection H as H. setoid_rewrite H. apply equiv_cd_wordchar.
    - apply equiv_cd_inv. pose proof wordCharacters_casesenst_eq rer Hcasesenst. unfold Semantics.wordCharacters, Coercions.Coercions.wrap_CharSet in H. simpl in H.
      injection H as H. setoid_rewrite H. apply equiv_cd_wordchar.
    - apply equiv_cd_unicodeprop.
    - apply equiv_cd_inv. apply equiv_cd_unicodeprop.
  Qed.

  (* Lemma for ControlEscapes *)
  Lemma equiv_cd_ControlEscape:
    forall esc cd rer,
      equiv_ControlEscape esc cd ->
      exists a, Semantics.compileToCharSet_ClassAtom (ClassEsc (CCharacterEsc (ControlEsc esc))) rer = Success a /\
             equiv_cd_charset cd a.
  Proof.
    intros esc cd rer Hequiv.
    inversion Hequiv; simpl; unfold Coercions.Coercions.wrap_CharSet; eexists; split; try solve[reflexivity]; unfold Numeric.nat_to_nni; rewrite Character.numeric_pseudo_bij; apply equiv_cd_single.
  Qed.

  (* Lemma for CharacterEscapes *)
  Lemma equiv_cd_CharacterEscape:
    forall esc cd rer,
      equiv_CharacterEscape esc cd ->
      exists a, Semantics.compileToCharSet_ClassAtom (ClassEsc (CCharacterEsc esc)) rer = Success a /\
             equiv_cd_charset cd a.
  Proof.
    intros esc cd rer Hequiv. inversion Hequiv as [esc0 cd0 Hequiv' Heqesc Heqcd0 | l cd0 Hequiv' Heqesc Heqcd0 | Heqesc Heqcd | d1 d2 Heqesc Heqcd | c Heqesc Heqcd | head tail Heqesc Heqcd | hex Heqesc Heqcd | c Heqesc Heqcd].
    - apply equiv_cd_ControlEscape. assumption.
    - inversion Hequiv' as [l0 i Heqi Heql0 Heqcd]. subst cd0 l0.
      simpl. rewrite <- Heqi.
      unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      unfold Numeric.nat_to_nni. rewrite Character.numeric_pseudo_bij. apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      unfold Numeric.nat_to_nni. apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      unfold Numeric.nat_to_nni. rewrite Character.numeric_pseudo_bij. apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      unfold Numeric.nat_to_nni. rewrite Character.numeric_pseudo_bij. apply equiv_cd_single.
  Qed.

  (* Lemma for ClassEscapes *)
  Lemma equiv_cd_ClassEscape:
    forall esc cd rer,
      RegExpRecord.ignoreCase rer = false ->
      equiv_ClassEscape esc cd ->
      exists a, Semantics.compileToCharSet_ClassAtom (ClassEsc esc) rer = Success a /\
             equiv_cd_charset cd a.
  Proof.
    intros esc cd rer Hcasesenst Hequiv. inversion Hequiv as [Heqesc Heqcd | Heqesc Heqcd | |].
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split.
      + reflexivity.
      + unfold Numeric.nat_to_nni. rewrite Character.numeric_pseudo_bij. apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split.
      + reflexivity.
      + unfold Numeric.nat_to_nni. rewrite Character.numeric_pseudo_bij. apply equiv_cd_single.
    - apply equiv_cd_CharacterClassEscape; auto.
    - apply equiv_cd_CharacterEscape; auto.
  Qed.

  (* Lemmas for ClassRanges *)
  Lemma equiv_cd_ClassAtom:
    forall ca cacd rer,
      RegExpRecord.ignoreCase rer = false ->
      equiv_ClassAtom ca cacd ->
      exists a, Semantics.compileToCharSet_ClassAtom ca rer = Success a /\ equiv_cd_charset cacd a.
  Proof.
    intros ca cacd rer Hcasesenst Hequiv.
    inversion Hequiv as [c Heqca Heqcacd | esc cd Hequiv' Heqca Heqcacd].
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. + reflexivity. + apply equiv_cd_single.
    - apply equiv_cd_ClassEscape; assumption.
  Qed.


  Lemma equiv_cd_ClassRanges:
    forall crs cd rer,
      RegExpRecord.ignoreCase rer = false ->
      equiv_ClassRanges crs cd ->
      exists a, Semantics.compileToCharSet crs rer = Success a /\
             equiv_cd_charset cd a.
  Proof.
    intros crs cd rer Hcasesenst Hequiv.
    induction Hequiv as [|ca cacd t tcd Hequiv' Hequiv IH | l h cl ch t tcd Hequivl Hequivh Hl_le_h Hequiv IH].
    - simpl. unfold Coercions.Coercions.wrap_CharSet.
      eexists. split. + reflexivity. + apply equiv_cd_empty.
    - simpl. pose proof equiv_cd_ClassAtom ca cacd rer Hcasesenst Hequiv' as [A [HeqA Hequivatom]].
      rewrite HeqA. simpl.
      destruct IH as [B [HeqB IH]]. rewrite HeqB. simpl.
      unfold Coercions.Coercions.wrap_CharSet. eexists. split. + reflexivity. + now apply equiv_cd_union.
    - simpl.
      pose proof equiv_cd_ClassAtom l (CdSingle cl) rer Hcasesenst Hequivl as [A [HeqA Hequivatoml]].
      pose proof equiv_cd_ClassAtom h (CdSingle ch) rer Hcasesenst Hequivh as [B [HeqB Hequivatomh]].
      rewrite HeqA, HeqB. simpl.
      destruct IH as [C [HeqC IH]]. rewrite HeqC. simpl.
      unfold Semantics.characterRange.
      pose proof equiv_cd_singleton_invn cl A Hequivatoml as HAsingleton.
      pose proof equiv_cd_singleton_invn ch B Hequivatomh as HBsingleton.
      rewrite <- CharSetExt.canonicity in HAsingleton, HBsingleton.
      rewrite HAsingleton, HBsingleton. do 2 rewrite CharSet.singleton_size. simpl.
      do 2 rewrite CharSetExt.singleton_unique. simpl.
      pose proof Hl_le_h as Hl_le_h'. rewrite <- PeanoNat.Nat.leb_le in Hl_le_h'. rewrite Hl_le_h'. simpl.
      unfold Coercions.Coercions.wrap_CharSet. eexists. split.
      + reflexivity.
      + apply equiv_cd_union; auto. do 2 rewrite Character.numeric_pseudo_bij. apply equiv_cd_range. assumption.
  Qed.
End CharDescrCharSet.
