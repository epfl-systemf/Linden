From Warblre Require Import Patterns Result Errors Coercions Notation Base.
From Warblre Require Characters.
From Linden Require Import Regex LindenParameters Chars.
Import Notation.
Import Result.
Import Result.Notations.
Local Open Scope result_flow.

(** * Relation defining equivalence between Warblre regexes and Linden regexes *)

Section RegexpTranslation.
  Context `{characterClass: Character.class}.
  
  (* Computes the number of capture groups of the regex r. *)
  Fixpoint num_groups (r: regex): nat := (* actually len (def_groups r); TODO replace later or prove lemma *)
    match r with
    | Epsilon | Character _ => 0
    | Disjunction r1 r2 => num_groups r1 + num_groups r2
    | Sequence r1 r2 => num_groups r1 + num_groups r2
    | Quantified _ _ _ r1 => num_groups r1
    | Group _ r1 => S (num_groups r1)
    | Lookaround _ r1 => num_groups r1
    | Anchor _ => 0
    end.

  (* Equivalence of greedy/lazy quantifier prefixes. *)
  Inductive equiv_greedylazy: (Patterns.QuantifierPrefix -> Patterns.Quantifier) -> bool -> Prop :=
  | Equiv_greedy: equiv_greedylazy Patterns.Greedy true
  | Equiv_lazy: equiv_greedylazy Patterns.Lazy false.

  (* Equivalence of quantifiers. *)
  Inductive equiv_quantifier: Patterns.QuantifierPrefix -> (bool -> regex -> regex) -> Prop :=
  | Equiv_star: equiv_quantifier Patterns.Star (fun greedy => Quantified greedy 0 +∞)
  | Equiv_plus: equiv_quantifier Patterns.Plus (fun greedy => Quantified greedy 1 +∞)
  | Equiv_question: equiv_quantifier Patterns.Question (fun greedy => Quantified greedy 0 (NoI.N 1))
  | Equiv_repexact: forall n, equiv_quantifier (Patterns.RepExact n) (fun greedy => Quantified greedy n (NoI.N 0))
  | Equiv_reppartialrange: forall n, equiv_quantifier (Patterns.RepPartialRange n) (fun greedy => Quantified greedy n +∞)
  | Equiv_reprange: forall mini maxi, mini <= maxi -> equiv_quantifier (Patterns.RepRange mini maxi) (fun greedy => Quantified greedy mini (NoI.N (maxi-mini))).

  (* Equivalence of lookarounds. *)
  Inductive equiv_lookaround: (Patterns.Regex -> Patterns.Regex) -> lookaround -> Prop :=
  | Equiv_lookahead: equiv_lookaround Patterns.Lookahead LookAhead
  | Equiv_neglookahead: equiv_lookaround Patterns.NegativeLookahead NegLookAhead
  | Equiv_lookbehind: equiv_lookaround Patterns.Lookbehind LookBehind
  | Equiv_neglookbehind: equiv_lookaround Patterns.NegativeLookbehind NegLookBehind.

  (* Equivalence of anchors. *)
  Inductive equiv_anchor: Patterns.Regex -> anchor -> Prop :=
  | Equiv_input_start: equiv_anchor Patterns.InputStart BeginInput
  | Equiv_input_end: equiv_anchor Patterns.InputEnd EndInput
  | Equiv_word_boundary: equiv_anchor Patterns.WordBoundary WordBoundary
  | Equiv_non_word_boundary: equiv_anchor Patterns.NotWordBoundary NonWordBoundary
  .


  (** ** Equivalence of AtomEscapes that correspond to character classes (not backreferences). *)
  (* CharacterClassEscape *)
  Inductive equiv_CharacterClassEscape: Patterns.CharacterClassEscape -> char_descr -> Prop :=
  | Equiv_esc_d: equiv_CharacterClassEscape Patterns.esc_d CdDigits
  | Equiv_esc_D: equiv_CharacterClassEscape Patterns.esc_D (CdInv CdDigits)
  | Equiv_esc_s: equiv_CharacterClassEscape Patterns.esc_s CdWhitespace
  | Equiv_esc_S: equiv_CharacterClassEscape Patterns.esc_S (CdInv CdWhitespace)
  | Equiv_esc_w: equiv_CharacterClassEscape Patterns.esc_w CdWordChar
  | Equiv_esc_W: equiv_CharacterClassEscape Patterns.esc_W (CdInv CdWordChar)
  .
  (* TODO Unicode properties *)

  (* ControlEscape *)
  Inductive equiv_ControlEscape: Patterns.ControlEscape -> char_descr -> Prop :=
  | Equiv_esc_f: equiv_ControlEscape Patterns.esc_f (CdSingle Characters.FORM_FEED)
  | Equiv_esc_n: equiv_ControlEscape Patterns.esc_n (CdSingle Characters.LINE_FEED)
  | Equiv_esc_r: equiv_ControlEscape Patterns.esc_r (CdSingle Characters.CARRIAGE_RETURN)
  | Equiv_esc_t: equiv_ControlEscape Patterns.esc_t (CdSingle Characters.CHARACTER_TABULATION)
  | Equiv_esc_v: equiv_ControlEscape Patterns.esc_v (CdSingle Characters.LINE_TABULATION).

  (* AsciiControlEsc *)
  Inductive equiv_asciiesc: AsciiLetter -> char_descr -> Prop :=
  | Equiv_asciiesc:
    forall l n,
      n = NonNegInt.modulo (AsciiLetter.numeric_value l) 32 ->
      equiv_asciiesc l (CdSingle (Character.from_numeric_value n))
  .

  (* CharacterEscape *)
  Inductive equiv_CharacterEscape: Patterns.CharacterEscape -> char_descr -> Prop :=
  | Equiv_ControlEsc: forall esc cd, equiv_ControlEscape esc cd -> equiv_CharacterEscape (Patterns.ControlEsc esc) cd
  | Equiv_AsciiControlEsc: forall l cd, equiv_asciiesc l cd -> equiv_CharacterEscape (Patterns.AsciiControlEsc l) cd
  | Equiv_esc_Zero: equiv_CharacterEscape Patterns.esc_Zero (CdSingle (Character.from_numeric_value 0))
  | Equiv_HexEscape: forall d1 d2: HexDigit, equiv_CharacterEscape (Patterns.HexEscape d1 d2) (CdSingle (Character.from_numeric_value (HexDigit.to_integer_2 d1 d2)))
  (* | Equiv_UnicodeEsc: TODO | Equiv_IdentityEsc: TODO *)
  .


  (** ** Equivalence of character classes *)
  Inductive equiv_ClassEscape: Patterns.ClassEscape -> char_descr -> Prop :=
  | Equiv_esc_b: equiv_ClassEscape Patterns.esc_b (CdSingle Characters.BACKSPACE)
  | Equiv_esc_Dash: equiv_ClassEscape Patterns.esc_Dash (CdSingle Characters.HYPHEN_MINUS)
  | Equiv_CCharacterClassEsc: forall esc cd, equiv_CharacterClassEscape esc cd -> equiv_ClassEscape (Patterns.CCharacterClassEsc esc) cd
  | Equiv_CCharacterEsc: forall esc cd, equiv_CharacterEscape esc cd -> equiv_ClassEscape (Patterns.CCharacterEsc esc) cd.

  Inductive equiv_ClassAtom: Patterns.ClassAtom -> char_descr -> Prop :=
  | Equiv_SourceCharacter: forall c: Parameters.Character, equiv_ClassAtom (Patterns.SourceCharacter c) (CdSingle c)
  | Equiv_ClassEsc: forall esc cd, equiv_ClassEscape esc cd -> equiv_ClassAtom (Patterns.ClassEsc esc) cd.

  Inductive equiv_ClassRanges: Patterns.ClassRanges -> char_descr -> Prop :=
  | Equiv_EmptyCR: equiv_ClassRanges Patterns.EmptyCR CdEmpty
  | Equiv_ClassAtomCR: forall ca cacd t tcd, equiv_ClassAtom ca cacd -> equiv_ClassRanges t tcd -> equiv_ClassRanges (Patterns.ClassAtomCR ca t) (CdUnion cacd tcd)
  | Equiv_RangeCR:
    forall l h cl ch t tcd,
      equiv_ClassAtom l (CdSingle cl) -> equiv_ClassAtom h (CdSingle ch) ->
      Character.numeric_value cl <= Character.numeric_value ch ->
      equiv_ClassRanges t tcd ->
      equiv_ClassRanges (Patterns.RangeCR l h t) (CdUnion (CdRange cl ch) tcd).

  Inductive equiv_CharClass: Patterns.CharClass -> char_descr -> Prop :=
  | Equiv_NoninvertedCC: forall crs cd, equiv_ClassRanges crs cd -> equiv_CharClass (Patterns.NoninvertedCC crs) cd
  | Equiv_InvertedCC: forall crs cd, equiv_ClassRanges crs cd -> equiv_CharClass (Patterns.InvertedCC crs) (CdInv cd).


  (* equiv_regex' wreg lreg n means that the two regexes wreg and lreg are equivalent, where the number of left capturing parentheses before wreg/lreg is n. *)
  Inductive equiv_regex': Patterns.Regex -> regex -> nat -> Prop :=
  | Equiv_empty: forall n: nat, equiv_regex' Patterns.Empty Epsilon n
  | Equiv_char: forall (n: nat) (c: Parameters.Character), equiv_regex' (Patterns.Char c) (Character (Chars.CdSingle c)) n
  | Equiv_dot: forall n: nat, equiv_regex' Patterns.Dot (Character Chars.CdDot) n
  | Equiv_atom_CharacterClassEscape:
    forall (esc: Patterns.CharacterClassEscape) (cd: char_descr) (n: nat),
      equiv_CharacterClassEscape esc cd ->
      equiv_regex' (Patterns.AtomEsc (Patterns.ACharacterClassEsc esc)) (Character cd) n
  | Equiv_atom_CharacterEscape:
    forall (esc: Patterns.CharacterEscape) (cd: char_descr) (n: nat),
      equiv_CharacterEscape esc cd ->
      equiv_regex' (Patterns.AtomEsc (Patterns.ACharacterEsc esc)) (Character cd) n
  | Equiv_CharacterClass:
    forall (cc: Patterns.CharClass) (cd: char_descr) (n: nat),
      equiv_CharClass cc cd ->
      equiv_regex' (Patterns.CharacterClass cc) (Character cd) n
  | Equiv_disj: forall n wr1 wr2 lr1 lr2,
      equiv_regex' wr1 lr1 n -> equiv_regex' wr2 lr2 (num_groups lr1 + n) ->
      equiv_regex' (Patterns.Disjunction wr1 wr2) (Disjunction lr1 lr2) n
  | Equiv_seq: forall n wr1 wr2 lr1 lr2,
      equiv_regex' wr1 lr1 n -> equiv_regex' wr2 lr2 (num_groups lr1 + n) ->
      equiv_regex' (Patterns.Seq wr1 wr2) (Sequence lr1 lr2) n
  | Equiv_quant:
    forall n wr lr wquant lquant wgreedylazy greedy,
      equiv_regex' wr lr n ->
      equiv_quantifier wquant lquant -> equiv_greedylazy wgreedylazy greedy ->
      equiv_regex' (Patterns.Quantified wr (wgreedylazy wquant)) (lquant greedy lr) n
  | Equiv_group: forall name n wr lr, equiv_regex' wr lr (S n) -> equiv_regex' (Patterns.Group name wr) (Group (S n) lr) n
  | Equiv_lk: forall n wr lr wlk llk, equiv_regex' wr lr n -> equiv_lookaround wlk llk -> equiv_regex' (wlk wr) (Lookaround llk lr) n
  | Equiv_anchor: forall n wr lanchor, equiv_anchor wr lanchor -> equiv_regex' wr (Anchor lanchor) n
  .


  (* Equivalence of root regexes. *)
  Definition equiv_regex (wreg: Patterns.Regex) (lreg: regex) := equiv_regex' wreg lreg 0.
End RegexpTranslation.
