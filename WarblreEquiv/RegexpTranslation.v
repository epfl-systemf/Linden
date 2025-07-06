From Warblre Require Import Patterns Result Errors Coercions Notation Base StaticSemantics.
From Warblre Require Characters.
From Linden Require Import Regex LindenParameters Chars Groups.
Import Notation.
Import Result.
Import Result.Notations.
Local Open Scope result_flow.
Require Import List.
Import ListNotations.

(** * Relation defining equivalence between Warblre regexes and Linden regexes *)

Section RegexpTranslation.
  Context `{characterClass: Character.class}.
  Context {unicodeProp: Parameters.Property.class Parameters.Character}.

  (* NamedMap: relating named groups to indices  *)

  Definition patname_eq_dec : forall (x y : Patterns.GroupName), { x = y } + { x <> y }.
  Proof. decide equality. apply Character.eq_dec. Qed.
  Definition patname_eqb (n1 n2:Patterns.GroupName) : bool :=
    if patname_eq_dec n1 n2 then true else false.

  Definition namedmap : Type := list (Patterns.GroupName * nat).
  Definition nameidx (nm:namedmap) (name:Patterns.GroupName) : option nat :=
    SetoidList.findA (fun n => patname_eqb n name) nm.

  (* Computing the named map of a Warblre regex *)
  Fixpoint buildnm' (wr:Patterns.Regex) (nm:namedmap) (n:nat) : namedmap * nat :=
    match wr with
    | Patterns.Empty | Patterns.Char _ | Patterns.Dot | Patterns.AtomEsc _ | Patterns.CharacterClass _
    | Patterns.InputStart | Patterns.InputEnd | Patterns.WordBoundary | Patterns.NotWordBoundary => (nm,n)
    | Patterns.Disjunction wr1 wr2 | Patterns.Seq wr1 wr2 =>
                                       let (nm1,n1) := buildnm' wr1 nm n in
                                       buildnm' wr2 nm1 n1
    | Patterns.Lookahead wr1 | Patterns.NegativeLookahead wr1
    | Patterns.Lookbehind wr1 | Patterns.NegativeLookbehind wr1
    | Patterns.Quantified wr1 _ => buildnm' wr1 nm n
    | Patterns.Group None wr1 => buildnm' wr1 nm (S n)
    | Patterns.Group (Some name) wr1 => buildnm' wr1 ((name,S n)::nm) (S n)
    end.

  Definition buildnm (wr:Patterns.Regex) : namedmap :=
    fst (buildnm' wr [] 0).
  
  (* Computes the number of capture groups of the regex r. *)
  Fixpoint num_groups (r: regex): nat := (* actually len (def_groups r); TODO replace later or prove lemma *)
    match r with
    | Epsilon | Character _ => 0
    | Disjunction r1 r2 => num_groups r1 + num_groups r2
    | Sequence r1 r2 => num_groups r1 + num_groups r2
    | Quantified _ _ _ r1 => num_groups r1
    | Group _ r1 => S (num_groups r1)
    | Lookaround _ r1 => num_groups r1
    | Anchor _ | Backreference _ => 0
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
  | Equiv_UnicodeProp: forall p, equiv_CharacterClassEscape (Patterns.UnicodeProp p) (CdUnicodeProp p)
  | Equiv_UnicodePropNeg: forall p, equiv_CharacterClassEscape (Patterns.UnicodePropNeg p) (CdInv (CdUnicodeProp p))
  .

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

  Definition unicodeCodePoint (head tail: Hex4Digits) :=
    (*>> 1. Let lead be the CharacterValue of HexLeadSurrogate. <<*)
    let lead := StaticSemantics.characterValue_Hex4Digits head in
    (*>> 2. Let trail be the CharacterValue of HexTrailSurrogate. <<*)
    let trail := StaticSemantics.characterValue_Hex4Digits tail in
    (*>> 3. Let cp be UTF16SurrogatePairToCodePoint(lead, trail). <<*)
    let cp := Unicode.utf16SurrogatePair lead trail in
    (*>> 4. Return the numeric value of cp. <<*)
    cp.

  (* CharacterEscape *)
  Inductive equiv_CharacterEscape: Patterns.CharacterEscape -> char_descr -> Prop :=
  | Equiv_ControlEsc: forall esc cd, equiv_ControlEscape esc cd -> equiv_CharacterEscape (Patterns.ControlEsc esc) cd
  | Equiv_AsciiControlEsc: forall l cd, equiv_asciiesc l cd -> equiv_CharacterEscape (Patterns.AsciiControlEsc l) cd
  | Equiv_esc_Zero: equiv_CharacterEscape Patterns.esc_Zero (CdSingle (Character.from_numeric_value 0))
  | Equiv_HexEscape: forall d1 d2: HexDigit, equiv_CharacterEscape (Patterns.HexEscape d1 d2) (CdSingle (Character.from_numeric_value (HexDigit.to_integer_2 d1 d2)))
  | Equiv_IdentityEsc: forall c, equiv_CharacterEscape (Patterns.IdentityEsc c) (CdSingle c)
  | Equiv_UnicodeEsc_Pair: forall head tail, equiv_CharacterEscape (Patterns.UnicodeEsc (Patterns.Pair head tail)) (CdSingle (Character.from_numeric_value (unicodeCodePoint head tail)))
  | Equiv_UnicodeEsc_Lonely: forall hex, equiv_CharacterEscape (Patterns.UnicodeEsc (Patterns.Lonely hex)) (CdSingle (Character.from_numeric_value (StaticSemantics.characterValue_Hex4Digits hex)))
  | Equiv_UnicodeEsc_CodePoint: forall c, equiv_CharacterEscape (Patterns.UnicodeEsc (Patterns.CodePoint c)) (CdSingle c)
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
  Inductive equiv_regex': Patterns.Regex -> regex -> nat -> namedmap -> Prop :=
  | Equiv_empty: forall (n: nat) nm, equiv_regex' Patterns.Empty Epsilon n nm
  | Equiv_char: forall (n: nat) (c: Parameters.Character) nm, equiv_regex' (Patterns.Char c) (Character (Chars.CdSingle c)) n nm
  | Equiv_dot: forall (n: nat) nm, equiv_regex' Patterns.Dot (Character Chars.CdDot) n nm
  | Equiv_backref: forall (n: nat) (gid: positive_integer) nm,
      equiv_regex' (Patterns.AtomEsc (Patterns.DecimalEsc gid)) (Backreference (positive_to_nat gid)) n nm
  | Equiv_named_backref: forall n nm name gid,
      nameidx nm name = Some gid -> 
      equiv_regex' (Patterns.AtomEsc (Patterns.GroupEsc name)) (Backreference gid) n nm
  | Equiv_atom_CharacterClassEscape:
    forall (esc: Patterns.CharacterClassEscape) (cd: char_descr) (n: nat) nm,
      equiv_CharacterClassEscape esc cd ->
      equiv_regex' (Patterns.AtomEsc (Patterns.ACharacterClassEsc esc)) (Character cd) n nm
  | Equiv_atom_CharacterEscape:
    forall (esc: Patterns.CharacterEscape) (cd: char_descr) (n: nat) nm,
      equiv_CharacterEscape esc cd ->
      equiv_regex' (Patterns.AtomEsc (Patterns.ACharacterEsc esc)) (Character cd) n nm
  | Equiv_CharacterClass:
    forall (cc: Patterns.CharClass) (cd: char_descr) (n: nat) nm,
      equiv_CharClass cc cd ->
      equiv_regex' (Patterns.CharacterClass cc) (Character cd) n nm
  | Equiv_disj: forall n wr1 wr2 lr1 lr2 nm,
      equiv_regex' wr1 lr1 n nm -> equiv_regex' wr2 lr2 (num_groups lr1 + n) nm ->
      equiv_regex' (Patterns.Disjunction wr1 wr2) (Disjunction lr1 lr2) n nm
  | Equiv_seq: forall n wr1 wr2 lr1 lr2 nm,
      equiv_regex' wr1 lr1 n nm -> equiv_regex' wr2 lr2 (num_groups lr1 + n) nm ->
      equiv_regex' (Patterns.Seq wr1 wr2) (Sequence lr1 lr2) n nm
  | Equiv_quant:
    forall n wr lr wquant lquant wgreedylazy greedy nm,
      equiv_regex' wr lr n nm ->
      equiv_quantifier wquant lquant -> equiv_greedylazy wgreedylazy greedy ->
      equiv_regex' (Patterns.Quantified wr (wgreedylazy wquant)) (lquant greedy lr) n nm
  | Equiv_group: forall n wr lr nm,
      equiv_regex' wr lr (S n) nm ->
      equiv_regex' (Patterns.Group None wr) (Group (S n) lr) n nm
  | Equiv_named_group: forall name n wr lr nm,
      nameidx nm name = Some (S n) ->
      equiv_regex' wr lr (S n) nm ->
      equiv_regex' (Patterns.Group (Some name) wr) (Group (S n) lr) n nm
  | Equiv_lk: forall n wr lr wlk llk nm, equiv_regex' wr lr n nm -> equiv_lookaround wlk llk -> equiv_regex' (wlk wr) (Lookaround llk lr) n nm
  | Equiv_anchor: forall n wr lanchor nm, equiv_anchor wr lanchor -> equiv_regex' wr (Anchor lanchor) n nm
  .


  (* Equivalence of root regexes. *)
  Definition equiv_regex (wreg: Patterns.Regex) (lreg: regex) := equiv_regex' wreg lreg 0 (buildnm wreg).


  (* Translation function from Warblre to Linden. *)
  Section WarblreToLinden.

    Inductive wl_transl_error: Type :=
      | WlMalformed
      | WlUnsupported.

    Definition characterClassEsc_to_linden (esc: Patterns.CharacterClassEscape): Result char_descr wl_transl_error :=
      match esc with
      | Patterns.esc_d => Success CdDigits
      | Patterns.esc_D => Success (CdInv CdDigits)
      | Patterns.esc_s => Success CdWhitespace
      | Patterns.esc_S => Success (CdInv CdWhitespace)
      | Patterns.esc_w => Success CdWordChar
      | Patterns.esc_W => Success (CdInv CdWordChar)
      | Patterns.UnicodeProp p => Success (CdUnicodeProp p)
      | Patterns.UnicodePropNeg p => Success (CdInv (CdUnicodeProp p))
      end.

    Definition controlEsc_singleCharacter (esc: Patterns.ControlEscape): Parameters.Character :=
      match esc with
      | Patterns.esc_f => Characters.FORM_FEED
      | Patterns.esc_n => Characters.LINE_FEED
      | Patterns.esc_r => Characters.CARRIAGE_RETURN
      | Patterns.esc_t => Characters.CHARACTER_TABULATION
      | Patterns.esc_v => Characters.LINE_TABULATION
      end.

    Definition asciiEsc_singleCharacter (l: AsciiLetter): Parameters.Character :=
      let n := NonNegInt.modulo (AsciiLetter.numeric_value l) 32 in
      Character.from_numeric_value n.
    
    Definition characterEscape_singleCharacter (esc: Patterns.CharacterEscape): Result Parameters.Character wl_transl_error :=
      match esc with
      | Patterns.ControlEsc esc => Success (controlEsc_singleCharacter esc)
      | Patterns.AsciiControlEsc l => Success (asciiEsc_singleCharacter l)
      | Patterns.esc_Zero => Success (Character.from_numeric_value 0)
      | Patterns.HexEscape d1 d2 => Success (Character.from_numeric_value (HexDigit.to_integer_2 d1 d2))
      | Patterns.UnicodeEsc (Patterns.Pair head tail) => Success (Character.from_numeric_value (unicodeCodePoint head tail))
      | Patterns.UnicodeEsc (Patterns.Lonely hex) => Success (Character.from_numeric_value (StaticSemantics.characterValue_Hex4Digits hex))
      | Patterns.UnicodeEsc (Patterns.CodePoint c) => Success c
      | Patterns.IdentityEsc c => Success c
      end.

    Definition characterEscape_to_linden (esc: Patterns.CharacterEscape): Result char_descr wl_transl_error :=
      let! c =<< characterEscape_singleCharacter esc in
      Success (CdSingle c).

    Definition atomesc_to_linden (ae: Patterns.AtomEscape) (nm:namedmap): Result regex wl_transl_error :=
      match ae with
      | Patterns.DecimalEsc gid => Success (Backreference (positive_to_nat gid))
      | Patterns.ACharacterClassEsc esc => 
          let! cd =<< characterClassEsc_to_linden esc in
          Success (Character cd)
      | Patterns.ACharacterEsc esc => 
          let! cd =<< characterEscape_to_linden esc in
          Success (Character cd)
      | Patterns.GroupEsc gn =>
          match nameidx nm gn with
          | None => Error WlUnsupported
          | Some gid => Success (Backreference gid)
          end
      end.

    Definition classEscape_to_linden (esc: Patterns.ClassEscape): Result char_descr wl_transl_error :=
      match esc with
      | Patterns.esc_b => Success (CdSingle Characters.BACKSPACE)
      | Patterns.esc_Dash => Success (CdSingle Characters.HYPHEN_MINUS)
      | Patterns.CCharacterClassEsc esc => characterClassEsc_to_linden esc
      | Patterns.CCharacterEsc esc => characterEscape_to_linden esc
      end.

    Definition classEscape_singleCharacter (esc: Patterns.ClassEscape): Result Parameters.Character wl_transl_error :=
      match esc with
      | Patterns.esc_b => Success Characters.BACKSPACE
      | Patterns.esc_Dash => Success Characters.HYPHEN_MINUS
      | Patterns.CCharacterClassEsc esc => Error WlMalformed
      | Patterns.CCharacterEsc esc => characterEscape_singleCharacter esc
      end.
    
    Definition classAtom_to_linden (ca: Patterns.ClassAtom): Result char_descr wl_transl_error :=
      match ca with
      | Patterns.SourceCharacter c => Success (CdSingle c)
      | Patterns.ClassEsc esc => classEscape_to_linden esc
      end.

    Definition classAtom_singleCharacter (ca: Patterns.ClassAtom): Result Parameters.Character wl_transl_error :=
      match ca with
      | Patterns.SourceCharacter c => Success c
      | Patterns.ClassEsc esc => classEscape_singleCharacter esc
      end.

    Fixpoint classRanges_to_linden (cr: Patterns.ClassRanges): Result char_descr wl_transl_error :=
      match cr with
      | Patterns.EmptyCR => Success CdEmpty
      | Patterns.ClassAtomCR ca t => 
          let! cda =<< classAtom_to_linden ca in
          let! cdt =<< classRanges_to_linden t in
          Success (CdUnion cda cdt)
      | Patterns.RangeCR l h t => 
          let! cl =<< classAtom_singleCharacter l in
          let! ch =<< classAtom_singleCharacter h in
          let! cdt =<< classRanges_to_linden t in
          if Character.numeric_value cl <=? Character.numeric_value ch then
            Success (CdUnion (CdRange cl ch) cdt)
          else
            Error WlMalformed
      end.
    
    Definition charclass_to_linden (cc: Patterns.CharClass): Result char_descr wl_transl_error :=
      match cc with
      | Patterns.NoninvertedCC crs => classRanges_to_linden crs
      | Patterns.InvertedCC crs => 
          let! cd =<< classRanges_to_linden crs in
          Success (CdInv cd)
      end.

    Definition wquantpref_to_linden (qp: Patterns.QuantifierPrefix): Result (bool -> regex -> regex) wl_transl_error :=
      match qp with
      | Patterns.Star => Success (fun greedy => Quantified greedy 0 +∞)
      | Patterns.Plus => Success (fun greedy => Quantified greedy 1 +∞)
      | Patterns.Question => Success (fun greedy => Quantified greedy 0 (NoI.N 1))
      | Patterns.RepExact n => Success (fun greedy => Quantified greedy n (NoI.N 0))
      | Patterns.RepPartialRange n => Success (fun greedy => Quantified greedy n +∞)
      | Patterns.RepRange mini maxi => 
          if mini <=? maxi then
            Success (fun greedy => Quantified greedy mini (NoI.N (maxi-mini)))
          else
            Error WlMalformed
      end.

    (* checking that we get the expected index *)
    Definition assert_idx_eq (i1 i2:nat) : Result unit wl_transl_error :=
      if (Nat.eqb i1 i2) then Success tt else Error WlMalformed.

    (* First option for unsupported features, second option for invalid regexes *)
    Fixpoint warblre_to_linden (wr: Patterns.Regex) (n: nat) (nm:namedmap): Result regex wl_transl_error :=
      match wr with
      | Patterns.Empty => Success Epsilon
      | Patterns.Char chr => Success (Character (CdSingle chr))
      | Patterns.Dot => Success (Character CdDot)
      | Patterns.AtomEsc ae => atomesc_to_linden ae nm
      | Patterns.CharacterClass cc => 
          let! cd =<< charclass_to_linden cc in
          Success (Character cd)
      | Patterns.Disjunction wr1 wr2 =>
          let! lr1 =<< warblre_to_linden wr1 n nm in
          let! lr2 =<< warblre_to_linden wr2 (num_groups lr1 + n) nm in
          Success (Disjunction lr1 lr2)
      | Patterns.Quantified wr (Patterns.Greedy qp) =>
          let! quant =<< wquantpref_to_linden qp in
          let! lr =<< warblre_to_linden wr n nm in
          Success (quant true lr)
      | Patterns.Quantified wr (Patterns.Lazy qp) =>
          let! quant =<< wquantpref_to_linden qp in
          let! lr =<< warblre_to_linden wr n nm in
          Success (quant false lr)
      | Patterns.Seq wr1 wr2 =>
          let! lr1 =<< warblre_to_linden wr1 n nm in
          let! lr2 =<< warblre_to_linden wr2 (num_groups lr1 + n) nm in
          Success (Sequence lr1 lr2)
      | Patterns.Group None wr =>
          let! lr =<< warblre_to_linden wr (S n) nm in
          Success (Group (S n) lr)
      | Patterns.Group (Some name) wr =>
          match (nameidx nm name) with
          | Some idx =>
              let! _ =<< assert_idx_eq idx (S n) in
              let! lr =<< warblre_to_linden wr (S n) nm in
              Success (Group (S n) lr)
          | _ => Error WlMalformed
          end
      | Patterns.InputStart => Success (Anchor BeginInput)
      | Patterns.InputEnd => Success (Anchor EndInput)
      | Patterns.WordBoundary => Success (Anchor WordBoundary)
      | Patterns.NotWordBoundary => Success (Anchor NonWordBoundary)
      | Patterns.Lookahead wr =>
          let! lr =<< warblre_to_linden wr n nm in
          Success (Lookaround LookAhead lr)
      | Patterns.NegativeLookahead wr =>
          let! lr =<< warblre_to_linden wr n nm in
          Success (Lookaround NegLookAhead lr)
      | Patterns.Lookbehind wr =>
          let! lr =<< warblre_to_linden wr n nm in
          Success (Lookaround LookBehind lr)
      | Patterns.NegativeLookbehind wr =>
          let! lr =<< warblre_to_linden wr n nm in
          Success (Lookaround NegLookBehind lr)
      end.

  End WarblreToLinden.

  Section LindenToWarblre.

    Definition cd_to_warblre (cd: char_descr): option Patterns.Regex :=
      match cd with
      | CdEmpty => Some (Patterns.CharacterClass (Patterns.NoninvertedCC Patterns.EmptyCR))
      | CdDot => Some Patterns.Dot
      | CdAll => None
      | CdSingle c => Some (Patterns.Char c)
      | CdDigits => Some (Patterns.AtomEsc (Patterns.ACharacterClassEsc Patterns.esc_d))
      | CdWhitespace => Some (Patterns.AtomEsc (Patterns.ACharacterClassEsc Patterns.esc_s))
      | CdWordChar => Some (Patterns.AtomEsc (Patterns.ACharacterClassEsc Patterns.esc_w))
      | CdUnicodeProp p => Some (Patterns.AtomEsc (Patterns.ACharacterClassEsc (Patterns.UnicodeProp p)))
      | CdInv cd => None (* any way to translate CdInv easily? *)
      | CdRange l h => Some (Patterns.CharacterClass (Patterns.NoninvertedCC (Patterns.RangeCR (Patterns.SourceCharacter l) (Patterns.SourceCharacter h) Patterns.EmptyCR)))
      | CdUnion cd1 cd2 => None (* any way to translate this easily? *)
      end.

    Definition to_warblre_qp (min: nat) (delta: non_neg_integer_or_inf) :=
      match delta with
      | +∞ => Patterns.RepPartialRange min
      | NoI.N delta => Patterns.RepRange min (min + delta)
      end.

    Fixpoint linden_to_warblre (lr: regex) (n: nat): option Patterns.Regex :=
      match lr with
      | Epsilon => Some Patterns.Empty
      | Character cd => cd_to_warblre cd
      | Disjunction r1 r2 =>
          let wr1_opt := linden_to_warblre r1 n in
          let wr2_opt := linden_to_warblre r2 (num_groups r1 + n) in
          match wr1_opt, wr2_opt with
          | Some wr1, Some wr2 => Some (Patterns.Disjunction wr1 wr2)
          | _, _ => None
          end
      | Sequence r1 r2 =>
          let wr1_opt := linden_to_warblre r1 n in
          let wr2_opt := linden_to_warblre r2 (num_groups r1 + n) in
          match wr1_opt, wr2_opt with
          | Some wr1, Some wr2 => Some (Patterns.Seq wr1 wr2)
          | _, _ => None
          end
      | Quantified greedy min delta r =>
          let greedylazy :=
            if greedy then Patterns.Greedy else Patterns.Lazy
          in
          let qp := to_warblre_qp min delta in
          let wr_opt := linden_to_warblre r n in
          match wr_opt with
          | Some wr => Some (Patterns.Quantified wr (greedylazy qp))
          | None => None
          end
      | Lookaround lk r =>
          let wr_opt := linden_to_warblre r n in
          let wlk :=
            match lk with
            | LookAhead => Patterns.Lookahead
            | LookBehind => Patterns.Lookbehind
            | NegLookAhead => Patterns.NegativeLookahead
            | NegLookBehind => Patterns.NegativeLookbehind
            end
          in
          match wr_opt with
          | Some wr => Some (wlk wr)
          | None => None
          end
      | Group id r =>
          if id !=? S n then
            None
          else
            let wr_opt := linden_to_warblre r (S n) in
            match wr_opt with
            | Some wr => Some (Patterns.Group None wr)
            | None => None
            end
      | Anchor a =>
          match a with
          | BeginInput => Some Patterns.InputStart
          | EndInput => Some Patterns.InputEnd
          | WordBoundary => Some Patterns.WordBoundary
          | NonWordBoundary => Some Patterns.NotWordBoundary
          end
      | Backreference gid => 
          match NonNegInt.to_positive gid with
          | Success gid => Some (Patterns.AtomEsc (Patterns.DecimalEsc gid))
          | Error _ => None
          end
      end.
  
  End LindenToWarblre.

  Section TranslationSoundness.

    Lemma characterClassEsc_to_linden_sound:
      forall esc cd,
        characterClassEsc_to_linden esc = Success cd ->
        equiv_CharacterClassEscape esc cd.
    Proof.
      intro esc. destruct esc; simpl; try discriminate.
      all: intros cd H; injection H as <-; constructor.
    Qed.

    Lemma controlEsc_singleCharacter_sound:
      forall esc, equiv_ControlEscape esc (CdSingle (controlEsc_singleCharacter esc)).
    Proof.
      intro esc. destruct esc; simpl; constructor.
    Qed.

    Lemma asciiEsc_singleCharacter_sound:
      forall l, equiv_asciiesc l (CdSingle (asciiEsc_singleCharacter l)).
    Proof.
      intro l. unfold asciiEsc_singleCharacter. constructor. reflexivity.
    Qed.

    Lemma characterEscape_to_linden_sound:
      forall esc cd,
        characterEscape_to_linden esc = Success cd ->
        equiv_CharacterEscape esc cd.
    Proof.
      intro esc. destruct esc; try discriminate; simpl; unfold characterEscape_to_linden; simpl.
      5: destruct seq; simpl.
      all: intros cd H; injection H as <-; try constructor.
      - apply controlEsc_singleCharacter_sound.
      - apply asciiEsc_singleCharacter_sound.
    Qed.

    Lemma atomesc_to_linden_sound:
      forall ae lr n nm,
        atomesc_to_linden ae nm = Success lr ->
        equiv_regex' (Patterns.AtomEsc ae) lr n nm.
    Proof.
      intro ae. destruct ae.
      - simpl. intros lr gid nm H. injection H as <-. constructor.
      - simpl. intros lr n nm.
        destruct characterClassEsc_to_linden as [cd|] eqn:Hcd; try discriminate. simpl.
        intro H. injection H as <-. constructor. apply characterClassEsc_to_linden_sound. auto.
      - simpl. intros lr n nm.
        destruct characterEscape_to_linden as [cd|] eqn:Hcd; try discriminate. simpl.
        intro H. injection H as <-. constructor. apply characterEscape_to_linden_sound. auto.
      - simpl. intros lr n nm H. destruct (nameidx nm id) eqn:NAME; [|discriminate].
        inversion H. subst. constructor. auto.
    Qed.

    Lemma wquantpref_to_linden_sound:
      forall qp quant,
        wquantpref_to_linden qp = Success quant ->
        equiv_quantifier qp quant.
    Proof.
      intros qp quant H. destruct qp.
      1-5: injection H as <-; constructor.
      simpl in H. destruct Nat.leb eqn:Hle; try discriminate.
      injection H as <-. constructor. apply PeanoNat.Nat.leb_le. auto.
    Qed.

    Lemma classEscape_to_linden_sound:
      forall esc cda,
        classEscape_to_linden esc = Success cda ->
        equiv_ClassEscape esc cda.
    Proof.
      intros esc cda. destruct esc; simpl.
      - intro H. injection H as <-. constructor.
      - intro H. injection H as <-. constructor.
      - intro H. constructor. apply characterClassEsc_to_linden_sound. auto.
      - intro H. constructor. apply characterEscape_to_linden_sound. auto.
    Qed.

    Lemma classAtom_to_linden_sound:
      forall ca cda,
        classAtom_to_linden ca = Success cda ->
        equiv_ClassAtom ca cda.
    Proof.
      intro ca. destruct ca.
      - simpl. intros cda H. injection H as <-. constructor.
      - simpl. intros cda H. constructor. apply classEscape_to_linden_sound. auto.
    Qed.

    Lemma characterEscape_singleCharacter_sound:
      forall esc clh,
        characterEscape_singleCharacter esc = Success clh ->
        equiv_CharacterEscape esc (CdSingle clh).
    Proof.
      intros esc clh. destruct esc; simpl; try discriminate.
      5: destruct seq; simpl.
      all: intro H; injection H as <-; constructor.
      - apply controlEsc_singleCharacter_sound.
      - apply asciiEsc_singleCharacter_sound.
    Qed.

    Lemma classEscape_singleCharacter_sound:
      forall esc clh,
        classEscape_singleCharacter esc = Success clh ->
        equiv_ClassEscape esc (CdSingle clh).
    Proof.
      intros esc clh. destruct esc; simpl; try discriminate.
      - intro H. injection H as <-. constructor.
      - intro H. injection H as <-. constructor.
      - intro H. constructor. apply characterEscape_singleCharacter_sound. auto.
    Qed.

    Lemma classAtom_singleCharacter_sound:
      forall lh clh,
        classAtom_singleCharacter lh = Success clh ->
        equiv_ClassAtom lh (CdSingle clh).
    Proof.
      intros lh clh. destruct lh.
      - simpl. intro H. injection H as <-. constructor.
      - simpl. intro H. constructor. apply classEscape_singleCharacter_sound. auto.
    Qed.

    Lemma classRanges_to_linden_sound:
      forall crs cd,
        classRanges_to_linden crs = Success cd ->
        equiv_ClassRanges crs cd.
    Proof.
      intro crs. induction crs.
      - simpl. intros cd H. injection H as <-. constructor.
      - simpl. intro cd.
        destruct classAtom_to_linden as [cda|] eqn:Hcda; try discriminate; simpl.
        destruct classRanges_to_linden as [cdt|] eqn:Hcdt; try discriminate; simpl.
        intro H. injection H as <-.
        constructor; auto. apply classAtom_to_linden_sound. auto.
      - simpl. intro cd.
        destruct classAtom_singleCharacter as [cl|] eqn:Hcl; try discriminate; simpl.
        destruct (classAtom_singleCharacter h) as [ch|] eqn:Hch; try discriminate; simpl.
        destruct classRanges_to_linden as [cdt|] eqn:Hcdt; try discriminate; simpl.
        destruct Nat.leb eqn:Hle; try discriminate; simpl.
        apply PeanoNat.Nat.leb_le in Hle.
        intro H. injection H as <-. constructor; auto; apply classAtom_singleCharacter_sound; auto.
    Qed.

    Lemma charclass_to_linden_sound:
      forall cc cd,
        charclass_to_linden cc = Success cd ->
        equiv_CharClass cc cd.
    Proof.
      intro cc. destruct cc.
      - simpl. intros cd H. constructor. apply classRanges_to_linden_sound. auto.
      - simpl. destruct classRanges_to_linden as [cdsub|] eqn:Hcdsub; simpl; try discriminate.
        intros cd H. injection H as <-. constructor. apply classRanges_to_linden_sound. auto.
    Qed.

    Lemma warblre_to_linden_sound:
      forall wr lr n nm,
        warblre_to_linden wr n nm = Success lr ->
        equiv_regex' wr lr n nm.
    Proof.
      intro wr. induction wr.
      - simpl. intros lr n nm H. injection H as <-. apply Equiv_empty.
      - simpl. intros lr n nm H. injection H as <-. apply Equiv_char.
      - simpl. intros lr n nm H. injection H as <-. apply Equiv_dot.
      - simpl. intros lr n nm H. apply atomesc_to_linden_sound. auto.
      - simpl. intros lr n nm.
        destruct charclass_to_linden as [cd|] eqn:Hcd; simpl; try discriminate.
        intro H. injection H as <-. constructor. apply charclass_to_linden_sound. auto.
      - simpl. intros lr n nm.
        destruct warblre_to_linden as [lr1|] eqn:Hwl1; try discriminate. simpl.
        destruct (warblre_to_linden wr2 _) as [lr2|] eqn:Hwl2; try discriminate. simpl.
        intro H. injection H as <-.
        apply Equiv_disj; auto.
      - simpl. intros lr n nm.
        destruct q as [qp|qp].
        + destruct wquantpref_to_linden as [quant|] eqn:Hquant; try discriminate. simpl.
          destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate. simpl.
          intro H. injection H as <-.
          apply Equiv_quant; auto. 2: constructor.
          apply wquantpref_to_linden_sound. auto.
        + destruct wquantpref_to_linden as [quant|] eqn:Hquant; try discriminate. simpl.
          destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate. simpl.
          intro H. injection H as <-.
          apply Equiv_quant; auto. 2: constructor.
          apply wquantpref_to_linden_sound. auto.
      - simpl. intros lr n nm.
        destruct warblre_to_linden as [lr1|] eqn:Hwl1; try discriminate. simpl.
        destruct (warblre_to_linden wr2 _) as [lr2|] eqn:Hwl2; try discriminate. simpl.
        intro H. injection H as <-. constructor; auto.
      - simpl. intros lr n nm.
        destruct name as [name|]; simpl.
        2: { destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate.
             simpl. inversion 1. constructor. auto. }
        destruct (nameidx nm name) eqn:NAME; [|inversion 1].
        unfold assert_idx_eq. simpl. destruct (Nat.eqb n0 (S n)) eqn:IDX; [|inversion 1].
        apply PeanoNat.Nat.eqb_eq in IDX.
        destruct warblre_to_linden as [lrsub|] eqn:Hwl; [|inversion 1].
        simpl. inversion 1. subst. constructor; auto.
      - simpl. intros lr n nm H. injection H as <-. constructor. constructor.
      - simpl. intros lr n nm H. injection H as <-. constructor. constructor.
      - simpl. intros lr n nm H. injection H as <-. constructor. constructor.
      - simpl. intros lr n nm H. injection H as <-. constructor. constructor.
      - simpl. intros lr n nm.
        destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate. simpl.
        intro H. injection H as <-. constructor; auto; constructor.
      - simpl. intros lr n nm.
        destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate. simpl.
        intro H. injection H as <-. constructor; auto; constructor.
      - simpl. intros lr n nm.
        destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate. simpl.
        intro H. injection H as <-. constructor; auto; constructor.
      - simpl. intros lr n nm.
        destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate. simpl.
        intro H. injection H as <-. constructor; auto; constructor.
    Qed.

  End TranslationSoundness.

End RegexpTranslation.
