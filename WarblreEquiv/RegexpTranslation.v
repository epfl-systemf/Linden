From Warblre Require Import Patterns Result Errors Coercions Notation Base.
From Warblre Require Characters.
From Linden Require Import Regex LindenParameters Chars Groups.
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
  | Equiv_backref: forall (n: nat) (gid: positive_integer),
      equiv_regex' (Patterns.AtomEsc (Patterns.DecimalEsc gid)) (Backreference (positive_to_nat gid)) n
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


  (* Translation function from Warblre to Linden. *)
  Section WarblreToLinden.

    Definition characterClassEsc_to_linden (esc: Patterns.CharacterClassEscape): option char_descr :=
      match esc with
      | Patterns.esc_d => Some CdDigits
      | Patterns.esc_D => Some (CdInv CdDigits)
      | Patterns.esc_s => Some CdWhitespace
      | Patterns.esc_S => Some (CdInv CdWhitespace)
      | Patterns.esc_w => Some CdWordChar
      | Patterns.esc_W => Some (CdInv CdWordChar)
      | Patterns.UnicodeProp _ => None (* Unsupported *)
      | Patterns.UnicodePropNeg _ => None (* Unsupported *)
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
    
    Definition characterEscape_singleCharacter (esc: Patterns.CharacterEscape): option Parameters.Character :=
      match esc with
      | Patterns.ControlEsc esc => Some (controlEsc_singleCharacter esc)
      | Patterns.AsciiControlEsc l => Some (asciiEsc_singleCharacter l)
      | Patterns.esc_Zero => Some (Character.from_numeric_value 0)
      | Patterns.HexEscape d1 d2 => Some (Character.from_numeric_value (HexDigit.to_integer_2 d1 d2))
      | Patterns.UnicodeEsc _ => None (* Unsupported *)
      | Patterns.IdentityEsc _ => None (* Unsupported *)
      end.

    Definition characterEscape_to_linden (esc: Patterns.CharacterEscape): option char_descr :=
      match characterEscape_singleCharacter esc with
      | Some c => Some (CdSingle c)
      | None => None
      end.

    Definition atomesc_to_linden (ae: Patterns.AtomEscape): option regex :=
      match ae with
      | Patterns.DecimalEsc gid => Some (Backreference (positive_to_nat gid))
      | Patterns.ACharacterClassEsc esc => 
          match characterClassEsc_to_linden esc with
          | Some cd => Some (Character cd)
          | None => None
          end
      | Patterns.ACharacterEsc esc => 
          match characterEscape_to_linden esc with
          | Some cd => Some (Character cd)
          | None => None
          end
      | Patterns.GroupEsc gn => None (* TODO *)
      end.

    Definition classEscape_to_linden (esc: Patterns.ClassEscape): option char_descr :=
      match esc with
      | Patterns.esc_b => Some (CdSingle Characters.BACKSPACE)
      | Patterns.esc_Dash => Some (CdSingle Characters.HYPHEN_MINUS)
      | Patterns.CCharacterClassEsc esc => characterClassEsc_to_linden esc
      | Patterns.CCharacterEsc esc => characterEscape_to_linden esc
      end.

    (* Here, the option is not an option monad *)
    Definition classEscape_singleCharacter (esc: Patterns.ClassEscape): option Parameters.Character :=
      match esc with
      | Patterns.esc_b => Some Characters.BACKSPACE
      | Patterns.esc_Dash => Some Characters.HYPHEN_MINUS
      | Patterns.CCharacterClassEsc esc => None
      | Patterns.CCharacterEsc esc => characterEscape_singleCharacter esc
      end.
    
    Definition classAtom_to_linden (ca: Patterns.ClassAtom): option char_descr :=
      match ca with
      | Patterns.SourceCharacter c => Some (CdSingle c)
      | Patterns.ClassEsc esc => classEscape_to_linden esc
      end.

    (* Here, the option is not an option monad *)
    Definition classAtom_singleCharacter (ca: Patterns.ClassAtom): option Parameters.Character :=
      match ca with
      | Patterns.SourceCharacter c => Some c
      | Patterns.ClassEsc esc => classEscape_singleCharacter esc
      end.
    
    (* The first option is an option monad, the second one accounts for the fact that class atoms do not necessarily
    represent single characters *)
    Fixpoint classRanges_to_linden (cr: Patterns.ClassRanges): option (option char_descr) :=
      match cr with
      | Patterns.EmptyCR => Some (Some CdEmpty)
      | Patterns.ClassAtomCR ca t => 
          match classAtom_to_linden ca, classRanges_to_linden t with
          | Some cda, Some (Some cdt) => Some (Some (CdUnion cda cdt))
          | Some _, Some None => Some None
          | _, _ => None
          end
      | Patterns.RangeCR l h t => 
          match classAtom_singleCharacter l, classAtom_singleCharacter h, classRanges_to_linden t with
          | Some cl, Some ch, Some (Some cdt) =>
              if Character.numeric_value cl <=? Character.numeric_value ch then
                Some (Some (CdUnion (CdRange cl ch) cdt))
              else
                Some None
          | Some _, Some _, Some None | None, _, Some _ | _, None, Some _ => Some None
          | _, _, _ => None
          end
      end.
    
    Definition charclass_to_linden (cc: Patterns.CharClass): option (option char_descr) :=
      match cc with
      | Patterns.NoninvertedCC crs => classRanges_to_linden crs
      | Patterns.InvertedCC crs => 
          match classRanges_to_linden crs with
          | Some (Some cd) => Some (Some (CdInv cd))
          | Some None => Some None
          | None => None
          end
      end.

    Definition wquantpref_to_linden (qp: Patterns.QuantifierPrefix): bool -> regex -> regex :=
      match qp with
      | Patterns.Star => (fun greedy => Quantified greedy 0 +∞)
      | Patterns.Plus => (fun greedy => Quantified greedy 1 +∞)
      | Patterns.Question => (fun greedy => Quantified greedy 0 (NoI.N 1))
      | Patterns.RepExact n => (fun greedy => Quantified greedy n (NoI.N 0))
      | Patterns.RepPartialRange n => (fun greedy => Quantified greedy n +∞)
      | Patterns.RepRange mini maxi => (fun greedy => Quantified greedy mini (NoI.N (maxi-mini)))
      end.

    (* First option for unsupported features, second option for invalid regexes *)
    Fixpoint warblre_to_linden (wr: Patterns.Regex) (n: nat): option (option regex) :=
      match wr with
      | Patterns.Empty => Some (Some Epsilon)
      | Patterns.Char chr => Some (Some (Character (CdSingle chr)))
      | Patterns.Dot => Some (Some (Character CdDot))
      | Patterns.AtomEsc ae =>
          match atomesc_to_linden ae with
          | Some lr => Some (Some lr)
          | None => None
          end
      | Patterns.CharacterClass cc => match charclass_to_linden cc with
          | Some (Some cd) => Some (Some (Character cd))
          | Some None => Some None
          | None => None
          end
      | Patterns.Disjunction wr1 wr2 =>
          let lr1 := warblre_to_linden wr1 n in
          let num_groups_lr1 := match lr1 with
          | Some (Some lr1) => num_groups lr1
          | _ => 0
          end in
          let lr2 := warblre_to_linden wr2 (num_groups_lr1 + n) in
          match lr1, lr2 with
          | Some (Some lr1), Some (Some lr2) => Some (Some (Disjunction lr1 lr2))
          | Some None, Some _ | Some _, Some None => Some None
          | None, _ | _, None => None
          end
      | Patterns.Quantified wr (Patterns.Greedy qp) =>
          let quant := wquantpref_to_linden qp in
          let lr := warblre_to_linden wr n in
          match lr with
          | Some (Some lr) => Some (Some (quant true lr))
          | Some None => Some None
          | None => None
          end
      | Patterns.Quantified wr (Patterns.Lazy qp) =>
          let quant := wquantpref_to_linden qp in
          let lr := warblre_to_linden wr n in
          match lr with
          | Some (Some lr) => Some (Some (quant false lr))
          | Some None => Some None
          | None => None
          end
      | Patterns.Seq wr1 wr2 =>
          let lr1 := warblre_to_linden wr1 n in
          let num_groups_lr1 := match lr1 with
          | Some (Some lr1) => num_groups lr1
          | _ => 0
          end in
          let lr2 := warblre_to_linden wr2 (num_groups_lr1 + n) in
          match lr1, lr2 with
          | Some (Some lr1), Some (Some lr2) => Some (Some (Sequence lr1 lr2))
          | Some None, Some _ | Some _, Some None => Some None
          | None, _ | _, None => None
          end
      | Patterns.Group _ wr =>
          let lr := warblre_to_linden wr (S n) in
          match lr with
          | Some (Some lr) => Some (Some (Group (S n) lr))
          | Some None => Some None
          | None => None
          end
      | Patterns.InputStart => Some (Some (Anchor BeginInput))
      | Patterns.InputEnd => Some (Some (Anchor EndInput))
      | Patterns.WordBoundary => Some (Some (Anchor WordBoundary))
      | Patterns.NotWordBoundary => Some (Some (Anchor NonWordBoundary))
      | Patterns.Lookahead wr =>
          let lr := warblre_to_linden wr n in
          match lr with
          | Some (Some lr) => Some (Some (Lookaround LookAhead lr))
          | Some None => Some None
          | None => None
          end
      | Patterns.NegativeLookahead wr =>
          let lr := warblre_to_linden wr n in
          match lr with
          | Some (Some lr) => Some (Some (Lookaround NegLookAhead lr))
          | Some None => Some None
          | None => None
          end
      | Patterns.Lookbehind wr =>
          let lr := warblre_to_linden wr n in
          match lr with
          | Some (Some lr) => Some (Some (Lookaround LookBehind lr))
          | Some None => Some None
          | None => None
          end
      | Patterns.NegativeLookbehind wr =>
          let lr := warblre_to_linden wr n in
          match lr with
          | Some (Some lr) => Some (Some (Lookaround NegLookBehind lr))
          | Some None => Some None
          | None => None
          end
      end.

  End WarblreToLinden.

  Section LindenToWarblre.

    Parameter todo_regex: option Patterns.Regex.

    Definition cd_to_warblre (cd: char_descr): option Patterns.Regex :=
      match cd with
      | CdEmpty => Some (Patterns.CharacterClass (Patterns.NoninvertedCC Patterns.EmptyCR))
      | CdDot => Some Patterns.Dot
      | CdAll => None
      | CdSingle c => Some (Patterns.Char c)
      | CdDigits => Some (Patterns.AtomEsc (Patterns.ACharacterClassEsc Patterns.esc_d))
      | CdWhitespace => Some (Patterns.AtomEsc (Patterns.ACharacterClassEsc Patterns.esc_s))
      | CdWordChar => Some (Patterns.AtomEsc (Patterns.ACharacterClassEsc Patterns.esc_w))
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

End RegexpTranslation.
