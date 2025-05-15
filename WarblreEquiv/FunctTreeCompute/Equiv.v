From Linden Require Import EquivDef RegexpTranslation Regex LindenParameters Semantics.
From Warblre Require Import Parameters Semantics RegExpRecord Patterns
  Node Result Notation Typeclasses List Base.
Import Patterns.
Import Result.Notations.
Import Notation.
From Coq Require Import ZArith PeanoNat.

Local Open Scope result_flow.

Section Equiv.
  Context `{characterClass: Character.class}.

  Theorem equiv:
    forall (rer: RegExpRecord) (lroot: regex) (wroot: Regex)
      (* Assume that we do not ignore case, *)
      (Hcasesenst: RegExpRecord.ignoreCase rer = false)
      (* that we do not consider line ends and starts to be input ends and starts, respectively, *)
      (Hnomultiline: RegExpRecord.multiline rer = false)
      (* and that dot matches all characters. *)
      (Hdotall: RegExpRecord.dotAll rer = true)
      (* Let lroot and wroot be a pair of equivanent regexes. *)
      (root_equiv: equiv_regex wroot lroot),
      (* Then for any sub-regex wreg of the root Warblre regex, *)
    forall (wreg: Regex) (lreg: regex) ctx
      (Hroot: Root wroot (wreg, ctx))
      (* and any Linden regex lreg that is equivalent to this sub-regex with the right number of left capturing parentheses before, *)
      (Hequiv: equiv_regex' wreg lreg (StaticSemantics.countLeftCapturingParensBefore wreg ctx)),
      forall m dir
        (* if compileSubPattern with direction dir yields a Matcher for regex wreg, *)
        (Hcompsucc: Semantics.compileSubPattern wreg ctx rer dir = Success m),
        (* then this Matcher is equivalent to the regex lreg and direction dir. *)
        equiv_matcher m lreg dir.
  Proof.
    do 12 intro.
    remember (StaticSemantics.countLeftCapturingParensBefore _ _) as n in Hequiv.
    revert ctx Hroot Heqn.
    induction Hequiv as [
        n |
        n c |
        n |
        esc cd n Hequivesc |
        esc cd n Hequivesc |
        cc cd n Hequivcc |
        n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
        n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
        n wr lr wquant lquant wgreedylazy greedy Hequiv IH Hequivquant Hequivgreedy |
        name n wr lr Hequiv IH |
        n wr lr wlk llk Hequiv IH Hequivlk |
        n wr lanchor Hanchequiv
    ].

    - (* Epsilon *)
      intros ctx _ _ m dir. simpl.
      intro. injection Hcompsucc as <-.
      unfold equiv_matcher. intros mc gl act Hequivcont _.
      unfold equiv_cont. intros gm ms inp res fuel t Hgmms Hgmgl Hmsinp Hmcsucc.
      destruct fuel as [|fuel]; try discriminate.
      simpl.
      intro Hsubtreesucc.
      eauto using Hequivcont.
  
    - (* Character *)
      intros ctx Hroot Heqn m dir Hcompsucc.
      injection Hcompsucc as <-.
      unfold equiv_matcher. intros mc gl act Hequivcont Hgldisj.
      unfold equiv_cont. intros gm ms inp res fuel t Hgmms Hgmgl Hmsinp.
      unfold Semantics.characterSetMatcher.
      destruct (((if (dir ==? forward)%wt then _ else _) <? 0)%Z || _)%bool eqn:Hoob; simpl.
      + (* Out of bounds *)
        intro Hres. injection Hres as <-. destruct fuel as [|fuel]; try discriminate. simpl.
        replace (Chars.read_char (Chars.CdSingle c) inp dir) with (@None (Character * Chars.input)) by admit.
        intro Heqt. injection Heqt as <-. simpl. constructor.
      + (* In bounds *)
        destruct List.Indexing.Int.indexing as [chr|] eqn:Hgetchr; simpl; try discriminate.
        destruct CharSet.CharSetExt.exist_canonicalized eqn:Hexist; simpl.
        * admit.
        * admit.
    
    - (* Dot *)
      admit.
    
    - (* AtomEsc (ACharacterClassEsc esc) *)
      admit.
    
    - (* AtomEsc (ACharacterEsc esc) *)
      admit.
    
    - (* CharacterClass *)
      admit.

    - (* Disjunction TODO *)
      admit.

    - (* Sequence TODO *)
      admit.

    - (* Quantified *)
      admit.

    - (* Group *)
      admit.

    - (* Lookaround *)
      admit.

    - (* Anchor *)
      admit.
  Admitted.
End Equiv.
