From Linden Require Import Equiv EquivDef LindenParameters RegexpTranslation
  Chars Tree Semantics FunctionalSemantics Groups GroupMapMS Regex
  EquivLemmas Utils MSInput Tactics ComputeIsTree GroupMapLemmas FunctionalUtils.
From Warblre Require Import Patterns RegExpRecord Parameters Semantics
  Result Base Notation Match.
From Coq Require Import List Lia PeanoNat ZArith DecidableClass.
Import Match.
Import Notation.
Import ListNotations.
Import Patterns.
Import Result.
Import Result.Notations.

Local Open Scope result_flow.

(** * Main equivalence theorems, linking everything together *)

Section EquivMain.
  Context `{characterClass: Character.class}.

  (** ** Some initialization results *)
  Section InitState.

    (* Initial match state corresponding to a string, an index and a RegExpRecord. *)
    Definition init_match_state (str0: string) (idx: nat) (rer: RegExpRecord): MatchState :=
      let cap := List.repeat undefined (RegExpRecord.capturingGroupsCount rer) in
      match_state str0 (Z.of_nat idx) cap.
    
    (* Such an initial match state is equivalent to the empty group map... *)
    Lemma init_ms_equiv_empty:
      forall str0 idx rer, equiv_groupmap_ms GroupMap.empty (init_match_state str0 idx rer).
    Proof.
      intros str0 idx rer. unfold equiv_groupmap_ms.
      intro gid_prec. rewrite gm_find_empty. unfold init_match_state. simpl.
      rewrite nth_repeat. constructor.
    Qed.

    (* ... and to the empty open group list. *)
    Lemma empty_gm_equiv_empty_gl:
      group_map_equiv_open_groups GroupMap.empty nil.
    Proof.
      unfold group_map_equiv_open_groups. intros gid idx. rewrite gm_find_empty.
      split; try discriminate. intro H. inversion H.
    Qed.

    (* The initial input corresponding to a string str0 is compatible with str0. *)
    Lemma init_input_compat:
      forall str0, input_compat (init_input str0) str0.
    Proof.
      intro str0. unfold init_input. constructor. reflexivity.
    Qed.

    (* The initial input corresponding to a string str0 and the initial match state
       corresponding to str0 and index 0 match each other. *)
    Lemma init_ms_matches_inp:
      forall str0 rer,
        ms_matches_inp (init_match_state str0 0 rer) (init_input str0).
    Proof.
      intros str0 rer. unfold init_match_state, init_input. constructor; reflexivity.
    Qed.

  End InitState.


  (* Computing the RegExpRecord corresponding to the flags supported by our equivalence
     proof and containing the right number of capturing groups. *)
  Definition computeRer (wroot: Regex): RegExpRecord :=
    {|
      RegExpRecord.ignoreCase := false;
      RegExpRecord.multiline := false;
      RegExpRecord.dotAll := true;
      RegExpRecord.unicode := tt;
      RegExpRecord.capturingGroupsCount := StaticSemantics.countLeftCapturingParensWithin wroot nil
    |}.
  

  (** ** Plugging the identity MatcherContinuation into a Matcher compiled from some root regexp *)
  Theorem equiv_matcher_idmcont_compsucc:
    forall wroot lroot rer m,
      (* For all pairs of equivalent Warblre and Linden regexes, *)
      equiv_regex wroot lroot ->
      rer = computeRer wroot ->
      (* if compiling the Warblre regex into a Matcher m succeeds, *)
      Semantics.compileSubPattern wroot nil rer forward = Success m ->
      forall str0,
        (* then plugging the identity MatcherContinuation into the Matcher m yields a
           MatcherContinuation that is equivalent to matching the Linden regex, under any input string. *)
        equiv_cont (fun ms => m ms id_mcont) nil (forbidden_groups lroot) [Areg lroot] forward str0 rer.
  Proof.
    intros wroot lroot rer m Hequiv Heqrer Hcompsucc str0.
    pose proof equiv rer lroot wroot as Hequivm.
    unfold equiv_matcher in Hequivm.
    replace (forbidden_groups lroot) with (forbidden_groups lroot ++ []) by apply app_nil_r.
    unfold computeRer in Heqrer. subst rer. simpl in *.
    eapply Hequivm; eauto.
    - constructor.
    - apply Hequiv.
    - apply id_equiv.
    - apply open_groups_disjoint_nil_l.
    - apply List.Disjoint_nil_r.
  Qed.

  (** ** Corollary assuming that both compiling the regex and matching a string do not yield errors. *)
  Corollary equiv_main':
    forall wroot lroot rer m,
      (* For all pairs of equivalent Warblre and Linden regexes, *)
      equiv_regex wroot lroot ->
      rer = computeRer wroot ->
      (* if compiling the Warblre regex into a matcher m succeeds, *)
      Semantics.compilePattern wroot rer = Success m ->
      (* then for any input string str0, *)
      forall str0 res t,
        (* if running m on str0 successfully yields a result res, *)
        m str0 0 = Success res ->
        (* then letting t be the priority tree corresponding to matching the Linden regex
           on the string str0, *)
        t = compute_tr [Areg lroot] (init_input str0) GroupMap.empty forward ->
        (* this tree respects the Linden semantics and *)
        is_tree [Areg lroot] (init_input str0) GroupMap.empty forward t /\
        (* the result res is equivalent to the first branch of the tree. *)
        equiv_groupmap_ms_opt (first_branch t) res.
  Proof.
    intros wroot lroot rer m Hequiv Heqrer Hcompsucc str0 res t Heqres Heqt.
    pose proof equiv_matcher_idmcont_compsucc wroot lroot rer as Hequivm.
    unfold Semantics.compilePattern in Hcompsucc.
    destruct Semantics.compileSubPattern as [msp|]; simpl in *; try discriminate.
    injection Hcompsucc as <-.
    replace (0 <=? length str0) with true in Heqres.
    2: { symmetry. apply Nat.leb_le. lia. }
    simpl in *.
    specialize (Hequivm msp Hequiv Heqrer eq_refl str0).
    unfold equiv_cont in Hequivm.
    set (fuel := 1 + actions_fuel [Areg lroot] (init_input str0) forward).
    set (ms0 := init_match_state str0 0 rer). change (match_state _ _ _) with ms0 in Heqres.
    change (fun y : MatchState => _) with id_mcont in Heqres.
    specialize (Hequivm GroupMap.empty ms0 (init_input str0) res fuel).
    pose proof functional_terminates [Areg lroot] (init_input str0) GroupMap.empty forward fuel as Hcomputetreesucc.
    specialize_prove Hcomputetreesucc by lia.
    specialize (Hequivm t).
    specialize_prove Hequivm by apply init_input_compat.
    specialize_prove Hequivm by apply init_ms_equiv_empty.
    specialize_prove Hequivm by apply empty_gm_equiv_empty_gl.
    specialize_prove Hequivm by apply init_ms_matches_inp.
    specialize_prove Hequivm. { apply ms_valid_wrt_checks_Areg, ms_valid_wrt_checks_nil. }
    specialize_prove Hequivm by apply empty_gm_valid.
    specialize_prove Hequivm by apply noforb_empty.
    specialize (Hequivm Heqres).
    assert (Hcompute: compute_tree [Areg lroot] (init_input str0) GroupMap.empty forward fuel = Some t). {
      unfold compute_tr in Heqt. unfold Nat.add in fuel. unfold fuel in Hcomputetreesucc.
      destruct compute_tree.
      - f_equal. congruence.
      - contradiction.
    }
    specialize (Hequivm Hcompute).
    split.
    - apply compute_is_tree with (fuel := fuel); auto.
      apply inp_valid_checks_Areg, inp_valid_checks_nil.
    - exact Hequivm.
  Qed.

  (** ** Main theorem *)
  Corollary equiv_main:
    forall wroot lroot rer str0,
      (* For any pair of equivalent Linden and Warblre regexes, *)
      equiv_regex wroot lroot ->
      rer = computeRer wroot ->
      (* such that the Warblre regex passes the early errors check, *)
      EarlyErrors.Pass_Regex wroot nil ->
      exists m res,
        (* compiling the Warblre regex successfully yields a matcher m, *)
        Semantics.compilePattern wroot rer = Success m /\
        (* for any input string str0, running m on str0 yields some result res, *)
        m str0 0 = Success res /\
        (* and letting t be the priority tree corresponding to matching the Linden regex on str0, *)
        forall t, t = compute_tr [Areg lroot] (init_input str0) GroupMap.empty forward ->
          (* this tree respects the Linden semantics and *)
          is_tree [Areg lroot] (init_input str0) GroupMap.empty forward t /\
          (* the result res is equivalent to the first branch of this tree. *)
          equiv_groupmap_ms_opt (first_branch t) res.
  Proof.
    intros wroot lroot rer str0 Hequiv Heqrer HearlyErrors.
    pose proof Compile.compilePattern_success wroot rer as Hcompilesucc.
    assert (Hrercapvalid: StaticSemantics.countLeftCapturingParensWithin wroot [] = RegExpRecord.capturingGroupsCount rer). {
      subst rer. unfold computeRer. simpl. reflexivity.
    }
    specialize (Hcompilesucc Hrercapvalid HearlyErrors). destruct Hcompilesucc as [m Hcompilesucc].
    exists m.
    pose proof Match.no_failure wroot rer str0 0 m HearlyErrors Hrercapvalid Hcompilesucc as Hresnofail.
    pose proof Match.termination wroot rer str0 0 m HearlyErrors Hrercapvalid Hcompilesucc as Hresterminates.
    specialize (Hresnofail ltac:(lia)).
    destruct (m str0 0) as [res|[]] eqn:Heqres.
    2,3: contradiction.
    exists res. split; [|split]; auto.
    intros t Heqt. eapply equiv_main'; eauto.
  Qed.

End EquivMain.
