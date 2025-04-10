From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List Program.Wf.
From Linden Require Import Tree LindenParameters CharsWarblre TMatching Chars Regex Semantics RegexpTranslation.
From Warblre Require Import Patterns Result Notation Errors Node RegExpRecord Base Coercions Semantics Typeclasses.
Import Patterns.
Import Result.Result.
Import Result.Notations.
Import Result.Notations.Boolean.
Import Coercions.
Import Notation.

Local Open Scope result_flow.

(*Definition state_of_input (inp: input) : MatchState :=
    let '(Input next pref) := inp in
    let end_ind := List.length pref in
    let s := List.rev pref ++ next in
    {|
        MatchState.input := s;
        MatchState.endIndex := Z.of_nat end_ind;
        MatchState.captures := nil
    |}.*)

Inductive ms_matches_inp: MatchState -> input -> Prop :=
| Ms_matches_inp: forall (s: string) (end_ind: nat) cap (next pref: string),
    List.length pref = end_ind -> List.rev pref ++ next = s ->
    ms_matches_inp {| MatchState.input := s; MatchState.endIndex := Z.of_nat end_ind;
        MatchState.captures := cap |} (Input next pref).

Definition tMC_is_tree (tmc: TMatcherContinuation) (reg: regex) (cont: continuation) (inp: input) :=
    forall s, ms_matches_inp s inp -> match tmc s with
    | Error _ => True (* finer modeling? *)
    | Success t => is_tree reg cont inp t
    end.

Section Main.
  Context (s0: string).

  Inductive input_compat: input -> Prop :=
  | Input_compat: forall next pref, List.rev pref ++ next = s0 -> input_compat (Input next pref).

  Theorem tmatcher_bt: forall reg ctx rer,
    let wreg' := to_warblre_regex reg in
    match wreg' with
    | Error _ => True
    | Success wreg =>
      match tCompileSubPattern wreg ctx rer forward with
      | Error _ => True
      | Success tm => forall (tmc: TMatcherContinuation) (regc: regex) (cont: continuation),
        (forall inp, input_compat inp -> tMC_is_tree tmc regc cont inp) ->
        forall inp, input_compat inp -> tMC_is_tree (fun s => tm s tmc) reg (Areg regc::cont) inp
      end
    end.
  Proof.
    intros reg ctx rer.
    revert ctx.
    induction reg.
    - simpl. intros _.
      intros.
      intro. intro.
      specialize (H inp H0 s H1).
      destruct (tmc s) eqn:?; simpl; try exact I.
      apply tree_pop_reg. assumption.
    - simpl.
      