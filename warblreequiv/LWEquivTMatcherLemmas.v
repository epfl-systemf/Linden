From Linden Require Import LWEquivTMatcherDef TreeMSInterp Tree LindenParameters ListLemmas.
From Warblre Require Import Result Notation Base Errors Parameters List.
Import Notation.
Import Result.Notations.
From Coq Require Import Lia.

Local Open Scope result_flow.

(** * Lemmas for 1st part of equivalence proof *)

Section LWEquivTMatcherLemmas.
  Context `{characterClass: Character.class}.

  (* Function that generates the subtree corresponding to a choice between two subtrees. *)
  Definition tree_choice {F} `{Result.AssertionError F} (topt1 topt2: Result tree F) :=
    let! z =<< topt1 in
    let! z' =<< topt2 in
    Success (Choice z z').


  (* Function that performs the choice between two results. *)
  Definition match_choice {F} `{Result.AssertionError F} (resopt1 resopt2: Result (option MatchState) F) :=
    let! z =<< resopt1 in
    if (z !=? None)%wt then
      Success z
    else
      resopt2.

  (* Equivalence lemma for the case of a choice between two branches. *)
  Lemma equiv_choice:
    forall (ms: MatchState) (gl: open_groups) (dir: Direction) resopt1 topt1 resopt2 topt2,
      equiv_results topt1 ms gl dir resopt1 -> equiv_results topt2 ms gl dir resopt2 ->
      equiv_results (tree_choice topt1 topt2) ms gl dir (match_choice resopt1 resopt2).
  Proof.
    intros ms gl dir resopt1 topt1 resopt2 topt2 Hequiv1 Hequiv2.
    unfold tree_choice, match_choice.
    inversion Hequiv1 as [ t1 ms' gl' dir' res1 Hequiv1' Heqt1 Heqms' Heqgl' Heqdir' Heqres1 |
                         | ].
    2,3: constructor.
    subst ms' gl' dir'.
    inversion Hequiv2 as [ t2 ms' gl' dir' res2 Hequiv2' Heqt2 Heqms' Heqgl' Heqdir' Heqres2 |
                         | ]; simpl.
    - replace (if (res1 !=? None)%wt then _ else _)
        with (Success (F := MatchError) (if (res1 !=? None)%wt then res1 else res2
             )) by now destruct res1.
      constructor. simpl.
      rewrite <- Hequiv1'. rewrite <- Hequiv2'.
      now destruct res1.
    - constructor.
    - (* Something is happening here; may be simplified later *)
      destruct res1; simpl. 2: constructor.
      destruct topt2.
      + simpl. constructor. simpl. rewrite <- Hequiv1'. reflexivity.
      + constructor.
  Qed.


  (* Lemma for swapping function application and monad unwrapping *)

  (* Applying the functions after unwrapping both results *)
  Definition apply_after_choice {F} `{Result.AssertionError F} (f1 f2: tree -> tree) (topt1 topt2: Result tree F) : Result tree F :=
    let! t1 =<< topt1 in
    let! t2 =<< topt2 in
    Success (Choice (f1 t1) (f2 t2)).

  (* Applying the first function as soon as the first result is unwrapped *)
  Definition apply_before_choice {F} `{Result.AssertionError F} (f1 f2: tree -> tree) (topt1 topt2: Result tree F) : Result tree F :=
    let! t1 =<<
      let! t1 =<< topt1 in
      Success (f1 t1)
    in
    let! t2 =<<
      let! t2 =<< topt2 in
      Success (f2 t2)
    in
    Success (Choice t1 t2).

  (* The two ways of doing give the same results. *)
  Lemma func_monad_swap {F} `{Result.AssertionError F}:
    forall topt1 topt2 (f1 f2: tree -> tree),
      apply_after_choice f1 f2 topt1 topt2 = apply_before_choice f1 f2 topt1 topt2.
  Proof.
    intros topt1 topt2 f1 f2.
    destruct topt1; destruct topt2; simpl; reflexivity.
  Qed.


  (* A simple identity lemma on the result monad. *)
  Lemma monad_id {T F} `{Result.AssertionError F}:
    forall res: Result T F,
      (let! x =<< res in Success x) = res.
  Proof.
    intro res.
    now destruct res.
  Qed.


  (* The capture reset defined in TreeMSInterp.v does the same thing as the capture reset used in Warblre. *)
  Lemma capture_reset_lw_same:
    forall (ms ms_reset: MatchState) (parenIndex parenCount: nat) (cap': list (option CaptureRange)),
      ms_reset = match_state (MatchState.input ms) (MatchState.endIndex ms) cap' ->
      List.Update.Nat.Batch.update None (MatchState.captures ms) (List.Range.Nat.Bounds.range (parenIndex + 1 - 1) (parenIndex + parenCount + 1 - 1)) = Success cap' ->
      reset_groups_ms (F := MatchError) (List.seq (parenIndex + 1) parenCount) ms = ms_reset.
  Proof.
    intros ms ms_reset parenIndex parenCount cap' Heqms_reset Hupdatesucc.
    unfold reset_groups_ms.
    destruct ms.
    rewrite <- List.List.Range.Nat.Length.range_seq.
    unfold List.List.Range.Nat.Bounds.range in Hupdatesucc.
    rewrite decr_range by lia.
    replace (parenIndex + parenCount + 1 - 1 - (parenIndex + 1 - 1)) with parenCount in Hupdatesucc by lia.
    simpl in Hupdatesucc.
    rewrite Hupdatesucc.
    simpl in *.
    congruence.
  Qed.
End LWEquivTMatcherLemmas.
