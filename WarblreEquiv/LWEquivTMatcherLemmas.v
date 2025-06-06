From Linden Require Import LWEquivTMatcherDef Tree LindenParameters
  ListLemmas WarblreLemmas Groups GroupMapMS GroupMapLemmas Tactics.
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
    forall (gm: GroupMap.t) (idx: nat) (dir: Direction) resopt1 topt1 resopt2 topt2,
      equiv_results topt1 gm idx dir resopt1 -> equiv_results topt2 gm idx dir resopt2 ->
      equiv_results (tree_choice topt1 topt2) gm idx dir (match_choice resopt1 resopt2).
  Proof.
    intros gm idx dir resopt1 topt1 resopt2 topt2 Hequiv1 Hequiv2.
    unfold tree_choice, match_choice.
    inversion Hequiv1 as [ t1 gm' idx' dir' res1 Hequiv1' Heqt1 Heqgm' Heqidx' Heqdir' Heqres1 |
                         | ].
    2,3: constructor.
    subst gm' idx' dir'.
    inversion Hequiv2 as [ t2 gm' idx' dir' res2 Hequiv2' Heqt2 Heqgm' Heqidx' Heqdir' Heqres2 |
                         | ]; simpl.
    - replace (if (res1 !=? None)%wt then _ else _)
        with (Success (F := MatchError) (if (res1 !=? None)%wt then res1 else res2
             )) by now destruct res1.
      constructor. simpl.
      inversion Hequiv1' as [Hleaf1None Hres1None | gmleaf1 msres1 Hequivgmms Hleaf1Some Hres1Some].
      + simpl. assumption.
      + simpl. constructor. assumption.
    - constructor.
    - (* Something is happening here; may be simplified later *)
      destruct res1; simpl. 2: constructor.
      destruct topt2.
      + simpl. apply Equiv_results. simpl. inversion Hequiv1'. simpl. constructor. assumption.
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

  Definition nat_in_range_dec:
    forall lIncl hExcl i, {lIncl <= i < hExcl} + {~(lIncl <= i < hExcl)}.
  Proof.
    intros. pose proof (Compare_dec.le_dec lIncl i). pose proof (Compare_dec.lt_dec i hExcl).
    destruct H; destruct H0; tauto.
  Defined.

  (* Equivalence of a group map and a MatchState is preserved when performing the same
  capture reset on both sides. *)
  Lemma equiv_gm_ms_reset {F} `{Result.AssertionError F}:
    forall gm ms gm_reset ms_reset parenIndex parenCount cap',
      equiv_groupmap_ms gm ms ->
      List.List.Update.Nat.Batch.update None (MatchState.captures ms)
        (List.List.Range.Nat.Bounds.range (parenIndex + 1 - 1) (parenIndex + parenCount + 1 - 1)) = Success cap' ->
      ms_reset = match_state (MatchState.input ms) (MatchState.endIndex ms) cap' ->
      gm_reset = GroupMap.reset (List.seq (parenIndex + 1) parenCount) gm ->
      equiv_groupmap_ms gm_reset ms_reset.
  Proof.
    intros gm ms gm_reset ms_reset parenIndex parenCount cap' Hgmms Hupdsucc Heqms_reset Heqgm_reset.
    unfold equiv_groupmap_ms. intro gid_prec.
    destruct (nat_in_range_dec (parenIndex + 1 - 1) (parenIndex + parenCount + 1 - 1) gid_prec) as [Hinrange | Houtrange].
    - (* In reset range *)
      assert (Hinrange_linden: parenIndex + 1 <= S gid_prec < parenIndex + parenCount + 1) by lia.
      unfold List.Range.Nat.Bounds.range in Hupdsucc. rewrite range_seq in Hupdsucc.
      replace (parenIndex + parenCount + 1 - 1 - _) with parenCount in Hupdsucc by lia.
      replace (parenIndex + parenCount + 1 - 1) with ((parenIndex + 1 - 1) + parenCount) in Hinrange by lia.
      apply <- List.in_seq in Hinrange.
      replace (GroupMap.find _ gm_reset) with (None (A := GroupMap.range)). 2: {
        symmetry. subst gm_reset. rewrite gm_reset_find. 1: reflexivity.
        apply List.in_seq. lia.
      }
      replace (List.nth gid_prec (MatchState.captures ms_reset) None) with (None (A := CaptureRange)). 2: {
        symmetry. subst ms_reset. simpl.
        pose proof batch_update_1 _ _ _ _ gid_prec Hupdsucc Hinrange None. auto.
      }
      constructor.
    - (* Not in reset range *)
      replace (GroupMap.find (S gid_prec) gm_reset) with (GroupMap.find (S gid_prec) gm). 2: {
        symmetry. subst gm_reset. rewrite gm_reset_find_other. 1: reflexivity.
        rewrite List.in_seq. lia.
      }
      replace (List.nth gid_prec (MatchState.captures ms_reset) None)
        with (List.nth gid_prec (MatchState.captures ms) None). 2: {
        symmetry. subst ms_reset. simpl.
        pose proof batch_update_2 _ _ _ _ gid_prec Hupdsucc.
        specialize_prove H0. { unfold List.Range.Nat.Bounds.range. rewrite range_seq, List.in_seq. lia. }
        apply H0.
      }
      apply Hgmms.
  Qed.
    

End LWEquivTMatcherLemmas.
