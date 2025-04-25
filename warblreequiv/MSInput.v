From Coq Require Import List ZArith Lia.
From Warblre Require Import Notation Parameters.
Import Notation.
From Linden Require Import Chars LindenParameters TMatching.


(** * Definitions and lemmas linking Warblre MatchStates with Linden inputs *)


(* Advance match state by one character *)
Definition advance_ms {H} `{CharacterMarker H} (s: MatchState): MatchState :=
  {|
    MatchState.input := MatchState.input s;
    MatchState.endIndex := (MatchState.endIndex s + 1)%Z;
    MatchState.captures := MatchState.captures s |}.


(* We say that a MatchState ms matches an input Input next pref when they represent the same
   string and the same position; in other words, when rev pref ++ next = MatchState.input ms
   and len pref = MatchState.endIndex ms. *)
Inductive ms_matches_inp: MatchState -> input -> Prop :=
| Ms_matches_inp: forall (s: string) (end_ind: nat) cap (next pref: string),
    List.length pref = end_ind -> List.rev pref ++ next = s ->
    ms_matches_inp {| MatchState.input := s; MatchState.endIndex := Z.of_nat end_ind;
                                             MatchState.captures := cap |} (Input next pref).

(* Inversion lemma: when a MatchState matches an input, we have MatchState.input ms = List.rev pref ++ next. *)
Lemma ms_matches_inp_invinp: forall ms pref next, ms_matches_inp ms (Input next pref) -> MatchState.input ms = List.rev pref ++ next.
Proof.
  intros ms pref next Hmatches. inversion Hmatches. symmetry. assumption.
Qed.

(* Linking the suffixes of corresponding MatchStates and Linden inputs. *)
Lemma ms_suffix_current_str: forall ms inp, ms_matches_inp ms inp -> current_str inp = ms_suffix ms.
Proof.
  intros ms inp Hmatches.
  inversion Hmatches as [s end_ind cap next pref Hlpref Hcompats Heqms Heqinp].
  simpl. unfold ms_suffix. simpl.
  rewrite Nat2Z.id in *.
  assert (length (rev pref) = end_ind) as Hlrevpref. {
    subst end_ind. apply rev_length.
  }
  pose proof firstn_app end_ind (rev pref) next as H.
  subst end_ind.
  replace (length pref - length (rev pref)) with 0 in H by lia. rewrite Hcompats in H.
  change (firstn 0 next) with (@nil Parameters.Character) in H.
  rewrite <- Hlrevpref in H at 2. rewrite firstn_all in H. rewrite app_nil_r in H.
  rewrite <- H in Hcompats.
  pose proof firstn_skipn (length pref) s as H2.
  rewrite <- H2 in Hcompats at 2.
  eapply app_inv_head. apply Hcompats.
Qed.


(* Definition of when an input is compatible with (i.e. represents) a given input string str0. *)
Inductive input_compat: input -> string -> Prop :=
| Input_compat: forall next pref str0, List.rev pref ++ next = str0 -> input_compat (Input next pref) str0.

(* A transitivity lemma: a MatchState ms that matches an input inp that is itself compatible with a string str0 has str0 as its input string. *)
Lemma inp_compat_ms_str0:
  forall (str0: string) (inp: input),
    input_compat inp str0 ->
    forall ms, ms_matches_inp ms inp -> MatchState.input ms = str0.
Proof.
  intros str0 [next pref] Hcompat ms Hmatches.
  apply ms_matches_inp_invinp in Hmatches.
  inversion Hcompat. congruence.
Qed.

(* As a consequence, if two MatchStates ms1 and ms2 respectively match inputs inp1 and inp2
   that are both compatible with str0, then ms1 and ms2 have the same input string. *)
Lemma inp_compat_ms_same_inp:
  forall (str0: string) (inp1 inp2: input),
    input_compat inp1 str0 -> input_compat inp2 str0 ->
    forall ms1 ms2,
      ms_matches_inp ms1 inp1 -> ms_matches_inp ms2 inp2 ->
      MatchState.input ms1 = MatchState.input ms2.
Proof.
  intros str0 [next1 pref1] [next2 pref2] Hcompat1 Hcompat2 ms1 ms2 Hmatches1 Hmatches2.
  transitivity str0.
  - eapply inp_compat_ms_str0.
    + apply Hcompat1.
    + apply Hmatches1.
  - symmetry. eapply inp_compat_ms_str0.
    + apply Hcompat2.
    + apply Hmatches2.
Qed.

(* Whether a MatchState matches an input does not depend on its captures. *)
Lemma ms_matches_inp_capchg:
  forall str endInd cap cap' inp,
    ms_matches_inp (match_state str endInd cap) inp ->
    ms_matches_inp (match_state str endInd cap') inp.
Proof.
  intros str endInd cap cap' inp Hmatches.
  inversion Hmatches. now constructor.
Qed.
