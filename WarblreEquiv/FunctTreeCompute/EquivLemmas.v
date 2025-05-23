From Linden Require Import Regex GroupMapMS LindenParameters Groups Tree Chars Semantics MSInput EquivDef.
From Warblre Require Import Parameters List Notation Result Typeclasses Base Errors.
From Coq Require Import List ZArith.
Import ListNotations.
Import Notation.
Import Result.Notations.

Section EquivLemmas.
  Context `{characterClass: Character.class}.

  (* Validity wrt checks in a list of actions `act` implies validity wrt checks in the tail of `act`. *)
  Lemma ms_valid_wrt_checks_tail:
    forall act acts ms dir,
    ms_valid_wrt_checks ms (act::acts) dir -> ms_valid_wrt_checks ms acts dir.
  Proof.
    intros act acts ms dir Hvalid inp Hin.
    apply Hvalid. now right.
  Qed.


  (* Inductive definition that relates a regex to its parent regex. *)
  Inductive ChildRegex: regex -> regex -> Prop :=
  | Child_Disjunction_left: forall r1 r2, ChildRegex r1 (Disjunction r1 r2)
  | Child_Disjunction_right: forall r1 r2, ChildRegex r2 (Disjunction r1 r2)
  | Child_Sequence_left: forall r1 r2, ChildRegex r1 (Sequence r1 r2)
  | Child_Sequence_right: forall r1 r2, ChildRegex r2 (Sequence r1 r2)
  | Child_Quantified: forall greedy min delta r, ChildRegex r (Quantified greedy min delta r)
  | Child_Lookaround: forall lk r, ChildRegex r (Lookaround lk r)
  | Child_Group: forall id r, ChildRegex r (Group id r).

  (* The groups defined in a child regex are included in those defined in the parent regex. *)
  Lemma child_groups_incl_parent:
    forall child parent, ChildRegex child parent ->
      forall gid, In gid (def_groups child) -> In gid (def_groups parent).
  Proof.
    intros child parent Hchild. inversion Hchild; intros gid Hinchild; simpl; auto using in_or_app.
  Qed.

  (* Corollary: disjointness from the list of groups of a parent regex implies disjointness from the list of groups of any child regex. *)
  Lemma disj_parent_disj_child:
    forall child parent, ChildRegex child parent ->
      forall gl, open_groups_disjoint gl (def_groups parent) -> open_groups_disjoint gl (def_groups child).
  Proof.
    intros child parent Hchild gl Hgldisjparent.
    unfold open_groups_disjoint. intros gid idx Hingl Hinchild.
    unfold open_groups_disjoint, "~" in Hgldisjparent. 
    eauto using Hgldisjparent, child_groups_incl_parent.
  Qed.

  (* Equivalence of a group map gm with a MatchState ms is preserved by resetting the same groups on both sides. *)
  Lemma equiv_gm_ms_reset {F} `{Result.AssertionError F}:
    forall gm ms parenIndex parenCount cap' msreset gidl gmreset
      (Hresetsucc: List.Update.Nat.Batch.update None (MatchState.captures ms)
        (List.Range.Nat.Bounds.range (parenIndex + 1 - 1)
          (parenIndex + parenCount + 1 - 1)) = Success cap')
      (Heqmsreset: msreset = match_state (MatchState.input ms) (MatchState.endIndex ms) cap')
      (Heqgidl: gidl = List.seq (parenIndex + 1) parenCount)
      (Heqgmreset: gmreset = GroupMap.reset gidl gm)
      (Hequiv: equiv_groupmap_ms gm ms),
      equiv_groupmap_ms gmreset msreset.
  Proof.
  Admitted.

  (* Resetting a list of groups that is disjoint from the list of open groups preserves equivalence to the list of open groups. *)
  Lemma equiv_open_groups_reset:
    forall gl gidl gm gmreset
      (Hgldisj: open_groups_disjoint gl gidl)
      (Hequiv: group_map_equiv_open_groups gm gl)
      (Heqreset: gmreset = GroupMap.reset gidl gm),
      group_map_equiv_open_groups gmreset gl.
  Proof.
  Admitted.

  (* Linking advance_idx with advance_input *)
  Lemma advance_idx_advance_input:
    forall inp inp' dir,
      advance_input inp dir = Some inp' ->
      Tree.advance_idx (idx inp) dir = idx inp'.
  Proof.
  Admitted.

  (* Lemma for closing a group *)
  Lemma equiv_gm_ms_close_group:
    forall ms ms' inp inp' gm' n gl dir (rres: Result (option CaptureRange) MatchError) r cap' str0
      (Hmsinp: ms_matches_inp ms inp)
      (Hinpcompat: input_compat inp str0)
      (Hms'inp': ms_matches_inp ms' inp')
      (Hinp'compat: input_compat inp' str0)
      (Hgm'ms': equiv_groupmap_ms gm' ms')
      (Hgm'gl': group_map_equiv_open_groups gm' ((S n, idx inp)::gl))
      (Heqrres: rres = 
        if (dir ==? forward)%wt
        then
         if negb (MatchState.endIndex ms <=? MatchState.endIndex ms')%Z
         then Error Errors.MatchError.AssertionFailed
         else
          Coercions.wrap_option Errors.MatchError.type CaptureRange
            (Coercions.CaptureRange_or_undefined
               (capture_range (MatchState.endIndex ms) (MatchState.endIndex ms')))
        else
         if negb (MatchState.endIndex ms' <=? MatchState.endIndex ms)%Z
         then Error Errors.MatchError.AssertionFailed
         else
          Coercions.wrap_option Errors.MatchError.type CaptureRange
            (Coercions.CaptureRange_or_undefined
               (capture_range (MatchState.endIndex ms') (MatchState.endIndex ms))))
      (Hrressucc: rres = Success r)
      (Hcapupd: List.Update.Nat.One.update r (MatchState.captures ms') n = Success cap'),
      equiv_groupmap_ms (GroupMap.close (idx inp') (S n) gm') (match_state (MatchState.input ms) (MatchState.endIndex ms') cap').
  Admitted.
  
  Lemma equiv_open_groups_close_group:
    forall n startidx endidx gm' gl lr,
      group_map_equiv_open_groups gm' ((S n, startidx)::gl) ->
      open_groups_disjoint gl (def_groups (Regex.Group (S n) lr)) ->
      group_map_equiv_open_groups (GroupMap.close endidx (S n) gm') gl.
  Admitted.

  Lemma ms_matches_inp_close_group:
    forall ms ms' cap' inp inp' str0,
      ms_matches_inp ms' inp' ->
      input_compat inp str0 ->
      input_compat inp' str0 ->
      ms_matches_inp (match_state (MatchState.input ms) (MatchState.endIndex ms') cap') inp'.
  Admitted.
End EquivLemmas.