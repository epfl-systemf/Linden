From Linden Require Import Regex GroupMapMS LindenParameters Groups Tree Chars Semantics MSInput EquivDef Utils RegexpTranslation.
From Warblre Require Import Parameters List Notation Result Typeclasses Base Errors.
From Coq Require Import List ZArith.
Import ListNotations.
Import Notation.
Import Result.Notations.

Section EquivLemmas.
  Context `{characterClass: Character.class}.


  (* Linking advance_idx with advance_input *)
  Lemma advance_idx_advance_input:
    forall inp inp' dir,
      advance_input inp dir = Some inp' ->
      Tree.advance_idx (idx inp) dir = idx inp'.
  Proof.
  Admitted.


  (** ** Lemma for validity wrt checks *)

  (* Validity wrt checks in a list of actions `acts` implies validity wrt checks in the tail of `acts`. *)
  Lemma ms_valid_wrt_checks_tail:
    forall act acts ms dir,
    ms_valid_wrt_checks ms (act::acts) dir -> ms_valid_wrt_checks ms acts dir.
  Proof.
    intros act acts ms dir Hvalid inp Hin.
    apply Hvalid. now right.
  Qed.

  (* Validity wrt checks in a list of actions `acts` implies validity wrt `Areg reg :: act` for any `reg`. *)
  Lemma ms_valid_wrt_checks_Areg:
    forall reg acts ms dir,
    ms_valid_wrt_checks ms acts dir -> ms_valid_wrt_checks ms (Areg reg :: acts) dir.
  Proof.
    intros reg acts ms dir Hvalid inp Hin.
    destruct Hin as [Habs | Hin]; try discriminate.
    now apply Hvalid.
  Qed.

  (* Validity wrt checks in a list of actions `acts` implies validity wrt `Aclose gid :: act` for any `gid`. *)
  Lemma ms_valid_wrt_checks_Aclose:
    forall gid acts ms dir,
    ms_valid_wrt_checks ms acts dir -> ms_valid_wrt_checks ms (Aclose gid :: acts) dir.
  Proof.
    intros gid acts ms dir Hvalid inp Hin.
    destruct Hin as [Habs | Hin]; try discriminate.
    now apply Hvalid.
  Qed.

  (* Validity wrt checks does not depend on input string (!) or captures, but only on end index *)
  Lemma ms_valid_wrt_checks_inpcap:
    forall acts winp winp' endIdx cap cap' dir,
      ms_valid_wrt_checks (match_state winp' endIdx cap') acts dir ->
      ms_valid_wrt_checks (match_state winp endIdx cap) acts dir.
  Proof.
    intros. intros inpcheck Hin.
    unfold ms_valid_wrt_checks in H. specialize (H inpcheck Hin).
    destruct dir; inversion H.
    - simpl in H0. constructor. simpl. assumption.
    - simpl in H0. constructor. simpl. assumption.
  Qed.



  (** ** Lemmas related to inclusion or disjunction of group IDs. *)

  (** * Inductive definition that relates a regex to its parent regex. *)
  Inductive ChildRegex: regex -> regex -> Prop :=
  | Child_Disjunction_left: forall r1 r2, ChildRegex r1 (Disjunction r1 r2)
  | Child_Disjunction_right: forall r1 r2, ChildRegex r2 (Disjunction r1 r2)
  | Child_Sequence_left: forall r1 r2, ChildRegex r1 (Sequence r1 r2)
  | Child_Sequence_right: forall r1 r2, ChildRegex r2 (Sequence r1 r2)
  | Child_Quantified: forall greedy min delta r, ChildRegex r (Quantified greedy min delta r)
  | Child_Lookaround: forall lk r, ChildRegex r (Lookaround lk r)
  | Child_Group: forall id r, ChildRegex r (Group id r).

  Definition is_quantifier (r: regex): Prop :=
    exists greedy min delta rsub, r = Quantified greedy min delta rsub.

  (* The groups defined in a child regex are included in those defined in the parent regex. *)
  Lemma child_groups_incl_parent:
    forall child parent, ChildRegex child parent ->
      forall gid, In gid (def_groups child) -> In gid (def_groups parent).
  Proof.
    intros child parent Hchild. inversion Hchild; intros gid Hinchild; simpl; auto using in_or_app.
  Qed.



  (** * Lemmas about disjointness of list of open groups *)

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

  (* Used when opening a group *)
  Lemma open_groups_disjoint_open_group:
    forall n wr lr idx gl,
      open_groups_disjoint gl (def_groups (Regex.Group (S n) lr)) ->
      equiv_regex' wr lr (S n) ->
      open_groups_disjoint ((S n, idx)::gl) (def_groups lr).
  Admitted.


  (** * Lemmas about absence of forbidden groups *)

  Lemma in_forb_implies_in_def:
    forall gid r, In gid (forbidden_groups r) -> In gid (def_groups r).
  Proof.
    intros gid r Hin. destruct r; simpl in *; auto.
    inversion Hin.
  Qed.

  Lemma noforbidden_child:
    forall child parent, ChildRegex child parent -> ~is_quantifier parent ->
      forall gm forbgroups,
        no_forbidden_groups gm (forbidden_groups parent ++ forbgroups) ->
        no_forbidden_groups gm (forbidden_groups child ++ forbgroups).
  Proof.
    intros child parent Hchild Hparnotquant gm forbgroups H.
    intros gid Hinforb.
    apply H. rewrite in_app_iff in *. destruct Hinforb. 2: tauto.
    apply in_forb_implies_in_def in H0. inversion Hchild; subst child parent; simpl; try rewrite in_app_iff; try tauto.
    left. apply Hparnotquant. now repeat eexists.
  Qed.

  Lemma noforbidden_seq:
    forall r1 r2 gm forbgroups,
      no_forbidden_groups gm (forbidden_groups (Sequence r1 r2) ++ forbgroups) ->
      no_forbidden_groups gm (forbidden_groups r1 ++ forbidden_groups r2 ++ forbgroups).
  Proof.
    intros r1 r2 gm forbgroups Hnoforb.
    simpl in Hnoforb. unfold no_forbidden_groups. intros gid Hin.
    apply Hnoforb. do 2 rewrite in_app_iff in *.
    pose proof in_forb_implies_in_def gid r1. pose proof in_forb_implies_in_def gid r2. tauto.
  Qed.

  Lemma noforbidden_seq_bwd:
    forall r1 r2 gm forbgroups,
      no_forbidden_groups gm (forbidden_groups (Sequence r1 r2) ++ forbgroups) ->
      no_forbidden_groups gm (forbidden_groups r2 ++ forbidden_groups r1 ++ forbgroups).
  Proof.
    intros r1 r2 gm forbgroups Hnoforb.
    simpl in Hnoforb. unfold no_forbidden_groups. intros gid Hin.
    apply Hnoforb. do 2 rewrite in_app_iff in *.
    pose proof in_forb_implies_in_def gid r1. pose proof in_forb_implies_in_def gid r2. tauto.
  Qed.

  Lemma disj_forbidden_seq:
    forall n wr1 lr1 wr2 lr2 forbgroups,
      equiv_regex' wr1 lr1 n ->
      equiv_regex' wr2 lr2 (num_groups lr1 + n) ->
      List.Disjoint (def_groups (Sequence lr1 lr2)) forbgroups ->
      List.Disjoint (def_groups lr1) (forbidden_groups lr2 ++ forbgroups).
  Admitted.

  Lemma disj_forbidden_seq_bwd:
    forall n wr1 lr1 wr2 lr2 forbgroups,
      equiv_regex' wr1 lr1 n ->
      equiv_regex' wr2 lr2 (num_groups lr1 + n) ->
      List.Disjoint (def_groups (Sequence lr1 lr2)) forbgroups ->
      List.Disjoint (def_groups lr2) (forbidden_groups lr1 ++ forbgroups).
  Admitted.

  Lemma disj_forbidden_child:
    forall child parent, ChildRegex child parent ->
      forall forbgroups,
        List.Disjoint (def_groups parent) forbgroups ->
        List.Disjoint (def_groups child) forbgroups.
  Proof.
    intros child parent Hchild forbgroups Hdisj gid Hinchild.
    apply Hdisj. eauto using child_groups_incl_parent.
  Qed.

  (* Lemma used when opening a group *)
  Lemma noforb_open_group:
    forall n wr lr gm idx forbgroups,
      no_forbidden_groups gm (forbidden_groups (Regex.Group (S n) lr) ++ forbgroups) ->
      List.Disjoint (def_groups (Regex.Group (S n) lr)) forbgroups ->
      equiv_regex' wr lr (S n) ->
      no_forbidden_groups (GroupMap.open idx (S n) gm) (forbidden_groups lr ++ forbgroups).
  Admitted.

  (* Lemma used when closing a group *)
  Lemma group_map_close_find_other:
    forall gm idx gid gid',
      gid <> gid' ->
      GroupMap.find gid' (GroupMap.close idx gid gm) = GroupMap.find gid' gm.
  Proof.
    intros gm idx gid gid' Hneq.
    unfold GroupMap.close.
    destruct (GroupMap.find gid gm); simpl. 2: reflexivity.
    destruct r as [startIdx endIdxOpt].
    unfold GroupMap.find.
    admit.
  Admitted.

  Lemma noforb_close_group:
    forall n lr idx gm' forbgroups,
      no_forbidden_groups gm' forbgroups ->
      List.Disjoint (def_groups (Regex.Group (S n) lr)) forbgroups ->
      no_forbidden_groups (GroupMap.close idx (S n) gm') forbgroups.
  Proof.
    intros n lr idx gm' forbgroups Hnoforb Hdef_forbid_disj.
    unfold no_forbidden_groups. intros gid Hin.
    destruct (Nat.eq_dec gid (S n)) as [His_Sn | Hisnot_Sn].
    - subst gid. exfalso. unfold List.Disjoint, not in Hdef_forbid_disj. apply Hdef_forbid_disj with (x := S n); auto.
      simpl. left. reflexivity.
    - rewrite group_map_close_find_other. 2: congruence. now apply Hnoforb.
  Qed.


  (** ** Lemmas related to equivalence of group maps and MatchStates *)

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

  Lemma equiv_gm_ms_open_group:
    forall n lr idx gm ms forbgroups,
      equiv_groupmap_ms gm ms ->
      no_forbidden_groups gm (forbidden_groups (Regex.Group (S n) lr) ++ forbgroups) ->
      equiv_groupmap_ms (GroupMap.open idx (S n) gm) ms.
  Proof.
  Admitted.

  Lemma equiv_gm_gl_open_group:
    forall n lr idx gm gl forbgroups,
      group_map_equiv_open_groups gm gl ->
      no_forbidden_groups gm (forbidden_groups (Regex.Group (S n) lr) ++ forbgroups) ->
      group_map_equiv_open_groups (GroupMap.open idx (S n) gm) ((S n, idx)::gl).
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