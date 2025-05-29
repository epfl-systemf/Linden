From Linden Require Import Regex GroupMapMS LindenParameters Groups Tree Chars Semantics
  MSInput EquivDef Utils RegexpTranslation FunctionalSemantics LWEquivTreeLemmas WarblreLemmas
  GroupMapLemmas Tactics.
From Warblre Require Import Parameters List Notation Result Typeclasses Base Errors.
From Coq Require Import List ZArith Lia.
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
    intros [next pref] inp' []; simpl.
    - destruct next as [|x next']; try discriminate.
      intro H. injection H as <-. simpl. lia.
    - destruct pref as [|x pref']; try discriminate.
      intro H. injection H as <-. simpl. lia.
  Qed.


  (** ** For lookarounds *)
  (* The following lemmas prove that interpreting a (lookaround) tree corresponding to some regex only affects the groups defined in that regex. *)

  (* Definition of groups defined by a list of actions *)
  Fixpoint actions_def_groups (a: actions): list group_id :=
    match a with
    | nil => nil
    | Areg r :: q => def_groups r ++ actions_def_groups q
    | Acheck _ :: q => actions_def_groups q
    | Aclose gid :: q => gid :: actions_def_groups q
    end.
  
  (* Lemma for a list of actions *)
  Lemma actions_tree_no_outside_groups:
    forall acts gm0 inp dir0 fuel t,
      compute_tree acts inp gm0 dir0 fuel = Some t ->
      forall gm1 gm2 idx dir,
        Tree.tree_res t gm1 idx dir = Some gm2 ->
        forall gid, ~In gid (actions_def_groups acts) -> GroupMap.find gid gm2 = GroupMap.find gid gm1.
  Proof.
    intros acts gm0 inp dir0 fuel. revert acts gm0 inp dir0.
    induction fuel as [|fuel IHfuel]. { discriminate. }
    intros acts gm0 inp dir0 t. simpl.
    destruct acts as [|[reg | inpcheck | gid] acts].
    - (* No action *)
      intro H. injection H as <-. simpl.
      intros gm1 gm2 _ _ H. now injection H as <-.
    
    - (* Areg *)
      destruct reg as [ | cd | r1 r2 | r1 r2 | greedy min delta r | lk r | gid r | a | gid].

      + (* Epsilon *)
        simpl. apply IHfuel.

      + (* Character *)
        simpl. destruct read_char as [[c nextinp]|].
        2: { intro H. injection H as <-. discriminate. }
        specialize (IHfuel acts gm0 nextinp dir0).
        destruct compute_tree as [treecont|]; simpl; try discriminate.
        intro H. injection H as <-. intros gm1 gm2 idx dir.
        simpl. intro Hrescont. specialize (IHfuel treecont eq_refl gm1 gm2 (advance_idx idx dir) dir Hrescont).
        exact IHfuel.
      
      + (* Disjunction *)
        destruct compute_tree as [t1|] eqn:Heqt1; simpl; try discriminate.
        destruct (compute_tree (Areg r2 :: acts) _ _ _ _) as [t2|] eqn:Heqt2; simpl; try discriminate.
        intro H. injection H as <-. simpl.
        intros gm1 gm2 idx dir Hres gid Hnotin.
        do 2 rewrite in_app_iff in Hnotin.
        unfold seqop in Hres. destruct (tree_res t1 gm1 idx dir) as [gmres1|] eqn:Hres1; simpl in *.
        * (* First branch succeeds *)
          injection Hres as <-.
          apply (IHfuel _ _ _ _ _ Heqt1 _ _ _ _ Hres1). simpl. rewrite in_app_iff. tauto.
        * eapply IHfuel; eauto. simpl. rewrite in_app_iff. tauto.

      + (* Sequence *)
        destruct dir0.
        * simpl.
          intro Htreecomp. specialize (IHfuel (Areg r1 :: Areg r2 :: acts) gm0 inp forward t Htreecomp).
          simpl in IHfuel. rewrite <- app_assoc. exact IHfuel.
        * simpl.
          intro Htreecomp. specialize (IHfuel (Areg r2 :: Areg r1 :: acts) gm0 inp backward t Htreecomp).
          simpl in IHfuel. rewrite <- app_assoc. intros. eapply IHfuel; eauto.
          do 2 rewrite in_app_iff. do 2 rewrite in_app_iff in H0. tauto.
      
      + (* Quantified *)
        destruct min as [|min']. 1: destruct delta as [[|ndelta']|].
        * (* Done *)
          simpl. intros. eapply IHfuel; eauto. rewrite in_app_iff in H1. tauto.
        * (* Free, finite delta *)
          simpl. replace (ndelta' - 0) with ndelta' by lia.
          destruct (compute_tree (Areg r :: Acheck inp :: _ :: acts) inp _ dir0 fuel) as [titer|] eqn:Hiter; simpl; try discriminate.
          destruct (compute_tree acts inp gm0 dir0 fuel) as [tskip|] eqn:Hskip; simpl; try discriminate.
          intro H. injection H as <-.
          intros gm1 gm2 idx dir.
          pose proof IHfuel _ _ _ _ _ Hiter (GroupMap.reset (def_groups r) gm1) as IHiter.
          pose proof IHfuel _ _ _ _ _ Hskip gm1 as IHskip.
          destruct greedy; simpl.
          -- (* Greedy *)
             destruct (tree_res titer _ idx dir) as [gmiter|] eqn:Hiterres; simpl.
             ++ (* Iteration succeeds *)
                intro H. injection H as <-.
                specialize (IHiter gmiter idx dir Hiterres). simpl in IHiter.
                intros. rewrite IHiter. 2: { do 2 rewrite in_app_iff. rewrite in_app_iff in H. tauto. }
                rewrite in_app_iff in H. assert (~In gid (def_groups r)) by tauto. now apply gm_reset_find_other.
             ++ (* Iteration fails *)
                intro Hskipres. specialize (IHskip gm2 idx dir Hskipres).
                intros. apply IHskip. rewrite in_app_iff in H. tauto.
          -- (* Lazy *)
             destruct (tree_res tskip _ idx dir) as [gmskip|] eqn:Hskipres; simpl.
             ++ (* Iteration succeeds *)
                intro H. injection H as <-.
                specialize (IHskip gmskip idx dir Hskipres).
                intros gid H. apply IHskip. rewrite in_app_iff in H. tauto.
             ++ (* Iteration fails *)
                intro Hiterres. specialize (IHiter _ _ _ Hiterres). simpl in IHiter.
                intros. rewrite in_app_iff in H.
                rewrite IHiter. 2: { do 2 rewrite in_app_iff. tauto. }
                assert (~In gid (def_groups r)) by tauto. now apply gm_reset_find_other.
        * (* Free, infinite delta *)
          simpl.
          (* Copy-pasting from above!! *)
          destruct (compute_tree (Areg r :: Acheck inp :: _ :: acts) inp _ dir0 fuel) as [titer|] eqn:Hiter; simpl; try discriminate.
          destruct (compute_tree acts inp gm0 dir0 fuel) as [tskip|] eqn:Hskip; simpl; try discriminate.
          intro H. injection H as <-.
          intros gm1 gm2 idx dir.
          pose proof IHfuel _ _ _ _ _ Hiter (GroupMap.reset (def_groups r) gm1) as IHiter.
          pose proof IHfuel _ _ _ _ _ Hskip gm1 as IHskip.
          destruct greedy; simpl.
          -- (* Greedy *)
             destruct (tree_res titer _ idx dir) as [gmiter|] eqn:Hiterres; simpl.
             ++ (* Iteration succeeds *)
                intro H. injection H as <-.
                specialize (IHiter gmiter idx dir Hiterres). simpl in IHiter.
                intros. rewrite IHiter. 2: { do 2 rewrite in_app_iff. rewrite in_app_iff in H. tauto. }
                rewrite in_app_iff in H. assert (~In gid (def_groups r)) by tauto. now apply gm_reset_find_other.
             ++ (* Iteration fails *)
                intro Hskipres. specialize (IHskip gm2 idx dir Hskipres).
                intros. apply IHskip. rewrite in_app_iff in H. tauto.
          -- (* Lazy *)
             destruct (tree_res tskip _ idx dir) as [gmskip|] eqn:Hskipres; simpl.
             ++ (* Iteration succeeds *)
                intro H. injection H as <-.
                specialize (IHskip gmskip idx dir Hskipres).
                intros gid H. apply IHskip. rewrite in_app_iff in H. tauto.
             ++ (* Iteration fails *)
                intro Hiterres. specialize (IHiter _ _ _ Hiterres). simpl in IHiter.
                intros. rewrite in_app_iff in H.
                rewrite IHiter. 2: { do 2 rewrite in_app_iff. tauto. }
                assert (~In gid (def_groups r)) by tauto. now apply gm_reset_find_other.
        * (* Forced *)
          destruct compute_tree as [titer|] eqn:Hiter; try discriminate.
          intro H. injection H as <-.
          simpl. intros gm1 gm2 idx dir Heqgm2 gid Hnotin. rewrite in_app_iff in Hnotin. 
          rewrite (IHfuel _ _ _ _ _ Hiter _ _ _ _ Heqgm2).
          2: { simpl. do 2 rewrite in_app_iff. tauto. }
          assert (~In gid (def_groups r)) by tauto. now apply gm_reset_find_other.
        
      + (* Lookaround *)
        destruct compute_tree as [treelk|] eqn:Hcomputelk; try discriminate.
        destruct lk_succeeds eqn:Hlksucc.
        * (* Lookaround succeeds *)
          destruct lk_group_map as [gmlk|] eqn:Heqgmlk.
          -- destruct (compute_tree acts inp gmlk dir0 fuel) as [treecont|] eqn:Htreecont; try discriminate.
             intro H. injection H as <-.
             simpl. destruct positivity.
             ++ intros gm1 gm2 idx dir. destruct tree_res as [gmafterlk|] eqn:Heqgmafterlk; try discriminate.
                intros Heqgm2 gid Hnotin.
                rewrite in_app_iff in Hnotin.
                rewrite (IHfuel _ _ _ _ _ Htreecont _ _ _ _ Heqgm2) by tauto.
                rewrite (IHfuel _ _ _ _ _ Hcomputelk _ _ _ _ Heqgmafterlk).
                2: { simpl. rewrite app_nil_r. tauto. }
                reflexivity.
             ++ intros gm1 gm2 idx dir.
                destruct tree_res eqn:Hgmafterlk; try discriminate.
                intros Heqgm2 gid Hnotin. rewrite in_app_iff in Hnotin.
                eapply IHfuel; eauto.
          -- (* Does not happen, but does not matter *)
             intro H. injection H as <-. simpl. discriminate.
        * (* Lookaround fails *)
          intro H. injection H as <-. simpl. discriminate.

      + (* Group *)
        destruct compute_tree as [treecont|] eqn:Hcomputecont; try discriminate.
        intro H. injection H as <-. simpl.
        intros gm1 gm2 idx dir Heqgm2 gid' Hnotin.
        rewrite (IHfuel _ _ _ _ _ Hcomputecont _ _ _ _ Heqgm2).
        2: { simpl. rewrite in_app_iff in *. simpl. tauto. }
        assert (gid <> gid') by tauto.
        now apply group_map_open_find_other.
      
      + (* Anchor *)
        destruct anchor_satisfied.
        * destruct compute_tree as [treecont|] eqn:Hcomputecont; try discriminate.
          intro H. injection H as <-. simpl. eauto using IHfuel.
        * intro H. injection H as <-. discriminate.

      + (* Backreference *)
        destruct read_backref as [[br_str nextinp]|].
        * destruct compute_tree as [tcont|] eqn:Hcomputecont; try discriminate.
          intro H. injection H as <-. simpl. eauto using IHfuel.
        * intro H. injection H as <-. discriminate.
    
    - (* Acheck *)
      destruct is_strict_suffix.
      + (* Check passes *)
        specialize (IHfuel acts gm0 inp dir0).
        destruct compute_tree as [treecont|]; simpl; try discriminate.
        intro H. injection H as <-. intros gm1 gm2 idx dir. simpl.
        intro Hrescont. specialize (IHfuel treecont eq_refl gm1 gm2 idx dir Hrescont).
        exact IHfuel.
      + (* Check fails *)
        intro H. injection H as <-. discriminate.
    
    - (* Aclose *)
      specialize (IHfuel acts (GroupMap.close (idx inp) gid gm0) inp dir0).
      destruct compute_tree as [treecont|]; simpl; try discriminate.
      specialize (IHfuel treecont eq_refl).
      intro H. injection H as <-.
      intros gm1 gm2 idx dir. simpl.
      specialize (IHfuel (GroupMap.close idx gid gm1) gm2 idx dir).
      intro Hrescont. specialize (IHfuel Hrescont).
      intros gid' Hnotin. rewrite IHfuel by tauto.
      Search GroupMap.find GroupMap.close.
      assert (gid' <> gid) by (symmetry; tauto).
      now apply group_map_close_find_other.
  Qed.

  Corollary reg_tree_no_outside_groups:
    forall reg gm0 inp dir0 fuel t,
      compute_tree [Areg reg] inp gm0 dir0 fuel = Some t ->
      forall gm1 gm2 idx dir,
        Tree.tree_res t gm1 idx dir = Some gm2 ->
        forall gid, ~In gid (def_groups reg) -> GroupMap.find gid gm2 = GroupMap.find gid gm1.
  Proof.
    intros.
    apply actions_tree_no_outside_groups with (acts := [Areg reg]) (inp := inp) (dir := dir) (fuel := fuel) (t := t) (idx := idx) (gm0 := gm0) (dir0 := dir0); auto.
    simpl. rewrite app_nil_r. assumption.
  Qed.

  Lemma Areg_Aclose_disappear:
    forall reg gid P,
      (Areg reg = Aclose gid \/ P) <-> P.
  Proof.
    intros reg gid P.
    assert (Areg reg = Aclose gid <-> False). { split; [discriminate|intros []]. }
    rewrite H. tauto.
  Qed.

  Lemma Acheck_Aclose_disappear:
    forall strcheck gid P,
      (Acheck strcheck = Aclose gid \/ P) <-> P.
  Proof.
    intros strcheck gid P.
    assert (Acheck strcheck = Aclose gid <-> False). { split; [discriminate|intros []]. }
    rewrite H. tauto.
  Qed.

  Lemma actions_tree_no_open_groups:
    forall acts gm0 inp dir0 fuel t,
      compute_tree acts inp gm0 dir0 fuel = Some t ->
      forall gm1 gm2 idx dir,
        Tree.tree_res t gm1 idx dir = Some gm2 ->
        forall gid,
          is_open_range (GroupMap.find gid gm2) ->
          is_open_range (GroupMap.find gid gm1) /\
          ~In (Aclose gid) acts.
  Proof.
    intros acts gm0 inp dir0 fuel. revert acts gm0 inp dir0.
    induction fuel as [|fuel IHfuel]; try discriminate.

    intro acts. destruct acts as [|[reg | strcheck | gid]].
    2: destruct reg as [ | cd | r1 r2 | r1 r2 | greedy min delta r | lk r | gid r | a | gid].
    - (* No action *)
      simpl. intros _ _ _ t H. injection H as <-. simpl.
      intros gm1 gm2 _ _ H. injection H as <-. auto.
    
    - (* Epsilon *)
      simpl. intros gm0 inp dir0 t Hcomputesucc gm1 gm2 idx dir Heqgm2 gid Hopen2.
      rewrite Areg_Aclose_disappear. eauto using IHfuel.

    - (* Character *)
      simpl. intros gm0 inp dir0 t.
      destruct read_char as [[c nextinp]|].
      + (* Read succeeds *)
        destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
        intro H. injection H as <-. simpl.
        intros gm1 gm2 idx dir Hres gid Hopen2.
        rewrite Areg_Aclose_disappear.
        eapply IHfuel; eauto.
      + (* Read fails *)
        intro H. injection H as <-. discriminate.
    
    - (* Disjunction *)
      simpl. intros gm0 inp dir0 t.
      destruct compute_tree as [t1|] eqn:Hcompute1; try discriminate.
      destruct (compute_tree (Areg r2 :: acts) inp gm0 dir0 fuel) as [t2|] eqn:Hcompute2; try discriminate.
      intro H. injection H as <-.
      intros gm1 gm2 idx dir. simpl.
      destruct (tree_res t1 gm1 idx dir) as [res1|] eqn:Hres1; simpl.
      + (* First branch succeeds *)
        intro H. injection H as <-. intros gid Hopenres.
        pose proof IHfuel _ _ _ _ _ Hcompute1 _ _ _ _ Hres1 _ Hopenres.
        simpl in H. rewrite Areg_Aclose_disappear in *. auto.
      + (* First branch fails *)
        intros Hres2 gid Hopen2.
        pose proof IHfuel _ _ _ _ _ Hcompute2 _ _ _ _ Hres2 _ Hopen2.
        simpl in H. rewrite Areg_Aclose_disappear in *. auto.
    
    - (* Sequence *)
      simpl. intros gm0 inp dir0 t Hcomputesucc gm1 gm2 idx dir Heqgm2 gid Hopen2.
      pose proof IHfuel _ _ _ _ _ Hcomputesucc _ _ _ _ Heqgm2 _ Hopen2.
      destruct dir0; simpl in H.
      + do 2 rewrite Areg_Aclose_disappear in H. rewrite Areg_Aclose_disappear. auto.
      + do 2 rewrite Areg_Aclose_disappear in H. rewrite Areg_Aclose_disappear. auto.

    - (* Quantified *)
      intros gm0 inp dir0 t. simpl.
      (* Annoying but should be okay *)
      admit.

    - (* Lookaround *)
      intros gm0 inp dir0 t. simpl.
      destruct compute_tree as [treelk|] eqn:Hcomputelk; try discriminate.
      destruct lk_succeeds.
      + (* Lookaround succeeds *)
        destruct lk_group_map as [gmlk|] eqn:Hgmlk.
        * (* Only valid case *)
          destruct (compute_tree acts inp gmlk dir0 fuel) as [treecont|] eqn:Htreecont; try discriminate.
          intro H. injection H as <-. intros gm1 gm2 idx dir.
          simpl.
          destruct positivity.
          -- destruct tree_res as [gmafterlk|] eqn:Hgmafterlk; try discriminate.
             intros Heqgm2 gid Hopen2.
             rewrite Areg_Aclose_disappear.
             pose proof IHfuel _ _ _ _ _ Htreecont _ _ _ _ Heqgm2 _ Hopen2 as [].
             pose proof IHfuel _ _ _ _ _ Hcomputelk _ _ _ _ Hgmafterlk _ H as []. auto.
          -- destruct tree_res as [gmafterlk|] eqn:Hgmafterlk; try discriminate.
             intros Heqgm2 gid Hopen2.
             rewrite Areg_Aclose_disappear.
             eauto using IHfuel.
        * (* Does not happen, but does not matter *)
          intro H. injection H as <-. simpl. discriminate.
      + (* Lookaround fails *)
        intro H. injection H as <-. simpl. discriminate.

    - (* Group *)
      intros gm0 inp dir0 t. simpl.
      destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
      intro H. injection H as <-.
      intros gm1 gm2 idx dir Heqgm2 gid0 Hopen2.
      simpl in Heqgm2.
      pose proof IHfuel _ _ _ _ _ Htreecont _ _ _ _ Heqgm2 _ Hopen2 as [].
      simpl in H0.
      rewrite Areg_Aclose_disappear in *.
      admit. (* Becomes solvable *)

    - (* Anchor *)
      intros gm0 inp dir0 t. simpl.
      admit. (* Should not be difficult *)
    
    - (* Backreference; should not be difficult *)
      admit.
    
    - (* Check; should not be difficult *)
      admit.

    - (* Close *)
      admit.
  Admitted.


  (** ** Lemmas for validity wrt checks *)

  (* We always have validity wrt no checks at all *)
  Lemma ms_valid_wrt_checks_nil:
    forall ms dir, ms_valid_wrt_checks ms nil dir.
  Proof.
    intros ms dir. unfold ms_valid_wrt_checks. intros inpcheck [].
  Qed.

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

  (* Progress check success case *)
  Lemma progresscheck_success_ssuffix:
    forall ms ms' inp inp' str0 tl dir,
      ms_valid_wrt_checks ms' (Acheck inp :: tl) dir ->
      (MatchState.endIndex ms' =? MatchState.endIndex ms)%Z = false ->
      ms_matches_inp ms' inp' -> input_compat inp' str0 ->
      ms_matches_inp ms inp -> input_compat inp str0 ->
      is_strict_suffix inp' inp dir = true.
  Admitted.




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
  Proof.
    intros n wr lr idx gl Hgldisj Hequiv.
    pose proof equiv_def_groups' _ _ _ Hequiv as Hdefgroups.
    simpl in Hgldisj.
    unfold open_groups_disjoint. intros gid idx' Hin.
    destruct Hin.
    - injection H as <- <-. intro Habs. rewrite Hdefgroups in Habs. apply in_seq in Habs. lia.
    - unfold open_groups_disjoint, not in Hgldisj. intro Habs. eapply Hgldisj; eauto. now right.
  Qed.

  Lemma open_groups_disjoint_nil_l:
    forall gidl, open_groups_disjoint nil gidl.
  Proof.
    intro gidl. unfold open_groups_disjoint.
    intros _ _ [].
  Qed.



  (** * Lemmas about absence of forbidden groups *)

  Lemma noforb_empty:
    forall forbgroups, no_forbidden_groups GroupMap.empty forbgroups.
  Admitted.

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
  Proof.
    intros n wr1 lr1 wr2 lr2 forbgroups Hequiv1 Hequiv2 Hdisj.
    unfold List.Disjoint. intros gid Hin1.
    rewrite in_app_iff. intro Habs. destruct Habs as [Habs | Habs].
    - apply equiv_def_groups' in Hequiv1, Hequiv2. rewrite Hequiv1, in_seq in Hin1.
      apply in_forb_implies_in_def in Habs. rewrite Hequiv2, in_seq in Habs. lia.
    - unfold List.Disjoint, not in Hdisj. apply Hdisj with (x := gid); auto. simpl. rewrite in_app_iff. now left.
  Qed.

  Lemma disj_forbidden_seq_bwd:
    forall n wr1 lr1 wr2 lr2 forbgroups,
      equiv_regex' wr1 lr1 n ->
      equiv_regex' wr2 lr2 (num_groups lr1 + n) ->
      List.Disjoint (def_groups (Sequence lr1 lr2)) forbgroups ->
      List.Disjoint (def_groups lr2) (forbidden_groups lr1 ++ forbgroups).
  Proof.
    intros n wr1 lr1 wr2 lr2 forbgroups Hequiv1 Hequiv2 Hdisj gid Hin2 Habs.
    rewrite in_app_iff in Habs. destruct Habs as [Habs | Habs].
    - apply equiv_def_groups' in Hequiv1, Hequiv2. rewrite Hequiv2, in_seq in Hin2.
      apply in_forb_implies_in_def in Habs. rewrite Hequiv1, in_seq in Habs. lia.
    - unfold List.Disjoint, not in Hdisj. apply Hdisj with (x := gid); auto. simpl. rewrite in_app_iff. now right.
  Qed.

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
  Proof.
    intros n wr lr gm idx forbgroups Hnoforb Hdef_forbid_disj Hequiv.
    unfold no_forbidden_groups. intros gid Hin. rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
    - apply in_forb_implies_in_def in Hin. apply equiv_def_groups' in Hequiv. rewrite Hequiv, in_seq in Hin.
      assert (Hgid_not_Sn: gid <> S n) by lia. rewrite group_map_open_find_other. 2: congruence.
      unfold no_forbidden_groups in Hnoforb. apply Hnoforb. simpl. rewrite in_app_iff. right. left. rewrite Hequiv. now rewrite in_seq.
    - assert (Hgid_not_Sn: gid <> S n). {
        unfold List.Disjoint, not in Hdef_forbid_disj. intros ->. apply Hdef_forbid_disj with (x := S n); auto. simpl. now left.
      }
      rewrite group_map_open_find_other. 2: congruence.
      unfold no_forbidden_groups in Hnoforb. apply Hnoforb. rewrite in_app_iff. now right. 
  Qed.

  (* Lemma used when closing a group *)
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

  (* Lemma used in lookarounds *)
  Lemma noforb_lk:
    forall lr gm gmafterlk forbgroups tlk inp fuel,
      no_forbidden_groups gm (forbidden_groups (Lookaround LookAhead lr) ++ forbgroups) ->
      compute_tree [Areg lr] inp gm forward fuel = Some tlk ->
      tree_res tlk gm (idx inp) forward = Some gmafterlk ->
      List.Disjoint (def_groups (Lookaround LookAhead lr)) forbgroups ->
      no_forbidden_groups gmafterlk forbgroups.
  Proof.
    intros lr gm gmafterlk forbgroups tlk inp fuel Hnoforb Heqtlk Heqgmafterlk Hdef_forbid_disj.
    unfold no_forbidden_groups. intros gid Hinforb.
    destruct (in_dec Nat.eq_dec gid (def_groups lr)) as [Hinlr | Hnotinlr].
    - exfalso. unfold List.Disjoint, not in Hdef_forbid_disj. simpl in Hdef_forbid_disj. eauto.
    - rewrite (reg_tree_no_outside_groups _ _ _ _ _ _ Heqtlk _ _ _ _ Heqgmafterlk) by assumption.
      unfold no_forbidden_groups in Hnoforb. apply Hnoforb. apply in_or_app. now right.
  Qed.



  (** ** Lemmas related to equivalence of group maps and MatchStates *)

  (* Irrelevance of input string and end index of the MatchState *)
  Lemma equiv_gm_ms_irrelevance:
    forall gm str1 str2 endInd1 endInd2 cap,
      equiv_groupmap_ms gm (match_state str1 endInd1 cap) ->
      equiv_groupmap_ms gm (match_state str2 endInd2 cap).
  Proof.
    intros. unfold equiv_groupmap_ms in *. simpl in *. exact H.
  Qed.

  (* Lemma used in lookarounds *)
  Lemma equiv_gmafterlk_msafterlk:
    forall rlk str0 endInd msafterlk gmafterlk,
      equiv_groupmap_ms gmafterlk rlk ->
      msafterlk = match_state str0 endInd (MatchState.captures rlk) ->
      equiv_groupmap_ms gmafterlk msafterlk.
  Proof.
    intros [str0' endInd' cap] str0 endInd msafterlk gmafterlk Hequiv Heqmsafterlk.
    subst msafterlk. simpl. eauto using equiv_gm_ms_irrelevance.
  Qed.

  (* Lemma used in lookarounds as well *)
  Lemma equiv_open_groups_lk:
    forall gm gl gmafterlk lr inp fuel tlk forbgroups,
      group_map_equiv_open_groups gm gl ->
      compute_tree [Areg lr] inp gm forward fuel = Some tlk ->
      tree_res tlk gm (idx inp) forward = Some gmafterlk ->
      no_forbidden_groups gm (forbidden_groups (Lookaround LookAhead lr) ++ forbgroups) ->
      group_map_equiv_open_groups gmafterlk gl.
  Proof.
    intros gm gl gmafterlk lr inp fuel tlk forbgroups Hgmgl Heqtlk Heqgmafterlk Hnoforb.
    unfold group_map_equiv_open_groups.
  Admitted.

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
    intros.
    unfold equiv_groupmap_ms. intro gid_prec.
    destruct (in_dec Nat.eq_dec gid_prec (List.Range.Nat.Bounds.range (parenIndex + 1 - 1) (parenIndex + parenCount + 1 - 1))) as [Hreset | Hnotreset].
    - (* In reset groups *)
      assert (Hreset': In (S gid_prec) gidl). {
        setoid_rewrite range_seq in Hreset. apply in_seq in Hreset. rewrite Heqgidl. apply in_seq. lia.
      }
      rewrite Heqgmreset. rewrite Heqmsreset. simpl.
      rewrite gm_reset_find by assumption. rewrite (batch_update_1 _ _ _ _ _ Hresetsucc) by assumption. constructor.
    - (* Not in reset groups *)
      assert (Hnotreset': ~In (S gid_prec) gidl). {
        setoid_rewrite range_seq in Hnotreset. rewrite in_seq in Hnotreset. rewrite Heqgidl. rewrite in_seq. lia.
      }
      rewrite Heqgmreset. rewrite Heqmsreset. simpl.
      rewrite gm_reset_find_other by assumption. rewrite (batch_update_2 _ _ _ _ _ Hresetsucc) by assumption.
      apply Hequiv.
  Qed.

  (* Resetting a list of groups that is disjoint from the list of open groups preserves equivalence to the list of open groups. *)
  Lemma equiv_open_groups_reset:
    forall gl gidl gm gmreset
      (Hgldisj: open_groups_disjoint gl gidl)
      (Hequiv: group_map_equiv_open_groups gm gl)
      (Heqreset: gmreset = GroupMap.reset gidl gm),
      group_map_equiv_open_groups gmreset gl.
  Proof.
    intros. unfold group_map_equiv_open_groups.
    intros gid idx. destruct (in_dec Nat.eq_dec gid gidl) as [Hreset | Hnotreset].
    - subst gmreset. rewrite gm_reset_find by assumption.
      split; try discriminate.
      intro Habs. unfold open_groups_disjoint, not in Hgldisj. exfalso. eauto.
    - subst gmreset. rewrite gm_reset_find_other by assumption. apply Hequiv.
  Qed.

  Lemma equiv_gm_ms_open_group:
    forall n lr idx gm ms forbgroups,
      equiv_groupmap_ms gm ms ->
      no_forbidden_groups gm (forbidden_groups (Regex.Group (S n) lr) ++ forbgroups) ->
      equiv_groupmap_ms (GroupMap.open idx (S n) gm) ms.
  Proof.
    intros n lr idx gm ms forbgroups Hequiv Hnoforb.
    unfold equiv_groupmap_ms. intro gid_prec.
    destruct (Nat.eq_dec gid_prec n) as [Hopengrp | Hnotopengrp].
    - (* gid is the newly open group *)
      unfold no_forbidden_groups in Hnoforb. unfold equiv_groupmap_ms in Hequiv.
      subst gid_prec. specialize (Hequiv n). specialize (Hnoforb (S n)).
      specialize_prove Hnoforb. { simpl. now left. }
      rewrite group_map_open_find. rewrite Hnoforb in Hequiv. inversion Hequiv. constructor.
    - assert (Hnotopengrp': S gid_prec <> S n) by lia. rewrite group_map_open_find_other by congruence. apply Hequiv.
  Qed.

  Lemma equiv_gm_gl_open_group:
    forall n lr idx gm gl forbgroups,
      group_map_equiv_open_groups gm gl ->
      no_forbidden_groups gm (forbidden_groups (Regex.Group (S n) lr) ++ forbgroups) ->
      group_map_equiv_open_groups (GroupMap.open idx (S n) gm) ((S n, idx)::gl).
  Proof.
    intros n lr idx gm gl forbgroups Hgmgl Hnoforb.
    unfold group_map_equiv_open_groups. intros gid' idx'.
    destruct (Nat.eq_dec gid' (S n)) as [Hopengrp | Hnotopengrp].
    - (* gid' is the newly open group *)
      subst gid'. rewrite group_map_open_find by assumption. split.
      + intro H. injection H as <-. now left.
      + (* Non-trivial: due to Hgmgl and Hnoforb, gl does not contain anything related to group S n *)
        intro Hin. destruct Hin as [Hin | Hin].
        * injection Hin as <-. reflexivity.
        * exfalso. admit.
    - (* gid' is not the newly open group *)
      rewrite group_map_open_find_other by congruence. unfold group_map_equiv_open_groups in Hgmgl. rewrite (Hgmgl gid' idx').
      split.
      + intro Hin. now right.
      + intros [Hin | Hin].
        * injection Hin as H1 H2. congruence.
        * assumption.
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
  Proof.
    intros n startidx endidx gm' gl lr Hequiv Hgldisj.
    unfold group_map_equiv_open_groups. intros gid idx.
    destruct (Nat.eq_dec gid (S n)) as [Hclosedgrp | Hnotclosedgrp].
    - subst gid. split; intro Habs.
      + pose proof group_map_close_find_notopen gm' endidx (S n) as Hnotopen.
        exfalso. apply Hnotopen. rewrite Habs. constructor.
      + exfalso. simpl in Hgldisj. unfold open_groups_disjoint in Hgldisj. specialize (Hgldisj (S n) idx Habs).
        apply Hgldisj. now left.
    - rewrite group_map_close_find_other by congruence. unfold group_map_equiv_open_groups in Hequiv. rewrite Hequiv.
      split.
      + intro H. destruct H as [Habs | H]; auto. injection Habs as <-. contradiction.
      + intro H. now right.
  Qed.

  Lemma ms_matches_inp_close_group:
    forall ms ms' cap' inp inp' str0,
      ms_matches_inp ms inp ->
      ms_matches_inp ms' inp' ->
      input_compat inp str0 ->
      input_compat inp' str0 ->
      ms_matches_inp (match_state (MatchState.input ms) (MatchState.endIndex ms') cap') inp'.
  Proof.
    intros ms ms' cap' inp inp' str0 Hmsinp Hms'inp' Hinpcompat Hinp'compat.
    rewrite inp_compat_ms_same_inp with (str0 := str0) (inp1 := inp) (inp2 := inp') (ms2 := ms') by assumption.
    apply ms_matches_inp_capchg with (cap := MatchState.captures ms'). now destruct ms'.
  Qed.

End EquivLemmas.
