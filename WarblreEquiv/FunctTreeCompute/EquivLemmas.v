From Linden Require Import Regex GroupMapMS LindenParameters Groups Tree Chars Semantics
  MSInput EquivDef Utils RegexpTranslation FunctionalSemantics LWEquivTreeLemmas WarblreLemmas
  GroupMapLemmas Tactics.
From Warblre Require Import Parameters List Notation Result Typeclasses Base Errors RegExpRecord.
From Coq Require Import List ZArith Lia DecidableClass ClassicalFacts.
Import ListNotations.
Import Notation.
Import Result.Notations.

Local Open Scope result_flow.

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
        forall gid idx,
          GroupMap.find gid gm2 = Some (GroupMap.Range idx None) ->
          GroupMap.find gid gm1 = Some (GroupMap.Range idx None) /\
          ~In (Aclose gid) acts.
  Proof. (* Some variable names do not make sense because this lemma was strengthened wrt a previous version of the lemma *)
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
        intro H. injection H as <-. intros gid idx' Hopenres.
        pose proof IHfuel _ _ _ _ _ Hcompute1 _ _ _ _ Hres1 _ _ Hopenres.
        simpl in H. rewrite Areg_Aclose_disappear in *. auto.
      + (* First branch fails *)
        intros Hres2 gid idx' Hopen2.
        pose proof IHfuel _ _ _ _ _ Hcompute2 _ _ _ _ Hres2 _ _ Hopen2.
        simpl in H. rewrite Areg_Aclose_disappear in *. auto.
    
    - (* Sequence *)
      simpl. intros gm0 inp dir0 t Hcomputesucc gm1 gm2 idx dir Heqgm2 gid idx' Hopen2.
      pose proof IHfuel _ _ _ _ _ Hcomputesucc _ _ _ _ Heqgm2 _ _ Hopen2.
      destruct dir0; simpl in H.
      + do 2 rewrite Areg_Aclose_disappear in H. rewrite Areg_Aclose_disappear. auto.
      + do 2 rewrite Areg_Aclose_disappear in H. rewrite Areg_Aclose_disappear. auto.

    - (* Quantified *)
      intros gm0 inp dir0 t. simpl.
      (* Annoying but should be okay *)
      destruct min as [|min'].
      1: destruct delta as [[|n']|].
      + (* Done *)
        intros Hcompute gm1 gm2 idx dir Heqgm2 gid idx' Hopen2.
        rewrite Areg_Aclose_disappear. eauto using IHfuel.
      + (* Free, finite delta *)
        destruct compute_tree as [titer|] eqn:Htiter; try discriminate.
        destruct (compute_tree acts inp gm0 dir0 fuel) as [tskip|] eqn:Htskip; try discriminate.
        intro H. injection H as <-.
        intros gm1 gm2 idx dir. destruct greedy; simpl.
        * (* Greedy *)
          destruct (tree_res titer _ idx dir) as [gmiter|] eqn:Hresiter; simpl.
          -- (* Iterating succeeds *)
             intro H. injection H as <-. intros gid idx' Hopeniter.
             rewrite Areg_Aclose_disappear.
             pose proof IHfuel _ _ _ _ _ Htiter _ _ _ _ Hresiter _ _ Hopeniter.
             simpl in H. rewrite Areg_Aclose_disappear, Acheck_Aclose_disappear, Areg_Aclose_disappear in H.
             destruct (in_dec Nat.eq_dec gid (def_groups r)) as [Hreset | Hnotreset].
             ++ rewrite gm_reset_find in H by assumption. destruct H. inversion H. (* gid was reset *)
             ++ rewrite gm_reset_find_other in H by assumption. auto.
          -- (* Iterating fails *)
             intros Heqgm2 gid idx' Hopen2.
             pose proof IHfuel _ _ _ _ _ Htskip _ _ _ _ Heqgm2 _ _ Hopen2.
             rewrite Areg_Aclose_disappear. auto.
        * (* Lazy *)
          destruct (tree_res tskip gm1 idx dir) as [gmskip|] eqn:Hresskip; simpl.
          -- (* Skipping succeeds *)
             intro H. injection H as <-. intros gid Hopenskip.
             rewrite Areg_Aclose_disappear. eauto using IHfuel.
          -- (* Skipping fails *)
             intros Heqgm2 gid idx' Hopen2.
             rewrite Areg_Aclose_disappear.
             pose proof IHfuel _ _ _ _ _ Htiter _ _ _ _ Heqgm2 _ _ Hopen2. simpl in H.
             rewrite Areg_Aclose_disappear, Acheck_Aclose_disappear, Areg_Aclose_disappear in H.
             destruct (in_dec Nat.eq_dec gid (def_groups r)) as [Hreset | Hnotreset].
             ++ rewrite gm_reset_find in H by assumption. destruct H. inversion H. (* gid was reset *)
             ++ rewrite gm_reset_find_other in H by assumption. auto.
      + (* Free, infinite delta: copy-pasting!! *)
        destruct compute_tree as [titer|] eqn:Htiter; try discriminate.
        destruct (compute_tree acts inp gm0 dir0 fuel) as [tskip|] eqn:Htskip; try discriminate.
        intro H. injection H as <-.
        intros gm1 gm2 idx dir. destruct greedy; simpl.
        * (* Greedy *)
          destruct (tree_res titer _ idx dir) as [gmiter|] eqn:Hresiter; simpl.
          -- (* Iterating succeeds *)
             intro H. injection H as <-. intros gid idx' Hopeniter.
             rewrite Areg_Aclose_disappear.
             pose proof IHfuel _ _ _ _ _ Htiter _ _ _ _ Hresiter _ _ Hopeniter.
             simpl in H. rewrite Areg_Aclose_disappear, Acheck_Aclose_disappear, Areg_Aclose_disappear in H.
             destruct (in_dec Nat.eq_dec gid (def_groups r)) as [Hreset | Hnotreset].
             ++ rewrite gm_reset_find in H by assumption. destruct H. inversion H. (* gid was reset *)
             ++ rewrite gm_reset_find_other in H by assumption. auto.
          -- (* Iterating fails *)
             intros Heqgm2 gid idx' Hopen2.
             pose proof IHfuel _ _ _ _ _ Htskip _ _ _ _ Heqgm2 _ _ Hopen2.
             rewrite Areg_Aclose_disappear. auto.
        * (* Lazy *)
          destruct (tree_res tskip gm1 idx dir) as [gmskip|] eqn:Hresskip; simpl.
          -- (* Skipping succeeds *)
             intro H. injection H as <-. intros gid idx' Hopenskip.
             rewrite Areg_Aclose_disappear. eauto using IHfuel.
          -- (* Skipping fails *)
             intros Heqgm2 gid idx' Hopen2.
             rewrite Areg_Aclose_disappear.
             pose proof IHfuel _ _ _ _ _ Htiter _ _ _ _ Heqgm2 _ _ Hopen2. simpl in H.
             rewrite Areg_Aclose_disappear, Acheck_Aclose_disappear, Areg_Aclose_disappear in H.
             destruct (in_dec Nat.eq_dec gid (def_groups r)) as [Hreset | Hnotreset].
             ++ rewrite gm_reset_find in H by assumption. destruct H. inversion H. (* gid was reset *)
             ++ rewrite gm_reset_find_other in H by assumption. auto.
      + (* Forced *)
        destruct compute_tree as [titer|] eqn:Htiter; try discriminate.
        intro H. injection H as <-.
        intros gm1 gm2 idx dir Heqgm2 gid idx' Hopen2.
        rewrite Areg_Aclose_disappear.
        pose proof IHfuel _ _ _ _ _ Htiter _ _ _ _ Heqgm2 _ _ Hopen2. simpl in H.
        do 2 rewrite Areg_Aclose_disappear in H.
        destruct (in_dec Nat.eq_dec gid (def_groups r)) as [Hreset | Hnotreset].
        ++ rewrite gm_reset_find in H by assumption. destruct H. inversion H. (* gid was reset *)
        ++ rewrite gm_reset_find_other in H by assumption. auto.

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
             intros Heqgm2 gid idx' Hopen2.
             rewrite Areg_Aclose_disappear.
             pose proof IHfuel _ _ _ _ _ Htreecont _ _ _ _ Heqgm2 _ _ Hopen2 as [].
             pose proof IHfuel _ _ _ _ _ Hcomputelk _ _ _ _ Hgmafterlk _ _ H as []. auto.
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
      intros gm1 gm2 idx dir Heqgm2 gid0 idx' Hopen2.
      simpl in Heqgm2.
      pose proof IHfuel _ _ _ _ _ Htreecont _ _ _ _ Heqgm2 _ _ Hopen2 as [].
      simpl in H0.
      rewrite Areg_Aclose_disappear in *.
      apply Decidable.not_or in H0. destruct H0.
      assert (gid <> gid0). { intros ->. contradiction. }
      rewrite group_map_open_find_other in H by assumption. auto.

    - (* Anchor *)
      intros gm0 inp dir0 t. simpl.
      destruct anchor_satisfied.
      + (* Anchor is satisfied *)
        destruct compute_tree as [treecont|] eqn:Hcomputecont; try discriminate.
        intro H. injection H as <-. intros gm1 gm2 idx dir Heqgm2 gid Hopen2.
        rewrite Areg_Aclose_disappear. eauto using IHfuel.
      + (* Anchor is not satisfied *)
        intro H. injection H as <-. discriminate.
    
    - (* Backreference *)
      intros gm0 inp dir t. simpl.
      destruct read_backref as [[br_str nextinp]|].
      + destruct compute_tree as [tcont|] eqn:Htcont; try discriminate.
        intro H. injection H as <-. simpl.
        intros gm1 gm2 idx dir0 Heqgm2 gid' Hopen2.
        rewrite Areg_Aclose_disappear. eauto using IHfuel.
      + intro H. injection H as <-. discriminate.
    
    - (* Check; should not be difficult *)
      intros gm0 inp dir0 t. simpl.
      destruct is_strict_suffix.
      + (* Is strict suffix *)
        destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
        intro H. injection H as <-. intros gm1 gm2 idx dir Heqgm2 gid Hopen2.
        rewrite Acheck_Aclose_disappear. eauto using IHfuel.
      + (* Is not strict suffix *)
        intro H. injection H as <-. discriminate.

    - (* Close *)
      intros gm0 inp dir0 t. simpl.
      destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
      intro H. injection H as <-. simpl. intros gm1 gm2 idx dir Heqgm2 gid' idx' Hopen2.
      pose proof IHfuel _ _ _ _ _ Htreecont _ _ _ _ Heqgm2 _ _ Hopen2.
      destruct (Nat.eq_dec gid gid') as [Heq | Hnoteq].
      + subst gid'.
        pose proof group_map_close_find_notopen gm1 idx gid as Hnotopen. destruct H. exfalso. apply Hnotopen.
        rewrite H. constructor.
      + rewrite group_map_close_find_other in H by assumption. destruct H. split; auto.
        intro Habs. destruct Habs.
        * injection H1 as H1. contradiction.
        * contradiction.

  Qed.


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

  (* Validity wrt checks right before iterating a quantifier *)
  Lemma msreset_valid_checks:
    forall ms inp cap' msreset lreg qreg qreg' act dir,
      ms_matches_inp ms inp ->
      msreset = match_state (MatchState.input ms) (MatchState.endIndex ms) cap' ->
      ms_valid_wrt_checks ms (Areg qreg :: act)%list dir ->
      ms_valid_wrt_checks msreset (Areg lreg :: Acheck inp :: Areg qreg' :: act)%list dir.
  Proof.
    intros ms inp cap' msreset lreg qreg qreg' act dir
      Hmsinp -> Hvalidchecks.
    intros inpcheck Hin. destruct dir.
    - destruct Hin as [Habs | Hin]. 1: discriminate.
      destruct Hin as [Heqinp | [Habs | Hinact]]. 2: discriminate.
      + (* The input itself *)
        injection Heqinp as <-.
        inversion Hmsinp. constructor. simpl. lia.
      + (* In the tail *)
        apply ms_valid_wrt_checks_tail in Hvalidchecks. specialize (Hvalidchecks inpcheck Hinact).
        inversion Hvalidchecks. constructor. simpl. lia.
    - destruct Hin as [Habs | Hin]. 1: discriminate.
      destruct Hin as [Heqinp | [Habs | Hinact]]. 2: discriminate.
      + (* The input itself *)
        injection Heqinp as <-.
        inversion Hmsinp. constructor. simpl. lia.
      + (* In the tail *)
        apply ms_valid_wrt_checks_tail in Hvalidchecks. specialize (Hvalidchecks inpcheck Hinact).
        inversion Hvalidchecks. constructor. simpl. lia.
  Qed.


  (** ** Lemmas related to inclusion or disjunction of group IDs *)

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
  Proof.
    intro forbgroups. unfold no_forbidden_groups.
    intros gid Hin. apply gm_find_empty.
  Qed.

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

  Lemma noforb_reset:
    forall gm lreg gmreset forbgroups,
      gmreset = GroupMap.reset (def_groups lreg) gm ->
      no_forbidden_groups gm forbgroups ->
      no_forbidden_groups gmreset (forbidden_groups lreg ++ forbgroups).
  Proof.
    intros gm lreg gmreset forbgroups -> Hnoforb.
    unfold no_forbidden_groups. intros gid Hinforb.
    apply in_app_or in Hinforb. destruct (in_dec Nat.eq_dec gid (def_groups lreg)) as [Hinlreg | Hnotinlreg].
    - now apply gm_reset_find.
    - destruct Hinforb as [Hinlreg | Hinforb].
      1: apply in_forb_implies_in_def in Hinlreg; contradiction.
      rewrite gm_reset_find_other by assumption. now apply Hnoforb.
  Qed.

  (* Lemma used in lookarounds *)
  Lemma noforb_lk:
    forall lr gm gmafterlk forbgroups tlk inp fuel dir,
      no_forbidden_groups gm (forbidden_groups (Lookaround (LKFactorization.to_lookaround dir true) lr) ++ forbgroups) ->
      compute_tree [Areg lr] inp gm dir fuel = Some tlk ->
      tree_res tlk gm (idx inp) dir = Some gmafterlk ->
      List.Disjoint (def_groups (Lookaround LookAhead lr)) forbgroups ->
      no_forbidden_groups gmafterlk forbgroups.
  Proof.
    intros lr gm gmafterlk forbgroups tlk inp fuel dir Hnoforb Heqtlk Heqgmafterlk Hdef_forbid_disj.
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

  (* Linking indexing success and GroupMap.find result *)
  Lemma equiv_gm_ms_indexing_find_nonneg:
    forall gm ms (gid: positive) startIdx endIdx,
      equiv_groupmap_ms gm ms ->
      Base.indexing (MatchState.captures ms) gid = Success (Some (capture_range startIdx endIdx)) ->
      GroupMap.find (positive_to_nat gid) gm = Some (GroupMap.Range (Z.to_nat startIdx) (Some (Z.to_nat endIdx))) /\
      (startIdx >= 0)%Z /\ (endIdx >= 0)%Z.
  Proof.
    intros gm ms gid startIdx endIdx Hequiv Hindexing.
    unfold equiv_groupmap_ms in Hequiv.
    unfold Base.indexing in Hindexing. simpl in Hindexing. unfold positive_to_non_neg in Hindexing.
    set (gid_prec := Pos.to_nat gid - 1) in Hindexing. specialize (Hequiv gid_prec).
    replace (S gid_prec) with (Pos.to_nat gid) in Hequiv by lia. unfold positive_to_nat.
    unfold List.Indexing.Nat.indexing in Hindexing.
    unfold Result.Conversions.from_option in Hindexing.
    assert (Hindexing': nth_error (MatchState.captures ms) gid_prec = Some (Some (capture_range startIdx endIdx))). {
      destruct nth_error as [x|]; try discriminate. now injection Hindexing as ->.
    }
    apply nth_error_nth with (d := None) in Hindexing'.
    rewrite Hindexing' in Hequiv. inversion Hequiv. inversion H1.
    do 2 rewrite Nat2Z.id. split; [|split].
    1: reflexivity.
    all: lia.
  Qed.

  (* If indexing yields None, then finding cannot yield Some with two defined ends *)
  Lemma equiv_gm_ms_indexing_none:
    forall gm ms (gid: positive) startIdx endIdx,
      equiv_groupmap_ms gm ms ->
      Base.indexing (MatchState.captures ms) gid = Success None ->
      GroupMap.find (positive_to_nat gid) gm = Some (GroupMap.Range startIdx (Some endIdx)) ->
      False.
  Proof.
    intros gm ms gid startIdx endIdx Hequiv Hindexing Hfind.
    unfold equiv_groupmap_ms in Hequiv.
    unfold Base.indexing in Hindexing. simpl in Hindexing. unfold positive_to_non_neg in Hindexing.
    set (gid_prec := Pos.to_nat gid - 1) in Hindexing. specialize (Hequiv gid_prec).
    replace (S gid_prec) with (Pos.to_nat gid) in Hequiv by lia. unfold positive_to_nat.
    unfold List.Indexing.Nat.indexing in Hindexing.
    unfold Result.Conversions.from_option in Hindexing.
    assert (Hindexing': nth_error (MatchState.captures ms) gid_prec = Some None). {
      destruct nth_error as [x|]; try discriminate. now injection Hindexing as ->.
    }
    apply nth_error_nth with (d := None) in Hindexing'.
    rewrite Hindexing' in Hequiv. inversion Hequiv.
    - unfold positive_to_nat in Hfind. congruence.
    - unfold positive_to_nat in Hfind. rewrite Hfind in H0. injection H0 as H0. discriminate.
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
    forall gm gl gmafterlk lr inp fuel tlk forbgroups dir,
      group_map_equiv_open_groups gm gl ->
      compute_tree [Areg lr] inp gm dir fuel = Some tlk ->
      tree_res tlk gm (idx inp) dir = Some gmafterlk ->
      no_forbidden_groups gm (forbidden_groups (Lookaround LookAhead lr) ++ forbgroups) ->
      group_map_equiv_open_groups gmafterlk gl.
  Proof.
    intros gm gl gmafterlk lr inp fuel tlk forbgroups dir Hgmgl Heqtlk Heqgmafterlk Hnoforb.
    unfold group_map_equiv_open_groups. intros gid idx.
    split.
    - intro Hfind.
      apply (actions_tree_no_open_groups _ _ _ _ _ _ Heqtlk _ _ _ _ Heqgmafterlk) in Hfind.
      destruct Hfind as [Hfind _]. apply Hgmgl. auto.
    - intro Hin.
      rewrite (reg_tree_no_outside_groups _ _ _ _ _ _ Heqtlk _ _ _ _ Heqgmafterlk).
      + apply Hgmgl. auto.
      + intro Habs. specialize (Hnoforb gid). apply Hgmgl in Hin. rewrite in_app_iff in Hnoforb.
        simpl in Hnoforb. specialize (Hnoforb (or_introl Habs)). congruence.
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
      + (* Due to Hgmgl and Hnoforb, gl does not contain anything related to group S n *)
        intro Hin. destruct Hin as [Hin | Hin].
        * injection Hin as <-. reflexivity.
        * exfalso. apply Hgmgl in Hin. specialize (Hnoforb (S n)).
          rewrite in_app_iff in Hnoforb.
          specialize_prove Hnoforb. {
            left. simpl. left. reflexivity. 
          }
          congruence.
    - (* gid' is not the newly open group *)
      rewrite group_map_open_find_other by congruence. unfold group_map_equiv_open_groups in Hgmgl. rewrite (Hgmgl gid' idx').
      split.
      + intro Hin. now right.
      + intros [Hin | Hin].
        * injection Hin as H1 H2. congruence.
        * assumption.
  Qed.

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
  Proof.
    intros. unfold equiv_groupmap_ms. intro gid_prec.
    destruct (Nat.eq_dec gid_prec n) as [Heqn | Hnoteqn].
    - subst gid_prec. simpl.
      rewrite nth_indexing.
      rewrite List.Update.Nat.One.indexing_updated_same with (ls := MatchState.captures ms') (v := r); auto.
      rewrite Heqrres in Hrressucc.
      destruct dir; simpl in *.
      + (* Forward *)
        destruct (MatchState.endIndex ms <=? MatchState.endIndex ms')%Z eqn:Hle; simpl in *; try discriminate.
        replace (GroupMap.find (S n) (GroupMap.close (idx inp') (S n) gm')) with (Some (GroupMap.Range (idx inp) (Some (idx inp')))).
        2: {
          symmetry. specialize (Hgm'gl' (S n) (idx inp)).
          destruct Hgm'gl' as [_ Hgm'gl'].
          specialize (Hgm'gl' (or_introl eq_refl)).
          unfold GroupMap.close. rewrite Hgm'gl'.
          replace (idx inp <=? idx inp') with true.
          2: {
            symmetry. apply Nat.leb_le.
            unfold idx.
            inversion Hmsinp. inversion Hms'inp'. inversion Hinpcompat. inversion Hinp'compat.
            subst ms ms'. simpl in *. lia.
          }
          apply gm_find_add.
        }
        injection Hrressucc as <-.
        constructor.
        replace (MatchState.endIndex ms) with (Z.of_nat (idx inp)). 2: {
          inversion Hmsinp. simpl. f_equal. auto.
        }
        replace (MatchState.endIndex ms') with (Z.of_nat (idx inp')). 2: {
          inversion Hms'inp'. simpl. f_equal. auto.
        }
        constructor.
      + (* Backward *)
        destruct (MatchState.endIndex ms' <=? MatchState.endIndex ms)%Z eqn:Hle; simpl in *; try discriminate.
        replace (GroupMap.find (S n) (GroupMap.close (idx inp') (S n) gm')) with (Some (GroupMap.Range (idx inp') (Some (idx inp)))).
        2: {
          symmetry. specialize (Hgm'gl' (S n) (idx inp)).
          destruct Hgm'gl' as [_ Hgm'gl'].
          specialize (Hgm'gl' (or_introl eq_refl)).
          unfold GroupMap.close. rewrite Hgm'gl'.
          decide (idx inp = idx inp').
          - rewrite <- H. rewrite Nat.leb_refl. apply gm_find_add.
          - replace (idx inp <=? idx inp') with false.
            2: {
              symmetry. apply Nat.leb_nle.
              unfold idx in *.
              inversion Hmsinp. inversion Hms'inp'. inversion Hinpcompat. inversion Hinp'compat. subst inp inp'.
              subst ms ms'. simpl in *. intro Habs. lia.
            }
            apply gm_find_add.
        }
        injection Hrressucc as <-.
        constructor.
        replace (MatchState.endIndex ms) with (Z.of_nat (idx inp)). 2: {
          inversion Hmsinp. simpl. f_equal. auto.
        }
        replace (MatchState.endIndex ms') with (Z.of_nat (idx inp')). 2: {
          inversion Hms'inp'. simpl. f_equal. auto.
        }
        constructor.
    - rewrite group_map_close_find_other. 2: { symmetry. intro Habs. injection Habs as Habs. contradiction. }
      simpl.
      rewrite nth_indexing.
      rewrite List.Update.Nat.One.indexing_updated_other with (i := n) (ls := MatchState.captures ms') (v := r); auto.
      rewrite <- nth_indexing. apply Hgm'ms'.
  Qed.
  
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


  (** ** For backreferences *)

  Lemma endMatch_oob_forward:
    forall ms next pref rlen endMatch,
      endMatch = (MatchState.endIndex ms + rlen)%Z ->
      ms_matches_inp ms (Input next pref) ->
      (rlen >= 0)%Z ->
      ((endMatch >? Z.of_nat (length (MatchState.input ms)))%Z = true <->
        Z.to_nat rlen >? length next = true).
  Proof.
    intros ms next pref rlen endMatch -> Hmsinp Hrlennneg.
    inversion Hmsinp as [str0 end_ind cap next' pref' Hlenpref Heqstr0 Heqms Heqnext']. subst next' pref' str0. simpl.
    rewrite app_length, rev_length, Z.gtb_gt.
    change (match Z.to_nat rlen with | 0 => _ | S m' => _ end) with (S (length next) <=? Z.to_nat rlen).
    rewrite Nat.leb_le. lia.
  Qed.

  Lemma beginMatch_oob_backward:
    forall ms next pref rlen beginMatch,
      beginMatch = (MatchState.endIndex ms - rlen)%Z ->
      ms_matches_inp ms (Input next pref) ->
      (rlen >= 0)%Z ->
      ((beginMatch <? 0)%Z = true <->
        Z.to_nat rlen >? length pref = true).
  Proof.
    intros ms next pref rlen beginMatch -> Hmsinp Hrlennneg.
    inversion Hmsinp as [str0 end_ind cap next' pref' Hlenpref Heqstr0 Heqms Heqnext']. subst next' pref' str0. simpl.
    change (match Z.to_nat rlen with | 0 => _ | S m' => _ end) with (S (length pref) <=? Z.to_nat rlen).
    rewrite Nat.leb_le. lia.
  Qed.

  (* Main lemma, quite difficult *)
  (* Helper lemmas *)
  Lemma string_eqb_iff:
    forall s t: string,
      (s ==? t)%wt = true <->
      forall i: nat, nth_error s i = nth_error t i.
  Proof.
    intros. split; intro H.
    - rewrite EqDec.inversion_true in H. subst t. reflexivity.
    - replace t with s. 1: apply EqDec.reflb.
      apply nth_error_ext. auto.
  Qed.

  Axiom EM: excluded_middle.

  Lemma notforalln_existsnnot:
    forall P: nat -> Prop,
      ~(forall n, P n) -> (exists n, ~P n).
  Proof.
    intros. destruct (EM (exists n: nat, ~P n)) as [Hexists | Hnotexists]; auto.
    exfalso. apply H. intro n. destruct (EM (P n)) as [HPn | HnPn]; auto.
    exfalso. apply Hnotexists. exists n. auto.
  Qed.

  Lemma string_diff_iff:
    forall s t: string,
      (s ==? t)%wt = false <->
      exists i: nat, nth_error s i <> nth_error t i.
  Proof.
    intros s t. split.
    - intro Hneq.
      apply notforalln_existsnnot. intro Habs. rewrite <- string_eqb_iff in Habs. congruence.
    - intro Hexistsdiff. apply Bool.not_true_iff_false. intro Habs.
      rewrite EqDec.inversion_true in Habs. subst t.
      destruct Hexistsdiff as [i Hexistsdiff]. contradiction.
  Qed.

  Lemma neqb_neq {A} `{EqDec A}: forall (x y: A),
      (x !=? y)%wt = true <-> x <> y.
  Proof.
    intros x y. split.
    - intro H. unfold EqDec.neqb in H.
      apply (f_equal negb) in H. rewrite Bool.negb_involutive in H. simpl in H. apply EqDec.inversion_false. auto.
    - intro H. apply EqDec.inversion_false in H. unfold EqDec.neqb. rewrite H. reflexivity.
  Qed.

  Lemma neqb_eq {A} `{EqDec A}:
    forall x y: A, (x !=? y)%wt = false <-> x = y.
  Proof.
    intros x y. split.
    - intro H. apply (f_equal negb) in H. unfold EqDec.neqb in H. rewrite Bool.negb_involutive in H. simpl in H.
      apply EqDec.inversion_true. auto.
    - intro H. unfold EqDec.neqb. subst y. rewrite EqDec.reflb. reflexivity.
  Qed.

  Lemma substr_len:
    forall i j inp, length (substr inp i j) <= j-i.
  Proof.
    intros i j inp. unfold substr.
    rewrite firstn_length. lia.
  Qed.

  Lemma indexing_nat_to_int {A}:
    forall (l: list A) (i: nat),
      List.Indexing.Nat.indexing l i = List.Indexing.Int.indexing l (Z.of_nat i).
  Proof.
    intros l i. unfold List.Indexing.Int.indexing, List.lift_to_Z.
    destruct i; simpl.
    - reflexivity.
    - now rewrite SuccNat2Pos.id_succ.
  Qed.

  Lemma indexing_range_success:
    forall (i: nat) (i': Z) (n: Z),
      List.Indexing.Nat.indexing (List.Range.Int.Bounds.range 0 n) i = Success i' ->
      i' = Z.of_nat i.
  Proof.
    intros i i' n H.
    rewrite indexing_nat_to_int in H.
    apply List.Range.Int.Bounds.indexing in H. lia.
  Qed.

  Lemma indexing_range_length_inb_success:
    forall (i: nat) (base: Z) (len: nat),
      i < len ->
      List.Indexing.Nat.indexing (List.Range.Int.Length.range base len) i = Success (base + Z.of_nat i)%Z.
  Proof.
    intros i base len Hlt.
    pose proof List.Range.Int.Length.length len base as Hlen.
    pose proof List.Range.Int.Length.indexing (Z.of_nat i) base len as Hindexing.
    replace (List.Indexing.Nat.indexing _ i) with (List.Indexing.Int.indexing (List.Range.Int.Length.range base len) (Z.of_nat i)).
    2: {
      unfold List.Indexing.Int.indexing, List.lift_to_Z.
      destruct i.
      - simpl. reflexivity.
      - simpl. now rewrite SuccNat2Pos.id_succ.
    }
    pose proof List.Indexing.Int.success_bounds0 (List.Range.Int.Length.range base len) (Z.of_nat i) as [_ Hsuccess_bounds0].
    rewrite Hlen in Hsuccess_bounds0. specialize_prove Hsuccess_bounds0 by lia.
    destruct Hsuccess_bounds0 as [v Hsuccess_bounds0].
    rewrite Hsuccess_bounds0.
    specialize (Hindexing v Hsuccess_bounds0). congruence.
  Qed.

  Corollary indexing_range_inb_success:
    forall (i: nat) (low up: Z),
      i < Z.to_nat (up - low)%Z ->
      List.Indexing.Nat.indexing (List.Range.Int.Bounds.range low up) i = Success (low + Z.of_nat i)%Z.
  Proof.
    intros i low up Hlt.
    unfold List.Range.Int.Bounds.range.
    apply indexing_range_length_inb_success. auto.
  Qed.

  Corollary indexing_range_inb_success':
    forall (i: nat) (n: Z),
      i < Z.to_nat n ->
      List.Indexing.Nat.indexing (List.Range.Int.Bounds.range 0 n) i = Success (Z.of_nat i).
  Proof.
    intros i n Hlt.
    pose proof indexing_range_inb_success i 0 n.
    specialize_prove H by lia. rewrite H. f_equal.
  Qed.

  Lemma indexing_success_nth {A: Type}:
    forall (l: list A) i x, List.Indexing.Nat.indexing l i = Success x -> nth_error l i = Some x.
  Proof.
    intros l i x. unfold List.Indexing.Nat.indexing, Result.Conversions.from_option.
    destruct (nth_error l i); try discriminate.
    intro H. injection H as ->. reflexivity.
  Qed.

  (* Non-trivial *)
  Lemma indexing_firstn_skipn {A: Type}:
    forall (s: list A) startIdx n i x,
      (startIdx >= 0)%Z ->
      i < n ->
      List.Indexing.Int.indexing s (startIdx + Z.of_nat i) = Success x ->
      nth_error (firstn n (skipn (Z.to_nat startIdx) s)) i = Some x.
  Proof.
    intros s startIdx n i x HstartIdxnneg Hinn Hindexing.
    rewrite List.Indexing.Int.to_nat in Hindexing by lia.
    apply indexing_success_nth in Hindexing.
    replace (Z.to_nat (startIdx + Z.of_nat i)) with (Z.to_nat startIdx + i) in Hindexing by lia.
    assert (Hinb: Z.to_nat startIdx + i < length s). { apply nth_error_Some. rewrite Hindexing. discriminate. }
    decide (Z.to_nat startIdx + n < length s).
    - (* firstn is actually truncating stuff *)
      rewrite <- nth_error_app1 with (l' := skipn n (skipn (Z.to_nat startIdx) s)).
      2: { rewrite firstn_length_le; auto. rewrite skipn_length. lia. }
      rewrite firstn_skipn.
      (* The rest of the proof of this case is the same as in the 2nd case *)
      replace i with ((Z.to_nat startIdx + i) - Z.to_nat startIdx) by lia.
      replace (Z.to_nat startIdx) with (length (firstn (Z.to_nat startIdx) s)) at 3.
      2: { apply firstn_length_le. lia. }
      rewrite <- nth_error_app2.
      2: { rewrite firstn_length_le by lia. lia. }
      rewrite firstn_skipn. auto.
    - (* firstn leaves the skipn unchanged *)
      rewrite firstn_all2.
      2: { rewrite skipn_length. lia. }
      (* Copy-pasting... *)
      replace i with ((Z.to_nat startIdx + i) - Z.to_nat startIdx) by lia.
      replace (Z.to_nat startIdx) with (length (firstn (Z.to_nat startIdx) s)) at 3.
      2: { apply firstn_length_le. lia. }
      rewrite <- nth_error_app2.
      2: { rewrite firstn_length_le by lia. lia. }
      rewrite firstn_skipn. auto.
  Qed.

  (* This lemma actually follows from the above lemma in a somewhat convoluted way *)
  Lemma ms_indexing_next_nth:
    forall ms next pref i x,
      ms_matches_inp ms (Input next pref) ->
      List.Indexing.Int.indexing (MatchState.input ms) (MatchState.endIndex ms + Z.of_nat i) = Success x ->
      nth_error next i = Some x.
  Proof.
    intros ms next pref i x Hmsinp Hindexing.
    inversion Hmsinp as [str0 end_ind cap next' pref' Hlenpref Heqstr0]. subst ms next' pref'.
    simpl in *.
    replace next with (skipn (length (rev pref)) str0).
    2: { apply (f_equal (skipn (length (rev pref)))) in Heqstr0. rewrite <- Heqstr0. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
    replace (skipn _ str0) with (firstn (length (skipn (length (rev pref)) str0)) (skipn (length (rev pref)) str0)).
    2: apply firstn_all.
    replace (length (rev pref)) with (Z.to_nat (Z.of_nat (length (rev pref)))) at 2 by lia.
    apply indexing_firstn_skipn.
    - lia.
    - replace (length (skipn (length (rev pref)) str0)) with (length next).
      2: { rewrite <- Heqstr0. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
      apply List.Indexing.Int.success_bounds in Hindexing. rewrite <- Heqstr0 in Hindexing.
      rewrite app_length, rev_length in Hindexing. lia.
    - rewrite rev_length, Hlenpref. auto.
  Qed.

  Lemma nth_error_firstn {A}:
    forall (l: list A) n i, i < n -> nth_error (firstn n l) i = nth_error l i.
  Proof.
    intros l n i Hlt.
    decide (n < length l).
    - rewrite <- firstn_skipn with (n := n) (A := A) (l := l) at 2.
      rewrite nth_error_app1. 1: reflexivity.
      rewrite firstn_length_le by lia. auto.
    - assert (H': n >= length l) by lia.
      rewrite firstn_all2; auto.
  Qed.

  Lemma backref_get_next:
    forall ms next pref rlen i gi,
      ms_matches_inp ms (Input next pref) ->
      i < Z.to_nat rlen ->
      List.Indexing.Int.indexing (MatchState.input ms) (MatchState.endIndex ms + Z.of_nat i) = Success gi ->
      nth_error (firstn (Z.to_nat rlen) next) i = Some gi.
  Proof.
    intros ms next pref rlen i gi Hmsinp Hinb Hindexing.
    replace (nth_error _ i) with (nth_error next i) by (symmetry; eauto using nth_error_firstn). (* because i < Z.to_nat rlen *)
    eauto using ms_indexing_next_nth.
  Qed.

  Lemma backref_get_pref:
    forall ms next pref rlen i gi,
      ms_matches_inp ms (Input next pref) ->
      i < Z.to_nat rlen ->
      (MatchState.endIndex ms - rlen >= 0)%Z ->
      List.Indexing.Int.indexing (MatchState.input ms) (MatchState.endIndex ms - rlen + Z.of_nat i) = Success gi ->
      nth_error (rev (firstn (Z.to_nat rlen) pref)) i = Some gi.
  Proof.
    intros ms next pref rlen i gi Hmsinp Hiinb Hstartinb Hindexing.
    inversion Hmsinp as [str0 end_ind cap next' pref' Hlenpref Heqstr0]. subst ms next' pref'.
    simpl in *.
    replace (rev _) with (firstn (Z.to_nat rlen) (skipn (end_ind - Z.to_nat rlen) str0)).
    2: { apply (f_equal (skipn (end_ind - Z.to_nat rlen))) in Heqstr0. rewrite <- Heqstr0.
    rewrite skipn_app, rev_length. replace (end_ind - _ - length pref) with 0 by lia. simpl.
    rewrite firstn_app, skipn_length, rev_length. replace (Z.to_nat rlen - _) with 0 by lia.
    simpl. rewrite app_nil_r. rewrite skipn_rev. replace (length pref - _) with (Z.to_nat rlen) by lia.
    rewrite firstn_all2. 2: { rewrite rev_length. apply firstn_le_length. } reflexivity. }
    replace (end_ind - Z.to_nat rlen) with (Z.to_nat (Z.of_nat end_ind - rlen)) by lia.
    apply indexing_firstn_skipn; auto.
  Qed.

  Lemma backref_get_ref:
    forall ms next pref startIdx endIdx rlen i rsi,
      rlen = (endIdx - startIdx)%Z -> (rlen >= 0)%Z ->
      (startIdx >= 0)%Z -> (endIdx >= 0)%Z ->
      ms_matches_inp ms (Input next pref) ->
      i < Z.to_nat rlen ->
      List.Indexing.Int.indexing (MatchState.input ms) (startIdx + Z.of_nat i) = Success rsi ->
      nth_error (substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx)) i = Some rsi.
  Proof.
    intros ms next pref startIdx endIdx rlen i rsi Heqrlen Hrlennneg HstartIdxnneg HendIdxnneg Hmsinp Hinb Hindexing.
    unfold substr. replace (Z.to_nat endIdx - Z.to_nat startIdx) with (Z.to_nat rlen) by lia.
    unfold input_str. rewrite <- ms_matches_inp_invinp with (ms := ms) by assumption.
    eauto using indexing_firstn_skipn.
  Qed.

  (* The lemmas *)
  Lemma exists_diff_iff:
    forall ms next pref startIdx endIdx endMatch rlen existsdiff rer,
      RegExpRecord.ignoreCase rer = false ->
      (rlen >= 0)%Z ->
      endMatch = (MatchState.endIndex ms + rlen)%Z ->
      ms_matches_inp ms (Input next pref) ->
      rlen = (endIdx - startIdx)%Z ->
      (startIdx >= 0)%Z -> (endIdx >= 0)%Z ->
      List.Exists.exist (List.Range.Int.Bounds.range 0 rlen)
        (fun i =>
          let! rsi =<< List.Indexing.Int.indexing (MatchState.input ms) (startIdx + i) in
          let! gi =<< List.Indexing.Int.indexing (MatchState.input ms) (Z.min (MatchState.endIndex ms) endMatch + i) in
          Coercions.wrap_bool Errors.MatchError.type (Character.canonicalize rer rsi !=? Character.canonicalize rer gi)%wt) = Success existsdiff ->
      existsdiff = true <-> (List.firstn (Z.to_nat rlen) next ==? substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx))%wt = false.
  Proof.
    intros ms next pref startIdx endIdx endMatch rlen existsdiff rer Hcasesenst Hrlennneg HeqendMatch Hmsinp Heqrlen HstartIdxnneg HendIdxnneg Heqexistsdiff.
    destruct existsdiff.
    - (* There exists some different character *)
      apply List.Exists.true_to_prop in Heqexistsdiff.
      unfold List.Exists.Exist in Heqexistsdiff. destruct Heqexistsdiff as [i [i' [Hindexing Hdiff]]].
      assert (Heqi': i' = Z.of_nat i) by eauto using indexing_range_success. subst i'.
      pose proof List.Indexing.Nat.success_bounds _ _ _ Hindexing as Hinb.
      rewrite List.Range.Int.Bounds.length in Hinb. replace (rlen - 0)%Z with rlen in Hinb by lia.
      replace (Z.min _ endMatch) with (MatchState.endIndex ms) in Hdiff by lia.
      destruct List.Indexing.Int.indexing as [rsi|] eqn:Heqrsi in Hdiff; try discriminate.
      destruct List.Indexing.Int.indexing as [gi|] eqn:Hgi in Hdiff; try discriminate.
      simpl in Hdiff. do 2 rewrite canonicalize_casesenst in Hdiff by assumption.
      split; try reflexivity; intros _.
      apply string_diff_iff. exists i.
      replace (nth_error (firstn _ _) i) with (Some gi) by (symmetry; eauto using backref_get_next).
      replace (nth_error (substr _ _ _) i) with (Some rsi) by (symmetry; eauto using backref_get_ref).
      injection Hdiff as Hdiff. intro H. injection H as H.
      symmetry in H. apply neqb_neq in Hdiff. contradiction.
    - (* All characters are equal *)
      split; try discriminate.
      apply List.Exists.false_to_prop in Heqexistsdiff.
      intro H. exfalso. revert H. setoid_rewrite Bool.not_false_iff_true.
      apply string_eqb_iff. intro i.
      decide (i < Z.to_nat rlen) as Hinb.
      + (* Apply Heqexistsdiff *)
        specialize (Heqexistsdiff i (Z.of_nat i)). specialize_prove Heqexistsdiff by auto using indexing_range_inb_success'.
        simpl in Heqexistsdiff.
        replace (Z.min _ endMatch) with (MatchState.endIndex ms) in Heqexistsdiff by lia.
        destruct List.Indexing.Int.indexing as [rsi|] eqn:Heqrsi in Heqexistsdiff; try discriminate.
        destruct List.Indexing.Int.indexing as [gi|] eqn:Hgi in Heqexistsdiff; try discriminate.
        simpl in Heqexistsdiff. do 2 rewrite canonicalize_casesenst in Heqexistsdiff by assumption.
        injection Heqexistsdiff as Hdiff.
        replace (nth_error (firstn _ _) i) with (Some gi) by (symmetry; eauto using backref_get_next).
        replace (nth_error (substr _ _ _) i) with (Some rsi) by (symmetry; eauto using backref_get_ref).
        rewrite neqb_eq in Hdiff. congruence.
      + replace (nth_error _ i) with (None (A := Character)).
        2: { symmetry. apply nth_error_None. rewrite firstn_length. lia. }
        replace (nth_error _ i) with (None (A := Character)).
        2: { symmetry. apply nth_error_None. transitivity (Z.to_nat endIdx - Z.to_nat startIdx). 2: lia.
          apply substr_len. }
        reflexivity.
  Qed.
  
  (* Backward direction; mostly copy-pasting forward proof *)
  Lemma exists_diff_iff_bwd:
    forall ms next pref startIdx endIdx beginMatch rlen existsdiff rer,
      RegExpRecord.ignoreCase rer = false ->
      (rlen >= 0)%Z ->
      beginMatch = (MatchState.endIndex ms - rlen)%Z ->
      (beginMatch >= 0)%Z ->
      ms_matches_inp ms (Input next pref) ->
      rlen = (endIdx - startIdx)%Z ->
      (startIdx >= 0)%Z -> (endIdx >= 0)%Z ->
      List.Exists.exist (List.Range.Int.Bounds.range 0 rlen)
        (fun i =>
          let! rsi =<< List.Indexing.Int.indexing (MatchState.input ms) (startIdx + i) in
          let! gi =<< List.Indexing.Int.indexing (MatchState.input ms) (Z.min (MatchState.endIndex ms) beginMatch + i) in
          Coercions.wrap_bool Errors.MatchError.type (Character.canonicalize rer rsi !=? Character.canonicalize rer gi)%wt) = Success existsdiff ->
      existsdiff = true <-> (List.rev (List.firstn (Z.to_nat rlen) pref) ==? substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx))%wt = false.
  Proof.
    intros ms next pref startIdx endIdx beginMatch rlen existsdiff rer
      Hcasesenst Hrlennneg HeqbeginMatch HbeginMatchinb Hmsinp Heqrlen
      HstartIdxnneg HendIdxnneg Heqexistsdiff.
    destruct existsdiff.
    - (* There exists some different character *)
      apply List.Exists.true_to_prop in Heqexistsdiff.
      unfold List.Exists.Exist in Heqexistsdiff. destruct Heqexistsdiff as [i [i' [Hindexing Hdiff]]].
      assert (Heqi': i' = Z.of_nat i) by eauto using indexing_range_success. subst i'.
      pose proof List.Indexing.Nat.success_bounds _ _ _ Hindexing as Hinb.
      rewrite List.Range.Int.Bounds.length in Hinb. replace (rlen - 0)%Z with rlen in Hinb by lia.
      replace (Z.min _ beginMatch) with (MatchState.endIndex ms - rlen)%Z in Hdiff by lia.
      destruct List.Indexing.Int.indexing as [rsi|] eqn:Heqrsi in Hdiff; try discriminate.
      destruct List.Indexing.Int.indexing as [gi|] eqn:Hgi in Hdiff; try discriminate.
      simpl in Hdiff. do 2 rewrite canonicalize_casesenst in Hdiff by assumption.
      split; try reflexivity; intros _.
      apply string_diff_iff. exists i.
      replace (nth_error (rev (firstn _ _)) i) with (Some gi). 2: { symmetry; eapply backref_get_pref; eauto. lia. }
      replace (nth_error (substr _ _ _) i) with (Some rsi) by (symmetry; eauto using backref_get_ref).
      injection Hdiff as Hdiff. intro H. injection H as H.
      symmetry in H. apply neqb_neq in Hdiff. contradiction.
    - (* All characters are equal *)
      split; try discriminate.
      apply List.Exists.false_to_prop in Heqexistsdiff.
      intro H. exfalso. revert H. setoid_rewrite Bool.not_false_iff_true.
      apply string_eqb_iff. intro i.
      decide (i < Z.to_nat rlen) as Hinb.
      + (* Apply Heqexistsdiff *)
        specialize (Heqexistsdiff i (Z.of_nat i)). specialize_prove Heqexistsdiff by auto using indexing_range_inb_success'.
        simpl in Heqexistsdiff.
        replace (Z.min _ beginMatch) with (MatchState.endIndex ms - rlen)%Z in Heqexistsdiff by lia.
        destruct List.Indexing.Int.indexing as [rsi|] eqn:Heqrsi in Heqexistsdiff; try discriminate.
        destruct List.Indexing.Int.indexing as [gi|] eqn:Hgi in Heqexistsdiff; try discriminate.
        simpl in Heqexistsdiff. do 2 rewrite canonicalize_casesenst in Heqexistsdiff by assumption.
        injection Heqexistsdiff as Hdiff.
        replace (nth_error (rev (firstn _ _)) i) with (Some gi). 2: { symmetry; eapply backref_get_pref; eauto. lia. }
        replace (nth_error (substr _ _ _) i) with (Some rsi) by (symmetry; eauto using backref_get_ref).
        rewrite neqb_eq in Hdiff. congruence.
      + replace (nth_error _ i) with (None (A := Character)).
        2: { symmetry. apply nth_error_None. rewrite rev_length, firstn_length. lia. }
        replace (nth_error _ i) with (None (A := Character)).
        2: { symmetry. apply nth_error_None. transitivity (Z.to_nat endIdx - Z.to_nat startIdx). 2: lia.
          apply substr_len. }
        reflexivity.
  Qed.

  Lemma msinp_backref_fwd:
    forall ms next pref rlen endMatch ms' inp' str0,
      ms_matches_inp ms (Input next pref) ->
      input_compat (Input next pref) str0 ->
      ms' = match_state (MatchState.input ms) endMatch (MatchState.captures ms) ->
      inp' = Input (List.skipn (Z.to_nat rlen) next) (List.rev (List.firstn (Z.to_nat rlen) next) ++ pref)%list ->
      endMatch = (MatchState.endIndex ms + rlen)%Z ->
      (rlen >= 0)%Z ->
      (endMatch >? Z.of_nat (length (MatchState.input ms)))%Z = false ->
      ms_matches_inp ms' inp' /\ input_compat inp' str0.
  Proof.
    intros ms next pref rlen endMatch ms' inp' str0 Hmsinp Hinpcompat -> -> -> Hrlennneg Hinb.
    pose proof ms_matches_inp_inbounds _ _ Hmsinp as Horiginb.
    set (endInd' := Z.to_nat (MatchState.endIndex ms + rlen)).
    replace (MatchState.endIndex ms + rlen)%Z with (Z.of_nat endInd') by lia.
    inversion Hmsinp as [str0' endIndOrig cap next' pref' Hlenpref Heqstr0 Heqms]. inversion Hinpcompat as [next'' pref'' str0'' Heqstr0bis Heqnext'' Heqpref''].
    subst next' next'' pref' pref'' ms str0''. simpl in *.
    split; constructor.
    - rewrite app_length, rev_length, firstn_length_le; try lia.
      apply (f_equal (length (A := Character))) in Heqstr0. rewrite app_length, rev_length in Heqstr0. lia.
    - rewrite rev_app_distr. rewrite <- app_assoc. rewrite rev_involutive, firstn_skipn. auto.
    - rewrite rev_app_distr. rewrite <- app_assoc. rewrite rev_involutive, firstn_skipn. auto.
  Qed.

  Lemma msinp_backref_bwd:
    forall ms next pref rlen beginMatch ms' inp' str0,
      ms_matches_inp ms (Input next pref) ->
      input_compat (Input next pref) str0 ->
      ms' = match_state (MatchState.input ms) beginMatch (MatchState.captures ms) ->
      inp' = Input (rev (firstn (Z.to_nat rlen) pref) ++ next)%list (skipn (Z.to_nat rlen) pref) ->
      beginMatch = (MatchState.endIndex ms - rlen)%Z ->
      (rlen >= 0)%Z ->
      (beginMatch >= 0)%Z ->
      ms_matches_inp ms' inp' /\ input_compat inp' str0.
  Proof.
    intros ms next pref rlen beginMatch ms' inp' str0 Hmsinp Hinpcompat -> -> -> Hrlennneg Hinb.
    pose proof ms_matches_inp_inbounds _ _ Hmsinp as Horiginb.
    set (endInd' := Z.to_nat (MatchState.endIndex ms - rlen)).
    replace (MatchState.endIndex ms - rlen)%Z with (Z.of_nat endInd') by lia.
    inversion Hmsinp as [str0' endIndOrig cap next' pref' Hlenpref Heqstr0 Heqms]. inversion Hinpcompat as [next'' pref'' str0'' Heqstr0bis Heqnext'' Heqpref''].
    subst next' next'' pref' pref'' ms str0''. simpl in *.
    split; constructor.
    - rewrite skipn_length. lia.
    - rewrite app_assoc. rewrite <- rev_app_distr. rewrite firstn_skipn. auto.
    - rewrite app_assoc. rewrite <- rev_app_distr. rewrite firstn_skipn. auto.
  Qed.

  Lemma backref_inp'_idx_fwd:
    forall next pref inp' rlen startIdx endIdx,
      rlen = (endIdx - startIdx)%Z -> (rlen >= 0)%Z ->
      List.firstn (Z.to_nat rlen) next = substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx) ->
      inp' = Input (List.skipn (Z.to_nat rlen) next) (List.rev (List.firstn (Z.to_nat rlen) next) ++ pref)%list ->
      length pref + length (substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx)) = idx inp'.
  Proof.
    intros next pref inp' rlen startIdx endIdx -> Hrlennneg Hfirstn_next_substr ->.
    rewrite <- Hfirstn_next_substr.
    simpl. rewrite app_length, rev_length. lia. 
  Qed.

  Lemma backref_inp'_idx_bwd:
    forall next pref inp' rlen startIdx endIdx,
      rlen = (endIdx - startIdx)%Z -> (rlen >= 0)%Z -> (rlen <= Z.of_nat (length pref))%Z ->
      List.rev (List.firstn (Z.to_nat rlen) pref) = substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx) ->
      inp' = Input (List.rev (List.firstn (Z.to_nat rlen) pref) ++ next)%list (List.skipn (Z.to_nat rlen) pref) ->
      length pref - length (substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx)) = idx inp'.
  Proof.
    intros next pref inp' rlen startIdx endIdx -> Hrlennneg Hrlenle Hfirstn_pref_substr ->.
    rewrite <- Hfirstn_pref_substr.
    simpl. rewrite rev_length, skipn_length, firstn_length_le; lia.
  Qed.


  (* tree_res preserves validity of group maps *)
  Lemma tree_res_gm_valid:
    forall t gm idx dir,
      gm_valid gm -> gm_opt_valid (tree_res t gm idx dir).
  Proof.
    intro t. induction t as [ | | t1 IH1 t2 IH2 | | | | | act t IH | lk tlk IHlk tcont IHcont |].
    - constructor.
    - intros gm idx dir Hvalid. constructor. auto.
    - intros gm idx dir Hvalid. simpl.
      specialize (IH1 gm idx dir Hvalid). specialize (IH2 gm idx dir Hvalid).
      destruct (tree_res t1 gm idx dir); auto.
    - intros gm idx dir Hvalid. simpl. auto.
    - intros gm idx dir Hvalid. simpl. auto.
    - intros gm idx dir Hvalid. simpl. auto.
    - intros gm idx dir Hvalid. simpl. auto.
    - intros gm idx dir Hvalid. destruct act as [gid | gid | gl]; simpl.
      + apply IH. apply gm_open_valid. auto.
      + apply IH. apply gm_close_valid. auto.
      + apply IH. apply gm_reset_valid. auto.
    - intros gm idx dir Hvalid. simpl.
      destruct positivity.
      + specialize (IHlk gm idx (lk_dir lk) Hvalid). destruct (tree_res tlk gm idx _).
        * apply IHcont. inversion IHlk. auto.
        * constructor.
      + destruct tree_res; [constructor|auto].
    - constructor.
  Qed.

End EquivLemmas.
