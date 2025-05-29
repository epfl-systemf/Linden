From Linden Require Import Semantics FunctionalSemantics.
From Warblre Require Import Parameters.
From Coq Require Import Lia.

Section ComputeIsTree.
  Context `{characterClass: Character.class}.

  Lemma lk_succeeds_group_map:
    forall lk treelk gm idx,
      lk_succeeds lk treelk = true ->
      lk_group_map lk treelk gm idx <> None.
  Proof.
    intros lk treelk gm idx Hsucceeds.
    unfold lk_succeeds in Hsucceeds. unfold lk_group_map.
    destruct Regex.positivity. 2: discriminate.
    unfold Tree.first_branch in Hsucceeds.
    destruct Tree.tree_res as [res|] eqn:Hres; try discriminate.
    intro Habs. apply Tree.res_group_map_indep with (gm2 := Groups.GroupMap.empty) (idx2 := 0) (dir2 := Base.forward) in Habs.
    congruence.
  Qed.

  Lemma lk_succeeds_result:
    forall lk treelk,
      lk_succeeds lk treelk = true <-> lk_result lk treelk.
  Proof.
    intros lk treelk.
    unfold lk_succeeds, lk_result.
    destruct Regex.positivity.
    - destruct Tree.first_branch as [res|].
      + split; try reflexivity. intros _. eexists. reflexivity.
      + split. * discriminate. * intros [res H]; discriminate.
    - destruct Tree.first_branch as [res|].
      + split; discriminate.
      + split; reflexivity.
  Qed. 

  Theorem compute_is_tree:
    forall act inp gm dir fuel t,
      compute_tree act inp gm dir fuel = Some t ->
      is_tree act inp gm dir t.
  Proof.
    intros act inp gm dir fuel. revert act inp gm dir. induction fuel as [|fuel IHfuel]; try discriminate.

    intros act inp gm dir t. simpl.
    destruct act as [|[reg | inpcheck | gid] acts].
    1: { 
      intro H. injection H as <-. apply tree_done.
    }

    1: destruct reg as [ | cd | r1 r2 | r1 r2 | greedy min delta r | lk r | gid r | a | gid].

    - (* Empty *)
      intro H. apply tree_epsilon. auto.
    
    - (* Char *)
      destruct Chars.read_char as [[c nextinp]|] eqn:Hreadchar.
      + destruct (compute_tree acts nextinp gm dir fuel) as [treecont|] eqn:Hcomputecont; try discriminate.
        intro H. injection H as <-.
        apply tree_char with (nextinp := nextinp); auto.
      + intro H. injection H as <-.
        apply tree_char_fail. auto.
    
    - (* Disjunction *)
      destruct compute_tree as [t1|] eqn:Hcompute1; try discriminate.
      destruct (compute_tree (Areg r2 :: acts)%list inp gm dir fuel) as [t2|] eqn:Hcompute2; try discriminate.
      intro H. injection H as <-.
      apply tree_disj; auto.
    
    - (* Sequence *)
      intro Hcompsucc. apply tree_sequence. auto.
    
    - (* Quantified *)
      destruct min as [|min'].
      1: destruct delta as [[|n']|].
      + (* Done *)
        intro Hcomputesucc. apply tree_quant_done. auto.
      + (* Free, finite delta *)
        destruct compute_tree as [titer|] eqn:Hiter; simpl; try discriminate.
        destruct (compute_tree acts inp gm dir fuel) as [tskip|] eqn:Hskip; simpl; try discriminate.
        intro H. injection H as <-.
        change (Numeric.NoI.N (S n')) with (Numeric.NoI.add (Numeric.NoI.N 1) (Numeric.NoI.N n')).
        eapply tree_quant_free with (titer := titer) (tskip := tskip).
        * reflexivity.
        * apply IHfuel. simpl in Hiter. replace (n' - 0) with n' in Hiter by lia. auto.
        * auto.
        * reflexivity.
      + (* Free, infinite delta *)
        destruct compute_tree as [titer|] eqn:Hiter; simpl; try discriminate.
        destruct (compute_tree acts inp gm dir fuel) as [tskip|] eqn:Hskip; simpl; try discriminate.
        intro H. injection H as <-.
        change Numeric.NoI.Inf with (Numeric.NoI.add (Numeric.NoI.N 1) Numeric.NoI.Inf).
        eapply tree_quant_free with (titer := titer) (tskip := tskip).
        * reflexivity.
        * apply IHfuel. simpl in Hiter. auto.
        * auto.
        * reflexivity.
      + (* Forced *)
        destruct compute_tree as [titer|] eqn:Hiter; simpl; try discriminate.
        intro H. injection H as <-.
        auto using tree_quant_forced.
    
    - (* Lookaround *)
      destruct compute_tree as [treelk|] eqn:Htreelk; simpl; try discriminate.
      destruct lk_succeeds eqn:Hlksucc.
      + (* Lookaround succeds *)
        pose proof lk_succeeds_group_map lk treelk gm (idx inp) Hlksucc as Hlkgm_not_None.
        destruct lk_group_map as [gmlk|] eqn:Hgmlk; try contradiction.
        destruct (compute_tree acts inp gmlk dir fuel) as [treecont|] eqn:Hcomputecont; try discriminate.
        intro H. injection H as <-.
        apply tree_lk with (gmlk := gmlk); auto. now apply lk_succeeds_result.
      + (* Lookaround fails *)
        intro H. injection H as <-.
        apply tree_lk_fail; auto. intro Habs. apply lk_succeeds_result in Habs. congruence.

    - (* Group *)
      destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
      intro H. injection H as <-.
      apply tree_group. auto.

    - (* Anchor *)
      destruct anchor_satisfied eqn:Hanchor.
      + (* Anchor is satisfied *)
        destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
        intro H. injection H as <-.
        apply tree_anchor; auto.
      + (* Anchor is not satisfied *)
        intro H. injection H as <-.
        apply tree_anchor_fail; auto.
    
    - (* Backreference *)
      destruct read_backref as [[br_str nextinp]|] eqn:Hreadbr.
      + (* Success *)
        destruct compute_tree as [tcont|] eqn:Htcont; try discriminate.
        intro H. injection H as <-.
        apply tree_backref with (nextinp := nextinp); auto.
      + (* Failure *)
        intro H. injection H as <-.
        auto using tree_backref_fail.
    
    - (* Check *)
      (* That's false... *)
      admit.

    - (* Close *)
      destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
      intro H. injection H as <-.
      apply tree_close. auto.
  Admitted.