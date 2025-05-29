From Linden Require Import Semantics FunctionalSemantics Chars.
From Warblre Require Import Parameters Base.
From Coq Require Import Lia List.

Section ComputeIsTree.
  Context `{characterClass: Character.class}.

  Definition inp_valid_check (inp strcheck: input) (dir: Direction): Prop :=
    inp = strcheck \/ strict_suffix inp strcheck dir.

  Definition inp_valid_checks (inp: input) (acts: actions) (dir: Direction) :=
    forall strcheck, In (Acheck strcheck) acts -> inp_valid_check inp strcheck dir.

  Lemma inp_valid_checks_tail:
    forall inp act acts dir,
      inp_valid_checks inp (act :: acts)%list dir -> inp_valid_checks inp acts dir.
  Admitted.

  Lemma inp_valid_checks_Areg:
    forall inp reg acts dir,
      inp_valid_checks inp acts dir -> inp_valid_checks inp (Areg reg :: acts)%list dir.
  Admitted.

  Lemma inp_valid_checks_Aclose:
    forall inp gid acts dir,
      inp_valid_checks inp acts dir -> inp_valid_checks inp (Aclose gid :: acts)%list dir.
  Admitted.

  Lemma inp_valid_checks_Acheck:
    forall inp strcheck acts dir,
      inp_valid_checks inp acts dir ->
      inp_valid_check inp strcheck dir ->
      inp_valid_checks inp (Acheck strcheck :: acts)%list dir.
  Admitted.

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
      inp_valid_checks inp act dir ->
      is_tree act inp gm dir t.
  Proof.
    intros act inp gm dir fuel. revert act inp gm dir. induction fuel as [|fuel IHfuel]; try discriminate.

    intros act inp gm dir t. simpl.
    destruct act as [|[reg | inpcheck | gid] acts].
    1: { 
      intros H _. injection H as <-. apply tree_done.
    }

    1: destruct reg as [ | cd | r1 r2 | r1 r2 | greedy min delta r | lk r | gid r | a | gid].

    - (* Empty *)
      intros H Hvalidchecks. apply tree_epsilon. apply IHfuel; auto. eauto using inp_valid_checks_tail.
    
    - (* Char *)
      destruct Chars.read_char as [[c nextinp]|] eqn:Hreadchar.
      + destruct (compute_tree acts nextinp gm dir fuel) as [treecont|] eqn:Hcomputecont; try discriminate.
        intros H Hvalidchecks. injection H as <-.
        apply tree_char with (nextinp := nextinp); auto.
        apply IHfuel; auto.
        apply inp_valid_checks_tail in Hvalidchecks.
        admit. (* Advancing the input does not affect validity wrt checks *)
      + intros H Hvalidchecks. injection H as <-.
        apply tree_char_fail. auto.
    
    - (* Disjunction *)
      destruct compute_tree as [t1|] eqn:Hcompute1; try discriminate.
      destruct (compute_tree (Areg r2 :: acts)%list inp gm dir fuel) as [t2|] eqn:Hcompute2; try discriminate.
      intros H Hvalidchecks. injection H as <-.
      apply tree_disj; apply IHfuel; auto; apply inp_valid_checks_Areg; now apply inp_valid_checks_tail in Hvalidchecks.
    
    - (* Sequence *)
      intros Hcompsucc Hvalidchecks. apply tree_sequence; apply IHfuel; auto.
      destruct dir; simpl; do 2 apply inp_valid_checks_Areg; now apply inp_valid_checks_tail in Hvalidchecks.
    
    - (* Quantified *)
      destruct min as [|min'].
      1: destruct delta as [[|n']|].
      + (* Done *)
        intros Hcomputesucc Hvalidchecks. apply tree_quant_done; apply IHfuel; auto.
        eauto using inp_valid_checks_tail.
      + (* Free, finite delta *)
        destruct compute_tree as [titer|] eqn:Hiter; simpl; try discriminate.
        destruct (compute_tree acts inp gm dir fuel) as [tskip|] eqn:Hskip; simpl; try discriminate.
        intros H Hvalidchecks. injection H as <-.
        change (Numeric.NoI.N (S n')) with (Numeric.NoI.add (Numeric.NoI.N 1) (Numeric.NoI.N n')).
        eapply tree_quant_free with (titer := titer) (tskip := tskip).
        * reflexivity.
        * apply IHfuel.
          -- simpl in Hiter. replace (n' - 0) with n' in Hiter by lia. auto.
          -- (* Adding a check to self *) admit.
        * apply IHfuel; auto. eauto using inp_valid_checks_tail.
        * reflexivity.
      + (* Free, infinite delta *)
        destruct compute_tree as [titer|] eqn:Hiter; simpl; try discriminate.
        destruct (compute_tree acts inp gm dir fuel) as [tskip|] eqn:Hskip; simpl; try discriminate.
        intros H Hvalidchecks. injection H as <-.
        change Numeric.NoI.Inf with (Numeric.NoI.add (Numeric.NoI.N 1) Numeric.NoI.Inf).
        eapply tree_quant_free with (titer := titer) (tskip := tskip).
        * reflexivity.
        * apply IHfuel.
          -- simpl in Hiter. auto.
          -- (* Adding a check to self *) admit.
        * apply IHfuel; auto. eauto using inp_valid_checks_tail.
        * reflexivity.
      + (* Forced *)
        destruct compute_tree as [titer|] eqn:Hiter; simpl; try discriminate.
        intros H Hvalidchecks. injection H as <-.
        apply tree_quant_forced; auto.
        apply IHfuel; auto.
        do 2 apply inp_valid_checks_Areg. now apply inp_valid_checks_tail in Hvalidchecks.
    
    - (* Lookaround *)
      destruct compute_tree as [treelk|] eqn:Htreelk; simpl; try discriminate.
      destruct lk_succeeds eqn:Hlksucc.
      + (* Lookaround succeds *)
        pose proof lk_succeeds_group_map lk treelk gm (idx inp) Hlksucc as Hlkgm_not_None.
        destruct lk_group_map as [gmlk|] eqn:Hgmlk; try contradiction.
        destruct (compute_tree acts inp gmlk dir fuel) as [treecont|] eqn:Hcomputecont; try discriminate.
        intros H Hvalidchecks. injection H as <-.
        apply tree_lk with (gmlk := gmlk); auto.
        * apply IHfuel; auto. (* Valid wrt no checks *) admit.
        * now apply lk_succeeds_result.
        * apply IHfuel; auto. now apply inp_valid_checks_tail in Hvalidchecks.
      + (* Lookaround fails *)
        intros H Hvalidchecks. injection H as <-.
        apply tree_lk_fail; auto.
        * apply IHfuel; auto. (* Valid wrt no checks *) admit.
        * intro Habs. apply lk_succeeds_result in Habs. congruence.

    - (* Group *)
      destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
      intros H Hvalidchecks. injection H as <-.
      apply tree_group. auto. apply IHfuel; auto.
      apply inp_valid_checks_Areg, inp_valid_checks_Aclose. now apply inp_valid_checks_tail in Hvalidchecks.

    - (* Anchor *)
      destruct anchor_satisfied eqn:Hanchor.
      + (* Anchor is satisfied *)
        destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
        intros H Hvalidchecks. injection H as <-.
        apply tree_anchor; auto. apply IHfuel; auto. now apply inp_valid_checks_tail in Hvalidchecks.
      + (* Anchor is not satisfied *)
        intros H Hvalidchecks. injection H as <-.
        apply tree_anchor_fail; auto.
    
    - (* Backreference *)
      destruct read_backref as [[br_str nextinp]|] eqn:Hreadbr.
      + (* Success *)
        destruct compute_tree as [tcont|] eqn:Htcont; try discriminate.
        intros H Hvalidchecks. injection H as <-.
        apply tree_backref with (nextinp := nextinp); auto. apply IHfuel; auto. apply inp_valid_checks_tail in Hvalidchecks.
        (* nextinp has progressed wrt inp; lemma already stated somewhere, I think? *) admit.
      + (* Failure *)
        intro H. injection H as <-.
        auto using tree_backref_fail.
    
    - (* Check *)
      destruct is_strict_suffix eqn:Hssuffix.
      + (* Is strict suffix *)
        destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
        intros H Hvalidchecks. injection H as <-.
        apply tree_check; auto.
        * (* follows from Hssuffix *) admit.
        * apply IHfuel; auto. now apply inp_valid_checks_tail in Hvalidchecks.
      + (* Is not strict suffix *)
        intros H Hvalidchecks. injection H as <-.
        apply tree_check_fail. (* Now follows from Hvalidchecks and Hssuffix! *) admit.


    - (* Close *)
      destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
      intros H Hvalidchecks. injection H as <-.
      apply tree_close. apply IHfuel; auto. now apply inp_valid_checks_tail in Hvalidchecks.
  Admitted.