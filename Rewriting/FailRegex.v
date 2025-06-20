From Linden Require Import ProofSetup.
From Linden Require Import ExampleRegexes.

Section FailRegex.
  Context {char: Parameters.Character.class}.

  Lemma fail_regex_fail:
    forall inp gm dir t,
      is_tree [Areg fail_regex] inp gm dir t ->
      tree_leaves t gm inp dir = [].
  Proof.
    intros inp gm dir t TREE.
    unfold fail_regex in TREE. inversion TREE; subst.
    rewrite app_nil_r in CONT. destruct dir; simpl in *.
    - inversion CONT; subst; simpl in *. 2: reflexivity.
      (* ?!. matches *)
      inversion TREELK; subst.
      1: { (* Impossible *) 
        unfold lk_result in RES_LK. simpl in RES_LK.
        inversion TREECONT0; subst. discriminate.
      }
      simpl. inversion TREECONT; subst.
      1: congruence. (* Impossible *)
      reflexivity.
    - inversion CONT; subst. 2: reflexivity.
      (* Now the right dot matches, so inp is not at the beginning of the string,
      and nextinp is not at the end of the string *)
      inversion TREECONT; subst; simpl. 2: reflexivity.
      (* The negative lookahead cannot succeed: impossible *)
      unfold lk_result in RES_LK. simpl in RES_LK.
      inversion TREELK; subst; simpl.
      + inversion TREECONT1; subst. discriminate.
      + destruct inp as [next pref]. simpl in READ.
        destruct pref as [|x pref']; try discriminate.
        injection READ as -> <-. discriminate.
  Qed.
End FailRegex.