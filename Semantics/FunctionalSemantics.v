Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars.
From Linden Require Import Tree.
From Linden Require Import NumericLemmas.
From Linden Require Import Groups Semantics.
From Warblre Require Import Numeric Base.

From Coq Require Import Lia.
(* From Coq Require Import Program. *)

Section FunctionalSemantics.
  Context `{characterClass: Character.class}.


  (** * Suffixes  *)

  (* advance_input is the next suffix *)
  (* but now we explore the transitive closure of this relation *)

  Inductive strict_suffix : input -> input -> Direction -> Prop :=
  | ss_advance:
    forall inp nextinp dir,
      advance_input inp dir = Some nextinp ->
      strict_suffix nextinp inp dir
  | ss_next:
    forall inp1 inp2 inp3 dir,
      advance_input inp2 dir = Some inp1 ->
      strict_suffix inp2 inp3 dir ->
      strict_suffix inp1 inp3 dir.


  (* Another, functional, version of strict suffix *)
  Fixpoint strict_suffix_forward (inp:input) (next pref:string): bool :=
    match next with
    | [] => false                  (* cannot be a strict suffix of the end of string *)
    | c::next' =>
        if (Input next' (c::pref) ==? inp)%wt then true
        else strict_suffix_forward inp next' (c::pref)
    end.

  Fixpoint strict_suffix_backward (inp:input) (next pref:string): bool :=
    match pref with
    | [] => false                  (* cannot be a (backward) strict suffix of the beginning of string *)
    | c::pref' =>
        if (Input (c::next) pref' ==? inp)%wt then true
        else strict_suffix_backward inp (c::next) pref'
    end.

  Definition is_strict_suffix (inp1 inp2:input) (dir:Direction) : bool :=
    match inp2 with
    | Input next2 pref2 =>
        match dir with
        | forward => strict_suffix_forward inp1 next2 pref2
        | backward => strict_suffix_backward inp1 next2 pref2
        end
    end.

  Lemma ss_next':
    forall inp1 inp2 inp3 dir,
      strict_suffix inp1 inp2 dir ->
      advance_input inp3 dir = Some inp2 ->
      strict_suffix inp1 inp3 dir.
  Proof.
    intros inp1 inp2 inp3 dir H12. revert inp3. induction H12 as [inp2 inp1 dir H12 | inp1 inp2 inp3 dir H12 H23 IH].
    - intros inp3 H23. eauto using ss_next, ss_advance.
    - intros inp4 H34. eauto using ss_next, ss_advance, IH.
  Qed.

  Lemma ss_next'_inv:
    forall inp1 inp2 inp3 dir,
      advance_input inp2 dir = Some inp1 ->
      strict_suffix inp2 inp3 dir ->
      exists inp2',
        strict_suffix inp1 inp2' dir /\
        advance_input inp3 dir = Some inp2'.
  Admitted.

  Lemma strict_suffix_ind':
    forall (P: input -> input -> Direction -> Prop)
      (Hadvance: forall inp nextinp dir,
      advance_input inp dir = Some nextinp -> P nextinp inp dir)
      (Hnext': forall inp1 inp2 inp3 dir,
        P inp1 inp2 dir ->
        advance_input inp3 dir = Some inp2 ->
        P inp1 inp3 dir),
      forall inp1 inp2 dir,
        strict_suffix inp1 inp2 dir -> P inp1 inp2 dir.
  Admitted.

  Lemma strict_suffix_forward_sound:
    forall inp next pref,
      strict_suffix_forward inp next pref = true -> strict_suffix inp (Input next pref) forward.
  Proof.
    intros inp next. induction next as [|c next' IH].
    1: discriminate.
    intro pref. simpl.
    destruct (Input next' (c::pref) ==? inp)%wt eqn:Hequal.
    1: { rewrite EqDec.inversion_true in Hequal. intros _. apply ss_advance. subst inp. reflexivity. }
    intro H. specialize (IH (c::pref) H).
    eapply ss_next'; eauto.
  Qed.

  Lemma strict_suffix_forward_complete:
    forall inp next pref,
      strict_suffix inp (Input next pref) forward -> strict_suffix_forward inp next pref = true.
  Admitted.

  Lemma strict_suffix_backward_sound:
    forall inp next pref,
      strict_suffix_backward inp next pref = true -> strict_suffix inp (Input next pref) backward.
  Proof.
    intros inp next pref. revert next. induction pref as [|c pref' IH].
    1: discriminate.
    intro next. simpl.
    destruct (Input (c::next) pref' ==? inp)%wt eqn:Hequal.
    1: { rewrite EqDec.inversion_true in Hequal. intros _. apply ss_advance. subst inp. reflexivity. }
    intro H. specialize (IH (c::next) H).
    eapply ss_next'; eauto.
  Qed.

  Lemma strict_suffix_backward_complete:
    forall inp next pref,
      strict_suffix inp (Input next pref) backward -> strict_suffix_backward inp next pref = true.
  Admitted.

  Theorem is_strict_suffix_correct:
    forall inp1 inp2 dir,
      is_strict_suffix inp1 inp2 dir = true <-> strict_suffix inp1 inp2 dir.
  Proof.
    intros [next1 pref1] [next2 pref2] dir. destruct dir; simpl.
    - split; intro.
      + now apply strict_suffix_forward_sound.
      + now apply strict_suffix_forward_complete.
    - split; intro.
      + now apply strict_suffix_backward_sound.
      + now apply strict_suffix_backward_complete.
  Qed.

  Theorem strict_suffix_current:
    forall inp1 inp2 dir,
      strict_suffix inp1 inp2 dir ->
      length (current_str inp1 dir) < length (current_str inp2 dir).
  Proof.
    intros [next1 pref1] [next2 pref2] dir H.
    rewrite <- is_strict_suffix_correct in H.
    unfold is_strict_suffix in H. destruct dir.
    - generalize dependent pref2. induction next2; intros.
      { inversion H. }
      simpl. simpl in IHnext2. simpl in H.
      destruct ((Input next2 (a :: pref2) ==? Input next1 pref1)%wt) eqn:INPEQ.
      + rewrite EqDec.inversion_true in INPEQ. inversion INPEQ. subst. lia.
      + apply IHnext2 in H. lia.
    - generalize dependent next2. induction pref2; intros.
      { inversion H. }
      simpl. simpl in IHpref2. simpl in H.
      destruct ((Input (a::next2) pref2 ==? Input next1 pref1)%wt) eqn:INPEQ.
      + rewrite EqDec.inversion_true in INPEQ. inversion INPEQ. subst. lia.
      + apply IHpref2 in H. lia.
  Qed.

  Theorem read_suffix:
    forall inp dir nextinp,
      advance_input inp dir = Some nextinp ->
      strict_suffix nextinp inp dir.
  Proof.
    intros inp dir nextinp H. constructor. auto.
  Qed.

  Lemma advance_current_plus_one:
    forall inp1 inp2 dir,
      advance_input inp2 dir = Some inp1 ->
      length (current_str inp2 dir) = S (length (current_str inp1 dir)).
  Proof.
    intros [next1 pref1] [next2 pref2] [|] H; simpl in H.
    - destruct next2; inversion H. simpl. auto.
    - destruct pref2; inversion H. simpl. auto.
  Qed.

  Theorem read_char_suffix:
    forall inp dir nextinp cd c,
      read_char cd inp dir = Some (c, nextinp) ->
      strict_suffix nextinp inp dir.
  Proof.
    intros [next pref] dir nextinp cd c H.  destruct dir; simpl in H.
    - destruct next; inversion H. destruct (char_match t cd); inversion H; subst.
      apply read_suffix. simpl. auto.
    - destruct pref; inversion H. destruct (char_match t cd); inversion H; subst.
      apply read_suffix. simpl. auto.
  Qed.


  Theorem strict_suffix_trans:
    forall inp1 inp2 inp3 dir,
      strict_suffix inp1 inp2 dir ->
      strict_suffix inp2 inp3 dir ->
      strict_suffix inp1 inp3 dir.
  Proof.
    intros inp1 inp2 inp3 dir H H0. induction H.
    - eapply ss_next; eauto.
    - eapply ss_next; eauto.
  Qed.

  Lemma strict_advance:
    forall inp1 inp2 dir nextinp1,
      strict_suffix inp1 inp2 dir ->
      advance_input inp1 dir = Some nextinp1 ->
      exists nextinp2, advance_input inp2 dir = Some nextinp2 /\
                    strict_suffix nextinp1 nextinp2 dir.
  Proof.
  Admitted.

  Lemma strict_no_advance:
    forall inp1 inp2 dir,
      strict_suffix inp1 inp2 dir ->
      advance_input inp2 dir = None ->
      False.
  Proof.
  Admitted.

  Lemma advance_suffix:
    forall inp inpnext inpsuf dir,
      strict_suffix inpsuf inp dir ->
      advance_input inp dir = Some inpnext ->
      inpnext = inpsuf \/ strict_suffix inpsuf inpnext dir.
  Proof.
  Admitted.


  (** * Total input  *)

  (* When computing fuel, what's the worst possible string we could have to match in a given direction *)
  (* This is used for lookarounds fuel: since they may change direction, we can't predict ahead of time  *)
  (* how much string they'll get to work with from the current input *)
  Definition worst_input (inp:input) (dir:Direction) : input :=
    match inp with
    | Input next pref =>
        match dir with
        | forward => Input ((rev pref) ++ next) []
        | backward => Input [] ((rev next) ++ pref)
        end
    end.

  Lemma suffix_same_worst:
    forall inp1 inp2 d,
      strict_suffix inp1 inp2 d ->
      (forall dir, worst_input inp1 dir = worst_input inp2 dir).
  Proof.
  Admitted.                       (* suffixes have the same total string *)

  Lemma worst_input_suffix:
    forall inp worst dir,
      worst_input inp dir = worst ->
      worst = inp \/ strict_suffix inp worst dir.
  Proof.
  Admitted.


  (** * Computing the measure  *)

  (* Get the current string index from the input *)
  Definition idx (inp:input) : nat :=
    match inp with
    | Input next pref => List.length pref
    end.

  (* The predecessor of a non_negative or infinite delta of a quantifier *)
  Definition noi_pred (noi:non_neg_integer_or_inf) : non_neg_integer_or_inf :=
    match noi with
    | NoI.N x => NoI.N (x - 1)
    | NoI.Inf => NoI.Inf
    end.


  (* The maximum number of iterations for a quantifier *)
  Definition max_iter (inp:input) (dir:Direction): nat :=
    1 + length (current_str inp dir).

  Lemma strict_suffix_max_iter:
    forall inp1 inp2 dir,
      strict_suffix inp1 inp2 dir ->
      max_iter inp1 dir < max_iter inp2 dir.
  Proof.
    intros inp1 inp2 dir H. apply strict_suffix_current in H.
    unfold max_iter. lia.
  Qed.

  Lemma advance_max_iter:
    forall inp nextinp dir,
      advance_input inp dir = Some nextinp ->
      max_iter inp dir = S (max_iter nextinp dir).
  Proof.
    intros [next pref] nextinp [|] H; simpl in H.
    - destruct next; inversion H. auto.
    - destruct pref; inversion H. auto.
  Qed.

  Lemma no_advance_max_iter:
    forall inp dir,
      advance_input inp dir = None ->
      max_iter inp dir = 1.
  Proof.
    intros [next pref] dir H. unfold max_iter. destruct dir; simpl in *.
    - destruct next; inversion H. auto.
    - destruct pref; inversion H. auto.
  Qed.


  (* An upper bound on the number of actions required for a regex *)
  Fixpoint regex_fuel (r:regex) (inp:input) (dir:Direction) : nat :=
    match r with
    | Epsilon => 1
    | Regex.Character _ => 1
    | Disjunction r1 r2 =>
        1 + (regex_fuel r1 inp dir) + (regex_fuel r2 inp dir)
    | Sequence r1 r2 =>
        1 + (regex_fuel r1 inp dir) + (regex_fuel r2 inp dir)
    | Quantified b min delta r1 =>
        let rfuel := regex_fuel r1 inp dir in
        (2 + rfuel) * (min + max_iter inp dir)
    | Lookaround lk r1 =>
        1 + (regex_fuel r1 (worst_input inp (lk_dir lk)) (lk_dir lk))
    | Group _ r1 =>
        2 + (regex_fuel r1 inp dir)
    | Anchor _ => 1
    | Backreference _ => 1
    end.

  Fixpoint actions_fuel (act:actions) (inp:input) (dir:Direction) : nat :=
    match act with
    | [] => 1
    | (Areg r)::l => (regex_fuel r inp dir) + (actions_fuel l inp dir)
    | (Acheck inpcheck)::l =>
        (* advance_input is the next closest possible input after having passed a check *)
        match (advance_input inpcheck dir) with
        | Some nextinp => 1 + actions_fuel l nextinp dir
        | None => 0
        end
    | (Aclose _):: l => 1 + (actions_fuel l inp dir)
    end.

  (** * Monotony Lemmas  *)

  Lemma regex_monoton:
    forall r dir inp1 inp2,
      strict_suffix inp1 inp2 dir ->
      regex_fuel r inp1 dir <= regex_fuel r inp2 dir.
  Proof.
    intros r dir inp1 inp2 H.
    induction r; simpl; try lia.
    - apply strict_suffix_max_iter in H as MAX.
      apply PeanoNat.Nat.add_le_mono; try lia.
      apply PeanoNat.Nat.add_le_mono; try lia.
      apply PeanoNat.Nat.mul_le_mono; try lia.
    - apply suffix_same_worst with (dir:=lk_dir lk) in H as WORST.
      rewrite WORST. lia.
  Qed.

  Lemma actions_monoton:
    forall act dir inp1 inp2,
      strict_suffix inp1 inp2 dir ->
      actions_fuel act inp1 dir <= actions_fuel act inp2 dir.
  Proof.
    intros act dir inp1 inp2 H. induction act.
    { simpl. lia. }
    destruct a.
    - simpl. apply regex_monoton with (r:=r) in H as R. lia.
    - simpl. destruct (advance_input i dir) eqn:ADV; try lia.
    - simpl. lia.
  Qed.

  (** * Termination Lemmas  *)
  (* Proving, for each recursive call, that the measure strictly decreases *)

  Lemma check_termination:
    forall cont inp strcheck dir,
      strict_suffix inp strcheck dir ->
      actions_fuel cont inp dir < actions_fuel (Acheck strcheck :: cont) inp dir.
  Proof.
    intros cont inp strcheck dir SS.
    simpl. destruct (advance_input strcheck dir) eqn:ADV.
    2: { exfalso. eapply strict_no_advance; eauto. }
    generalize (advance_suffix _ _ _ _ SS ADV). intros [INPEQ | SS2].
    - subst. lia.
    - generalize (actions_monoton cont _ _ _ SS2). intros H. lia.
  Qed.

  Lemma close_termination:
    forall cont inp dir gid,
      actions_fuel cont inp dir < actions_fuel (Aclose gid :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma epsilon_termination:
    forall cont inp dir,
      actions_fuel cont inp dir < actions_fuel (Areg Epsilon :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma character_termination:
    forall cont inp dir cd c nextinp,
      read_char cd inp dir = Some (c, nextinp) ->
      actions_fuel cont nextinp dir < actions_fuel (Areg (Regex.Character cd) :: cont) inp dir.
  Proof.
    intros cont inp dir cd c nextinp H. apply read_char_suffix in H. simpl.
    apply actions_monoton with (act:=cont) in H. lia.
  Qed.

  Lemma disjunction_left_termination:
    forall cont inp dir r1 r2,
      actions_fuel (Areg r1 :: cont) inp dir < actions_fuel (Areg (Disjunction r1 r2) :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma disjunction_right_termination:
    forall cont inp dir r1 r2,
      actions_fuel (Areg r2 :: cont) inp dir < actions_fuel (Areg (Disjunction r1 r2) :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma sequence_termination:
    forall cont inp dir r1 r2,
      actions_fuel (seq_list r1 r2 dir ++ cont) inp dir < actions_fuel (Areg (Sequence r1 r2) :: cont) inp dir.
  Proof. intros. destruct dir; simpl; lia. Qed.

  Lemma quant_forced_termination:
    forall cont inp dir r1 min delta greedy,
      actions_fuel (Areg r1 :: Areg (Quantified greedy min delta r1) :: cont) inp dir <
        actions_fuel (Areg (Quantified greedy (S min) delta r1) :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma quant_done_termination:
    forall cont inp dir r1 greedy,
      actions_fuel cont inp dir < actions_fuel (Areg (Quantified greedy 0 (NoI.N 0) r1) :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma quant_free_skip_termination:
    forall cont inp dir r1 greedy delta,
      actions_fuel cont inp dir < actions_fuel (Areg (Quantified greedy 0 delta r1)::cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma le_lt_S:
    forall n m,
      n <= m -> n < S m.
  Proof. lia. Qed.

  Lemma quant_free_iter_termination:
    forall cont inp dir r1 greedy delta,
      actions_fuel (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) inp dir <
        actions_fuel (Areg (Quantified greedy 0 delta r1) :: cont) inp dir.
  Proof.
    intros cont inp dir r1 greedy delta.
    destruct (advance_input inp dir) eqn:ADV; simpl; rewrite ADV.
    (* it's not possible to pass the check *)
    2: { apply no_advance_max_iter in ADV. rewrite ADV. lia. }
    apply read_suffix in ADV as SS.
    apply regex_monoton with (r:=r1) in SS as SMALLER_R.
    apply actions_monoton with (act:=cont) in SS as SMALLER_CONT.
    apply advance_current_plus_one in ADV as SMALLER_LEN.
    rewrite SMALLER_LEN.
    apply advance_max_iter in ADV as SMALLER_MAX.
    rewrite SMALLER_MAX.
    assert (RMAX: regex_fuel r1 i dir * max_iter i dir <= regex_fuel r1 inp dir * max_iter i dir).
    { apply GroupId.mul_le_mono_r. auto. }
    lia.
    (* used before lia worked, to inspect the measure calculation *)
    (* pose (R2 := regex_fuel r1 inp dir). fold R2. fold R2 in SMALLER_R. *)
    (* pose (R1 := regex_fuel r1 i dir). fold R1. fold R1 in SMALLER_R. *)
    (* pose (ACT2 := actions_fuel cont inp dir). fold ACT2. fold ACT2 in SMALLER_CONT. *)
    (* pose (ACT1 := actions_fuel cont i dir). fold ACT1. fold ACT1 in SMALLER_CONT. *)
    (* pose (MAX := max_iter i dir). fold MAX. fold MAX in SMALLER_MAX. *)
    (* pose (LEN := length (current_str i dir)). fold LEN. *)
  Qed.

  Lemma group_termination:
    forall cont inp dir r1 gid,
      actions_fuel (Areg r1 :: Aclose gid :: cont) inp dir < actions_fuel (Areg (Group gid r1) :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.



  (** * Computing a tree  *)


  Fixpoint compute_tree (act: actions) (inp: input) (gm: group_map) (dir: Direction) (fuel:nat): option tree :=
    match fuel with
    | 0 => None
    | S fuel => 
        match act with
        (* tree_done *)
        | [] => Some Match
        (* tree_check, tree_check_fail *)
        | Acheck strcheck :: cont =>
            if (is_strict_suffix inp strcheck dir) then
              match (compute_tree cont inp gm dir fuel) with
              | Some treecont => Some (Progress strcheck treecont)
              | None => None
              end
            else Some Mismatch            
        (* tree_close *)
        | Aclose gid :: cont =>
            match (compute_tree cont inp (GroupMap.close (idx inp) gid gm) dir fuel) with
            | Some treecont => Some (GroupAction (Close gid) treecont)
            | None => None
            end          
        (* tree_epsilon *)
        | Areg Epsilon::cont => compute_tree cont inp gm dir fuel
        (* tree_char, tree_char_fail *)
        | Areg (Regex.Character cd)::cont =>
            match read_char cd inp dir with
            | Some (c, nextinp) =>
                match (compute_tree cont nextinp gm dir fuel) with
                | Some treecont => Some (Read c treecont)
                | None => None
                end
            | None => Some Mismatch
                end
        (* tree_disj *)
        | Areg (Disjunction r1 r2)::cont =>
            match (compute_tree (Areg r1 :: cont) inp gm dir fuel, compute_tree (Areg r2 :: cont) inp gm dir fuel) with
            | (Some t1, Some t2) => Some (Choice t1 t2)
            | _ => None
            end
        (* tree_sequence *)
        | Areg (Sequence r1 r2)::cont =>
            compute_tree (seq_list r1 r2 dir ++ cont) inp gm dir fuel
        (* tree_quant_forced *)
        | Areg (Quantified greedy (S min) delta r1)::cont =>
            let gidl := def_groups r1 in
            match compute_tree (Areg r1 :: Areg (Quantified greedy min delta r1) :: cont) inp (GroupMap.reset gidl gm) dir fuel with
            | Some titer => Some (GroupAction (Reset gidl) titer)
            | None => None
            end          
        (* tree_quant_done *)
        | Areg (Quantified greedy 0 (NoI.N 0) r1)::cont =>
            compute_tree cont inp gm dir fuel
        (* tree_quant_free *)
        | Areg (Quantified greedy 0 delta r1)::cont =>
            let gidl := def_groups r1 in
            match  (compute_tree (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) inp (GroupMap.reset gidl gm) dir fuel, compute_tree cont inp gm dir fuel) with
            | (Some titer, Some tskip) =>  Some (greedy_choice greedy (GroupAction (Reset gidl) titer) tskip)
            | _ => None
            end
        (* tree_group *)
        | Areg (Group gid r1)::cont =>
            match compute_tree (Areg r1 :: Aclose gid :: cont) inp (GroupMap.open (idx inp) gid gm) dir fuel with
            | Some treecont => Some (GroupAction (Open gid) treecont)
            | _ => None
            end          
        (* tree_lk, tree_lk_fail, tree_anchor, tree_anchor_fail, tree_backref, tree_backref_fail: TODO *)
        | _ => Some Mismatch
        end
    end.
    
  (** * Functional Semantics Termination  *)

  Lemma somenone:
    forall T (x:T), Some x <> None.
  Proof.
    intros T x. unfold not. intros H. inversion H.
  Qed.

  Lemma noi_destruct:
    forall n, n = NoI.N 0 \/ n <> NoI.N 0.
  Proof.
    destruct n.
    2: { right. unfold not. intros H. inversion H. }
    destruct n.
    - left. auto.
    - right. unfold not. intros H. inversion H.
  Qed.

  Theorem functional_terminates:
    forall act inp gm dir fuel,
      fuel > actions_fuel act inp dir ->
      compute_tree act inp gm dir fuel <> None.
  Proof.
    intros act inp gm dir fuel H.
    generalize dependent act. generalize dependent inp. 
    generalize dependent gm. generalize dependent dir.
    induction fuel; intros.
    { inversion H. }
    destruct act as [|a act].
    { simpl. apply somenone. }
    destruct a.
    - destruct r.
      + simpl. generalize (epsilon_termination act inp dir). intros.
        assert (ENOUGH: fuel > actions_fuel act inp dir) by lia.
        apply IHfuel with (gm:=gm) in ENOUGH.
        destruct (compute_tree act inp gm dir fuel); try contradiction.
        apply somenone.
      + simpl. destruct (read_char cd inp dir) eqn:READ; try apply somenone.
        destruct p as [c nextinp].
        generalize (character_termination act inp dir cd c nextinp READ). intros.
        assert (ENOUGH: fuel > actions_fuel act nextinp dir) by lia.
        apply IHfuel with (gm:=gm) in ENOUGH.
        destruct (compute_tree act nextinp gm dir fuel); try contradiction.
        apply somenone.
      + simpl. generalize (disjunction_left_termination act inp dir r1 r2). intros.
        generalize (disjunction_right_termination act inp dir r1 r2). intros.
        assert (ENOUGH1: fuel > actions_fuel (Areg r1::act) inp dir) by lia.
        assert (ENOUGH2: fuel > actions_fuel (Areg r2::act) inp dir) by lia.
        apply IHfuel with (gm:=gm) in ENOUGH1. apply IHfuel with (gm:=gm) in ENOUGH2.
        destruct (compute_tree (Areg r1 :: act) inp gm dir fuel); try contradiction.
        destruct (compute_tree (Areg r2 :: act) inp gm dir fuel); try contradiction.
        apply somenone.
      + simpl. generalize (sequence_termination act inp dir r1 r2). intros.
        assert (ENOUGH: fuel > actions_fuel (seq_list r1 r2 dir ++ act) inp dir) by lia.
        apply IHfuel with (gm:=gm) in ENOUGH. auto.
      + destruct min eqn:HMIN.
        { generalize (noi_destruct delta). intros [DELTA_DONE | DELTA_FREE]; subst.
          -                       (* quant done *)
            simpl. generalize (quant_done_termination act inp dir r greedy). intros.
            assert (ENOUGH: fuel > actions_fuel act inp dir) by lia.
            apply IHfuel with (gm:=gm) in ENOUGH. auto.
          -                       (* quant free *)
            generalize (quant_free_iter_termination act inp dir r greedy delta). intros.
            generalize (quant_free_skip_termination act inp dir r greedy delta). intros.
            assert (ENOUGH1: fuel > actions_fuel (Areg r :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r) :: act) inp dir) by lia.
            assert (ENOUGH2: fuel > actions_fuel act inp dir) by lia.
            apply IHfuel with (gm:=(GroupMap.reset (def_groups r) gm)) in ENOUGH1.
            apply IHfuel with (gm:=gm) in ENOUGH2.
            simpl. destruct delta.
            + destruct n. auto.
              destruct (compute_tree (Areg r :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred (NoI.N (S n))) r) :: act) inp (GroupMap.reset (def_groups r) gm) dir fuel); try contradiction.
              destruct (compute_tree act inp gm dir fuel); try contradiction.
              apply somenone.
            + destruct (compute_tree (Areg r :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred +∞) r) :: act) inp (GroupMap.reset (def_groups r) gm) dir fuel); try contradiction.
              destruct (compute_tree act inp gm dir fuel); try contradiction.
              apply somenone.
        }
        {                         (* quant forced *)
          simpl. generalize (quant_forced_termination act inp dir r n delta greedy). intros. subst.
          assert (ENOUGH: fuel > actions_fuel (Areg r :: Areg (Quantified greedy n delta r) :: act) inp dir) by lia.
          apply IHfuel with (gm:=(GroupMap.reset (def_groups r) gm)) in ENOUGH.
          destruct (compute_tree (Areg r :: Areg (Quantified greedy n delta r) :: act) inp (GroupMap.reset (def_groups r) gm) dir fuel); try contradiction.
          apply somenone.
        }
      + simpl. apply somenone.    (* TODO lookarounds *)
      + simpl. generalize (group_termination act inp dir r id). intros.
        assert (ENOUGH: fuel > actions_fuel (Areg r :: Aclose id :: act) inp dir) by lia.
        apply IHfuel with (gm:=(GroupMap.open (idx inp) id gm)) in ENOUGH.
        destruct (compute_tree (Areg r :: Aclose id :: act) inp (GroupMap.open (idx inp) id gm) dir fuel); try contradiction.
        apply somenone.
      + simpl. apply somenone.    (* TODO *)
      + simpl. apply somenone.    (* TODO *) 
    - simpl. destruct (is_strict_suffix inp i dir) eqn:SS.
      + apply is_strict_suffix_correct in SS.
        eapply check_termination with (cont:=act) in SS as FUEL.
        assert (ENOUGH: fuel > actions_fuel act inp dir) by lia.
        apply IHfuel with (gm:=gm) in ENOUGH.
        destruct (compute_tree act inp gm dir fuel) eqn:CMP; try contradiction.
        apply somenone.
      + apply somenone.
    - simpl. generalize (close_termination act inp dir g). intros.
      assert (ENOUGH: fuel > actions_fuel act inp dir) by lia.
      apply IHfuel with (gm:=GroupMap.close (idx inp) g gm) in ENOUGH.
      destruct (compute_tree act inp (GroupMap.close (idx inp) g gm) dir fuel); try contradiction.
      apply somenone.
  Qed.

End FunctionalSemantics.