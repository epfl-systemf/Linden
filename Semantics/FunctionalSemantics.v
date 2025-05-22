Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars.
From Linden Require Import Tree.
From Linden Require Import NumericLemmas.
From Linden Require Import Groups Semantics.
From Warblre Require Import Numeric Base.

From Coq Require Import Lia.
From Coq Require Import Program.

Context `{characterClass: Character.class}.


(** * Suffixes  *)

(* advance_input is the next suffix *)
(* but know we explore the transitive closure of this relation *)

(* an input is a strict suffix of another is there are less characters left to see *)
(* here, we define inp1 is a strict suffix of inp2 *)
Program Fixpoint strict_suffix_pf (inp1 inp2:input) (dir:Direction) {measure (length (current_str inp2 dir))} : bool :=
  match (advance_input inp2 dir) with
  | None => false                (* we cannot be a strict suffix of the end of string *)
  | Some nextinp2 =>
      if (inp1 ==? nextinp2)%wt then true
      else strict_suffix_pf inp1 nextinp2 dir
  end.
Next Obligation.
  destruct inp2 as [next2 pref2]. unfold advance_input in Heq_anonymous.
  destruct dir.
  - destruct next2; inversion Heq_anonymous.
    simpl. lia.
  - destruct pref2; inversion Heq_anonymous.
    simpl. lia.
Qed.

Lemma advance_input_current:
  forall inp nextinp dir,
    advance_input inp dir = Some nextinp ->
    length (current_str nextinp dir) < length (current_str inp dir).
Proof.
  intros inp nextinp dir H. unfold advance_input in H.
  destruct inp as [next pref]. destruct dir.
  - destruct next; inversion H. simpl. lia.
  - destruct pref; inversion H. simpl. lia.
Qed.

Program Lemma strict_suffix_pf_current:
  forall inp1 inp2 dir,
    strict_suffix_pf inp1 inp2 dir = true ->
    length (current_str inp1 dir) < length (current_str inp2 dir).
Proof.
  intros inp1 inp2 dir H.
  destruct inp1 as [next1 pref1]. destruct inp2 as [next2 pref2].
  unfold strict_suffix_pf in H. destruct dir.
  - generalize dependent pref2. induction next2; intros.
    + simpl. inversion H.
    + admit.
Abort.
(* it's a pain to reason about these Program Fixpoints (unless I am missing a trick) *)
(* in this special case, I could just do two version for forward and backward that should be easy to write with structural recursion *)
(* But in the semantics below, this could be an issue *)


(* Another version of strict suffix, without program fixpoints *)
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

Definition strict_suffix (inp1 inp2:input) (dir:Direction) : bool :=
  match inp2 with
  | Input next2 pref2 =>
      match dir with
      | forward => strict_suffix_forward inp1 next2 pref2
      | backward => strict_suffix_backward inp1 next2 pref2
      end
  end.

Lemma strict_suffix_current:
  forall inp1 inp2 dir,
    strict_suffix inp1 inp2 dir = true ->
    length (current_str inp1 dir) < length (current_str inp2 dir).
Proof.
  intros [next1 pref1] [next2 pref2] dir H. unfold strict_suffix in H. destruct dir.
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
(* much better than the program fixpoint version *)


Theorem read_suffix:
  forall inp dir nextinp,
    advance_input inp dir = Some nextinp ->
    strict_suffix nextinp inp dir = true.
Proof.
  intros [oldnext oldpref] dir [newnext newpref] H. destruct dir.
  - simpl in H. simpl. unfold strict_suffix_forward. destruct oldnext; inversion H.
    subst. rewrite EqDec.reflb. reflexivity.
  - simpl in H. simpl. unfold strict_suffix_backward. destruct oldpref; inversion H.
    subst. rewrite EqDec.reflb. reflexivity.
Qed.

Theorem read_char_suffix:
  forall inp dir nextinp cd c,
    read_char cd inp dir = Some (c, nextinp) ->
    strict_suffix nextinp inp dir = true.
Proof.
  intros [next pref] dir nextinp cd c H.  destruct dir; simpl in H.
  - destruct next; inversion H. destruct (char_match t cd); inversion H; subst.
    apply read_suffix. simpl. auto.
  - destruct pref; inversion H. destruct (char_match t cd); inversion H; subst.
    apply read_suffix. simpl. auto.
Qed.


Theorem strict_suffix_trans:
  forall inp1 inp2 inp3 dir,
    strict_suffix inp1 inp2 dir = true ->
    strict_suffix inp2 inp3 dir = true ->
    strict_suffix inp1 inp3 dir = true.
Proof.
Admitted.

Lemma strict_advance:
  forall inp1 inp2 dir nextinp1,
    strict_suffix inp1 inp2 dir = true ->
    advance_input inp1 dir = Some nextinp1 ->
    exists nextinp2, advance_input inp2 dir = Some nextinp2 /\
                  strict_suffix nextinp1 nextinp2 dir = true.
Proof.
Admitted.

(** * Computing the measure  *)


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
    strict_suffix inp1 inp2 d = true ->
    (forall dir, worst_input inp1 dir = worst_input inp2 dir).
Proof.
Admitted.                       (* suffixes have the same total string *)

Lemma worst_suffix_forward:
  forall pref next,
    pref = [] \/ strict_suffix_forward (Input next pref) (rev pref ++ next) [] = true.
Proof.
  intros. generalize dependent next. induction pref; intros.
  { left. auto. }
  right. specialize (IHpref (a::next)). destruct IHpref as [EMPTY | STRICT].
  - subst. simpl. rewrite EqDec.reflb. auto.
  - simpl. rewrite <- app_assoc. simpl.
    assert (strict_suffix (Input next (a::pref)) (Input (a::next) pref) forward = true).
    { simpl. rewrite EqDec.reflb. auto. }
    assert (strict_suffix (Input (a :: next) pref) (Input (rev pref ++ a :: next) []) forward = true).
    { simpl; auto. }
    eapply strict_suffix_trans in H0; eauto.
Qed.

Lemma worst_input_suffix:
  forall inp worst dir,
    worst_input inp dir = worst ->
    worst = inp \/ strict_suffix inp worst dir = true.
Proof.
  intros [next pref] worst dir H. unfold worst_input in H.
  destruct dir; inversion H; subst.
  - simpl. generalize dependent pref. induction next; intros.
    { destruct pref.
      - left. auto.
      - generalize (worst_suffix_forward (t::pref) []). intros [H|H].
        + inversion H.
        + right. auto. }
    admit.
Admitted.

(* The maximum number of iterations for a quantifier *)
Definition max_iter (inp:input) (dir:Direction): nat :=
  1 + length (current_str inp dir).

Lemma strict_suffix_max_iter:
  forall inp1 inp2 dir,
    strict_suffix inp1 inp2 dir = true ->
    max_iter inp1 dir < max_iter inp2 dir.
Proof.
  intros inp1 inp2 dir H. apply strict_suffix_current in H.
  unfold max_iter. lia.
Qed.

Lemma advance_max_iter:
  forall inp nextinp dir,
    advance_input inp dir = Some nextinp ->
    max_iter nextinp dir < max_iter inp dir.
Proof.
  intros inp nextinp dir H. apply read_suffix in H. apply strict_suffix_max_iter. auto.
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
      (1 + rfuel) * (min + max_iter inp dir)
  | Lookaround lk r1 =>
      1 + (regex_fuel r1 (worst_input inp (lk_dir lk)) (lk_dir lk))
  | Group _ r1 =>
      2 + (regex_fuel r1 inp dir)
  | Anchor _ => 1
  | Backreference _ => 1
  end.

Fixpoint actions_fuel (act:actions) (inp:input) (dir:Direction) : nat :=
  match act with
  | [] => 0
  | (Areg r)::l => (regex_fuel r inp dir) + (actions_fuel l inp dir)
  | (Acheck _)::l =>
      (* advance_input is the next closest possible input after having passed a check *)
      match (advance_input inp dir) with
      | Some nextinp => actions_fuel l nextinp dir
      | None => 0
      end
  | (Aclose _):: l => 1 + (actions_fuel l inp dir)
  end.

(** * Monotonicity Lemmas  *)

Lemma smaller_product:
  forall (a b c d:nat),
    a <= b ->
    c <= d ->
    a * c <= b * d.
Proof.
Admitted.

(* Inputs taken from the same initial string *)
Definition same_string (inp1 inp2:input) : Prop :=
  forall dir, worst_input inp1 dir = worst_input inp2 dir.

Lemma read_advances:
  forall cd inp dir c nextinp,
    read_char cd inp dir = Some (c, nextinp) ->
    max_iter nextinp dir < max_iter inp dir /\
      same_string nextinp inp.
Proof.
  intros cd inp dir c nextinp H. unfold read_char in H. destruct inp.
  destruct dir.
  - destruct next; inversion H.
    destruct (char_match t cd); inversion H. subst.
    split; auto. unfold same_string. intros dir. destruct dir; simpl.
    + rewrite <- app_assoc. simpl. auto.
    + rewrite <- app_assoc. simpl. auto.
  - destruct pref; inversion H.
    destruct (char_match t cd); inversion H. subst.
    split; auto. unfold same_string. intros dir. destruct dir; simpl.
    + rewrite <- app_assoc. simpl. auto.
    + rewrite <- app_assoc. simpl. auto.
Qed.

Lemma regex_monoton:
  forall r dir inp1 inp2,
    strict_suffix inp1 inp2 dir = true ->
    regex_fuel r inp1 dir <= regex_fuel r inp2 dir.
Proof.
  intros r dir inp1 inp2 H.
  induction r; simpl; try lia.
  - apply strict_suffix_max_iter in H.
    assert ((min + max_iter inp1 dir) <= (min + max_iter inp2 dir)) by lia. 
  (* eapply smaller_product; eauto. lia. *)
    admit.
  - apply suffix_same_worst with (dir:=(lk_dir lk)) in H. rewrite H. lia.
Admitted.

Lemma regex_next_monoton:
  forall r inp nextinp dir,
    advance_input inp dir = Some nextinp ->
    regex_fuel r nextinp dir <= regex_fuel r inp dir.
Proof.
  intros r inp nextinp dir H.
  induction r; simpl; try lia.
  - apply advance_max_iter in H as MAX.
    assert (S (min + max_iter nextinp dir) <= S (min + max_iter inp dir)) by lia.
    (* eapply smaller_product; eauto.  *) admit.
  - apply read_suffix in H. apply suffix_same_worst with (dir:=lk_dir lk) in H.
    rewrite H. lia.
Admitted.
  

Lemma actions_monoton:
  forall actions dir inp1 inp2,
    strict_suffix inp1 inp2 dir = true ->
    actions_fuel actions inp1 dir <= actions_fuel actions inp2 dir.
Proof.
  intros actions dir inp1 inp2 H. induction actions; simpl; try lia.
  destruct a; simpl; try lia.
  - eapply regex_monoton with (r:=r) in H; auto. lia.
  - destruct (advance_input inp1 dir) eqn:ADV.
    + eapply strict_advance in ADV as [nextinp2 [ADV2 SUF2]]; eauto.
      rewrite ADV2.
      (* TODO *)
Admitted.
    

(** * Computing a tree  *)

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

  Program Fixpoint compute_tree (act: actions) (inp: input) (gm: group_map) (dir: Direction) {measure (actions_fuel act inp dir)}: tree :=
    match act with
    (* tree_done *)
    | [] => Match
    (* tree_check, tree_check_fail *)
    | Acheck strcheck :: cont =>
        if (current_str inp dir ==? strcheck)%wt then
          Mismatch
        else
          let treecont := compute_tree cont inp gm dir in
          (Progress strcheck treecont)
    (* tree_close *)
    | Aclose gid :: cont =>
        let treecont := compute_tree cont inp (GroupMap.close (idx inp) gid gm) dir in
        (GroupAction (Close gid) treecont)
    (* tree_epsilon *)
    | Areg Epsilon::cont => compute_tree cont inp gm dir
    (* tree_char, tree_char_fail *)
    | Areg (Regex.Character cd)::cont =>
        match read_char cd inp dir with
        | Some (c, nextinp) =>
            let tcont := compute_tree cont nextinp gm dir in
            (Read c tcont)
        | None => Mismatch
        end
    (* tree_disj *)
    | Areg (Disjunction r1 r2)::cont =>
        let t1 := compute_tree (Areg r1 :: cont) inp gm dir in
        let t2 := compute_tree (Areg r2 :: cont) inp gm dir in
        (Choice t1 t2)
    (* tree_sequence *)
    | Areg (Sequence r1 r2)::cont =>
        compute_tree (seq_list r1 r2 dir ++ cont) inp gm dir
    (* tree_quant_forced *)
    | Areg (Quantified greedy (S min) delta r1)::cont =>
        let gidl := def_groups r1 in
        let titer := compute_tree (Areg r1 :: Areg (Quantified greedy min delta r1) :: cont) inp (GroupMap.reset gidl gm) dir in
        (GroupAction (Reset gidl) titer)
    (* tree_quant_done *)
    | Areg (Quantified greedy 0 (NoI.N 0) r1)::cont =>
        compute_tree cont inp gm dir
    (* tree_quant_free: finite max *)
    | Areg (Quantified greedy 0 delta r1)::cont =>
        let gidl := def_groups r1 in
        let titer := compute_tree (Areg r1 :: Acheck (current_str inp dir) :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) inp (GroupMap.reset gidl gm) dir in
        let tskip := compute_tree cont inp gm dir in
        (greedy_choice greedy (GroupAction (Reset gidl) titer) tskip)
    (* tree_group *)
    | Areg (Group gid r1)::cont =>
        let treecont := compute_tree (Areg r1 :: Aclose gid :: cont) inp (GroupMap.open (idx inp) gid gm) dir in
        (GroupAction (Open gid) treecont)
    (* tree_lk, tree_lk_fail, tree_anchor, tree_anchor_fail, tree_backref, tree_backref_fail: TODO *)
    | _ => Mismatch
    end.

  (** * Proving Termination  *)
  (* we prove the strict decrease of the measure in each recursive call *)

  (* check *)
  Next Obligation.
    simpl.
    (* I have no way to finish *)
    (* Also I have lost the fact that the input is different from strcheck *)
  Admitted.
  (* char *)
  Next Obligation.
    simpl. symmetry in Heq_anonymous. apply read_char_suffix in Heq_anonymous as SUFFIX.
    assert (actions_fuel cont nextinp dir <= actions_fuel cont inp dir).
    { apply actions_monoton; auto. }
    lia.
  Qed.
  (* disjunction left *)
  Next Obligation.
    simpl. lia.
  Qed.
  (* disjunction right *)
  Next Obligation.
    simpl. lia.
  Qed.
  (* sequence *)
  Next Obligation.
    simpl. destruct dir; simpl; lia.
  Qed.
  (* quant forced *)
  Next Obligation.
    simpl. lia.
  Qed.
  (* quant done *)
  Next Obligation.
    simpl. lia.
  Qed.
  (* quant free: iteration *)
  Next Obligation.
    simpl. pose (ACT := actions_fuel cont inp dir). fold ACT.
    pose (R1 := regex_fuel r1 inp dir). fold R1.
    pose (MAX := max_iter inp dir). fold MAX.
    
  Admitted.
  (* quant free; skip *)
  Next Obligation.
    simpl. lia.
  Qed.
  (* group *)
  Next Obligation.
    simpl. lia.
  Qed.
  (* UNSUPPORTED, TODO *)
  Next Obligation.
    repeat (try split; auto); try solve[unfold not; intros; inversion H].
  Qed.
  Next Obligation.
    repeat (try split; auto); try solve[unfold not; intros; inversion H].
  Qed.
  Next Obligation.
    repeat (try split; auto); try solve[unfold not; intros; inversion H].
  Qed.
