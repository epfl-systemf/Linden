Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars.
From Linden Require Import Tree.
From Linden Require Import NumericLemmas.
From Linden Require Import TreeMSInterp.
From Warblre Require Import Numeric Base Errors. (* we don't really care about the kind of error that first_branch' may need, but we need an instance of these errors *)
From Linden Require Import Groups.
From Coq Require Import Lia.

(* This relates a regex and a string to their backtracking tree *)


Section Semantics.
  Context `{characterClass: Character.class}.


  (* TODO: Read a substring from a group map *)
  Parameter read_backref : group_map -> input -> Direction -> option (string * input).
  
  (** * Lookaround tree functions  *)

  (* Positive lookarounds expect trees with a result, and negative ones expect trees without results *)
  Definition lk_result (lk:lookaround) (t:tree) : Prop :=
    match (positivity lk) with
    | true => exists res, first_branch' t = Some res
    | false => first_branch' t = None
    end.

  (* Computes the updated group_map after finding the first result in a tree of lookarounds *)
  Definition lk_group_map (lk: lookaround) (t: tree) (gm: group_map) (idx: nat): option group_map :=
    match (positivity lk) with
    | true => tree_res t gm idx (lk_dir lk)
    | false => Some gm
    end.


  (** * Anchor semantics *)

  Definition is_boundary (i:input) : bool :=
    match i with
    | Input next pref =>
        match next, pref with
        | [], [] => false
        | [], c::p' => word_char c
        | c::n', [] => word_char c
        | c1::n', c2::p' =>
            xorb (word_char c1) (word_char c2)
        end
    end.

  (* independent of the direction *)
  Definition anchor_satisfied (a:anchor) (i:input) : bool :=
    match i with
    | Input next pref =>
        match a with
        | BeginInput =>
            match pref with | [] => true | _ => false end
        | EndInput =>
            match next with | [] => true | _ => false end
        | WordBoundary =>
            is_boundary i
        | NonWordBoundary =>
            negb (is_boundary i)
        end
    end.

  (** * Continuation Semantics *)

  (* actions encode the next things to do while constructing a tree, a stack of continuations *)
  (* it can either be matching a regex *)
  (* or checking that the current string is different from another string (for the JS star) *)
  (* or closing a group after it's been opened *)
  Inductive action: Type :=
  | Areg: regex -> action
  | Acheck: string -> action
  | Aclose: group_id -> action.

  Definition actions: Type := list action.

  (* Adds two regexes to the stack of actions, in an order dependent of the direction *)
  Definition seq_list (r1 r2: regex) (dir: Direction) : actions :=
    match dir with
    | forward => [Areg r1; Areg r2]
    | backward => [Areg r2; Areg r1]
    end.

  (* Get the current string index from the input *)
  Definition idx (inp:input) : nat :=
    match inp with
    | Input next pref => List.length pref
    end.

  (* `is_tree actions str t` means that `t` is a correct backtracking tree for all `actions` on `s` *)
  Inductive is_tree: actions -> input -> group_map -> Direction -> tree -> Prop :=
  | tree_done:
    (* nothing to do on an empty list of actions *)
    forall inp gm dir,
      is_tree [] inp gm dir Match
  | tree_check:
  (* pops a successful check from the action list *)
    forall inp gm dir strcheck cont treecont
      (PROGRESS: current_str inp dir <> strcheck)
      (TREECONT: is_tree cont inp gm dir treecont),
      is_tree (Acheck strcheck :: cont) inp gm dir (Progress strcheck treecont)
  | tree_check_fail:
  (* pops a failing check from the action list *)
    forall inp gm dir strcheck cont
      (CHECKFAIL: current_str inp dir = strcheck),
      is_tree (Acheck strcheck :: cont) inp gm dir Mismatch
  | tree_close:
  (* pops the closing of a group from the action list *)
    forall inp gm dir cont treecont gid
      (TREECONT: is_tree cont inp (close_group gm gid (idx inp)) dir treecont),
      is_tree (Aclose gid :: cont) inp gm dir (GroupAction (Close gid) treecont)
  | tree_epsilon:
    forall inp gm dir cont tcont
      (ISTREE: is_tree cont inp gm dir tcont),
      is_tree ((Areg Epsilon)::cont) inp gm dir tcont
  | tree_char:
    forall c cd inp gm nextinp dir cont tcont
      (READ: read_char cd inp dir = Some (c, nextinp))
      (TREECONT: is_tree cont nextinp gm dir tcont),
      is_tree (Areg (Regex.Character cd) :: cont) inp gm dir (Read c tcont)
  | tree_char_fail:
    forall cd inp gm dir cont
      (READ: read_char cd inp dir = None),
      is_tree (Areg (Regex.Character cd) :: cont) inp gm dir Mismatch
  | tree_disj:
    forall r1 r2 cont t1 t2 inp gm dir
      (ISTREE1: is_tree (Areg r1 :: cont) inp gm dir t1)
      (ISTREE2: is_tree (Areg r2 :: cont) inp gm dir t2),
      is_tree (Areg (Disjunction r1 r2) :: cont) inp gm dir (Choice t1 t2)
  | tree_sequence:
    (* adding next regex to the continuation *)
    forall r1 r2 cont t inp gm dir
      (CONT: is_tree (seq_list r1 r2 dir ++ cont) inp gm dir t),
      is_tree (Areg (Sequence r1 r2) :: cont) inp gm dir t
  | tree_quant_forced:
    (* the quantifier is forced to iterate, because there is a strictly positive minimum *)
    forall r1 greedy min plus cont titer inp gm dir gidl
      (* the list of capture groups to reset *)
      (RESET: gidl = def_groups r1)
      (* doing one iteration *)
      (ISTREE1: is_tree (Areg r1 :: Areg (Quantified greedy min plus r1) :: cont) inp (reset_groups gm gidl) dir titer),
      is_tree (Areg (Quantified greedy (S min) plus r1) :: cont) inp gm dir (GroupAction (Reset gidl) titer)
  | tree_quant_done:
    (* the quantifier is done iterating, because min and max are zero *)
    forall r1 greedy cont tskip inp gm dir
      (SKIP: is_tree cont inp gm dir tskip),
      is_tree (Areg (Quantified greedy 0 (NoI.N 0) r1) :: cont) inp gm dir tskip
  | tree_quant_free:
    (* the quantifier is free to iterate or stop *)
    forall r1 greedy plus cont titer tskip tquant inp gm dir gidl
      (* the list of capture groups to reset *)
      (RESET: gidl = def_groups r1)
      (* doing one iteration, then a check, then executing the next quantifier *)
      (ISTREE1: is_tree (Areg r1 :: Acheck (current_str inp dir) :: Areg (Quantified greedy 0 plus r1) :: cont) inp (reset_groups gm gidl) dir titer)
      (* skipping the quantifier entirely *)
      (SKIP: is_tree cont inp gm dir tskip)
      (CHOICE: tquant = greedy_choice greedy (GroupAction (Reset gidl) titer) tskip),
      is_tree (Areg (Quantified greedy 0 (NoI.N 1 + plus)%NoI r1) :: cont) inp gm dir tquant
  | tree_group:
    forall r1 cont treecont inp gm dir gid
      (TREECONT: is_tree (Areg r1 :: Aclose gid :: cont) inp (open_group gm gid (idx inp)) dir treecont),
      is_tree (Areg (Group gid r1) :: cont) inp gm dir (GroupAction (Open gid) treecont)
  | tree_lk:
    forall lk r1 cont treecont treelk inp gm gmlk dir
      (* there is a tree for the lookaround *)
      (TREELK: is_tree [Areg r1] inp gm (lk_dir lk) treelk)
      (* this tree has the correct expected result (positivity) *)
      (RES_LK: lk_result lk treelk)
      (* we update the group_map with the groups defined in the lookaround *)
      (GM_LK: lk_group_map lk treelk gm (idx inp) = Some gmlk)
      (TREECONT: is_tree cont inp gmlk dir treecont),
      is_tree (Areg (Lookaround lk r1) :: cont) inp gm dir (LK lk treelk treecont)
  | tree_lk_fail:
    forall lk r1 cont treelk inp gm dir
      (TREELK: is_tree [Areg r1] inp gm (lk_dir lk) treelk)
      (FAIL_LK: ~ lk_result lk treelk),
      is_tree (Areg (Lookaround lk r1) :: cont) inp gm dir (LKFail lk treelk)
  | tree_anchor:
    forall a cont treecont inp gm dir
      (ANCHOR: anchor_satisfied a inp = true)
      (TREECONT: is_tree cont inp gm dir treecont),
      is_tree (Areg (Anchor a) :: cont) inp gm dir (AnchorPass a treecont)
  | tree_anchor_fail:
    forall a cont inp gm dir
      (ANCHOR: anchor_satisfied a inp = false),
      is_tree (Areg (Anchor a) :: cont) inp gm dir Mismatch
  | tree_backref:
    forall gid inp gm nextinp dir cont tcont br_str
      (READ_BACKREF: read_backref gm inp dir = Some (br_str, nextinp))
      (TREECONT: is_tree cont nextinp gm dir tcont),
      is_tree (Areg (Backreference gid) :: cont) inp gm dir (ReadBackRef br_str tcont)
  | tree_backref_fail:
    forall gid inp gm dir cont
      (READ_BACKREF: read_backref gm inp dir = None),
      is_tree (Areg (Backreference gid) :: cont) inp gm dir Mismatch.



  Definition priotree (r:regex) (str:string) (t:tree): Prop :=
    is_tree [Areg r] (init_input str) empty_group_map forward t.


  (** * Determinism  *)

  Theorem is_tree_determ:
    forall actions i gm dir t1 t2,
      is_tree actions i gm dir t1 ->
      is_tree actions i gm dir t2 ->
      t1 = t2.
  Proof.
    intros actions i gm dir t1 t2 H.
    generalize dependent t2.
    induction H; intros.
    - inversion H; subst; auto.
    - inversion H0; subst; auto.
      + apply IHis_tree in TREECONT. subst. auto.
      + exfalso. apply PROGRESS. auto.
    - inversion H; subst; auto.
      exfalso. apply PROGRESS. auto.
    - inversion H0; subst; auto.
      apply IHis_tree in TREECONT. subst. auto.
    - inversion H0; auto.
    - inversion H0; subst; auto; rewrite READ0 in READ; inversion READ; subst.
      apply IHis_tree in TREECONT. subst. auto.
    - inversion H; subst; auto.
      rewrite READ0 in READ. inversion READ.
    - inversion H1; subst; auto.
      apply IHis_tree1 in ISTREE1. apply IHis_tree2 in ISTREE2. subst. auto.
    - inversion H0; subst; auto.
    - inversion H0; subst; auto.
      apply IHis_tree in ISTREE1.
      subst. auto.
    - inversion H0; subst; auto.
      destruct plus; discriminate.
    - inversion H1; subst; auto.
      + destruct plus; discriminate.
      + apply plus_one_inj in H4. subst plus0.
        apply IHis_tree1 in ISTREE1. apply IHis_tree2 in SKIP. subst. auto.
    - inversion H0; subst; auto.
      apply IHis_tree in TREECONT. subst. auto.
    - inversion H1; subst; auto.
      2: { apply IHis_tree1 in TREELK. subst. exfalso. apply FAIL_LK. auto. }
      apply IHis_tree1 in TREELK. subst treelk0. rewrite GM_LK in GM_LK0. injection GM_LK0 as GM_LK0. subst gmlk0.
      apply IHis_tree2 in TREECONT. subst. auto.
    - inversion H0; subst; auto.
      { apply IHis_tree in TREELK. subst. exfalso. apply FAIL_LK. auto. }
      apply IHis_tree in TREELK. subst. auto.
    - inversion H0; subst; auto.
      + f_equal. auto.
      + congruence.
    - inversion H; subst; auto. congruence.
    - inversion H0; subst; auto; rewrite READ_BACKREF0 in READ_BACKREF; inversion READ_BACKREF; subst.
      apply IHis_tree in TREECONT. subst. auto.
    - inversion H; subst; auto; rewrite READ_BACKREF0 in READ_BACKREF; inversion READ_BACKREF; subst.
  Qed.

  Corollary priotree_determ:
    forall r s t1 t2,
      priotree r s t1 ->
      priotree r s t2 ->
      t1 = t2.
  Proof.
    unfold priotree. intros r s t1 t2 H H0. eapply is_tree_determ; eauto.
  Qed.

  (* We could also prove that there always exists a priotree for any regexes and string,
   bu that amounts to proving the termination of the priotree construction. *)


  (** * Highest priority result  *)
  (* the highest priority result is just the first branch of the corresponding tree *)

  Inductive highestprio_result: regex -> string -> option leaf -> Prop :=
  | bt_result:
    forall r str res tree
      (TREE: priotree r str tree)
      (FIRST: first_branch tree = res),
      highestprio_result r str res.

  Lemma highestprio_determ:
    forall r str res1 res2,
      highestprio_result r str res1 ->
      highestprio_result r str res2 ->
      res1 = res2.
  Proof.
    intros r str res1 res2 H H0. inversion H. subst.
    inversion H0. subst.
    specialize (priotree_determ _ _ _ _ TREE TREE0). intros. subst. auto.
  Qed.
End Semantics.
