Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree.
From Linden Require Import NumericLemmas.
From Warblre Require Import Numeric.
From Coq Require Import Lia.

(* This relates a regex and a string to their backtracking tree *)

(** * Continuation Semantics *)

(* actions are things to do after executing the current focused regex *)
(* it can either be executing another regex (encoding the sequence) *)
(* or checking that the current string is different from another string (for the JS star) *)
(* or closing a group after it's been opened *)
Inductive action: Type :=
| Areg: regex -> action
| Acheck: string -> action
| Aclose: group_id -> action.

Definition continuation: Type := list action.

(* `is_tree r cont str t` means that `t` is a correct backtracking tree for `r` on `s`,
   where we have to execute `cont` at each leaf *)
Inductive is_tree: regex -> continuation -> input -> tree -> Prop :=
| tree_epsilon:
  (* on an empty continuation *)
  forall inp,
    is_tree Epsilon [] inp Match
| tree_pop_reg:
  (* pops a regex from the continuation list *)
  forall inp regcont tailcont treecont
    (TREECONT: is_tree regcont tailcont inp treecont),
    is_tree Epsilon (Areg regcont :: tailcont) inp treecont
| tree_pop_check:
(* pops a successful check from the continuation list *)
  forall inp strcheck tailcont treecont
    (PROGRESS: current_str inp <> strcheck)
    (TREECONT: is_tree Epsilon tailcont inp treecont),
    is_tree Epsilon (Acheck strcheck :: tailcont) inp (CheckPass strcheck treecont)
| tree_pop_check_fail:
(* pops a failing check from the continuation list *)
  forall inp strcheck tailcont
    (CHECKFAIL: current_str inp = strcheck),
    is_tree Epsilon (Acheck strcheck :: tailcont) inp (CheckFail strcheck)
| tree_pop_close:
(* pops the closing of a group from the continuation list *)
  forall inp tailcont treecont gid
    (TREECONT: is_tree Epsilon tailcont inp treecont),
    is_tree Epsilon (Aclose gid :: tailcont) inp (GroupAction (Close gid) treecont)
| tree_char:
  forall c cd inp nextinp cont tcont
    (READ: read_char cd inp = Some (c, nextinp))
    (TREECONT: is_tree Epsilon cont nextinp tcont),
    is_tree (Character cd) cont inp (Read c tcont)
| tree_char_fail:
  forall cd inp cont
    (READ: read_char cd inp = None),
    is_tree (Character cd) cont inp Mismatch
| tree_disj:
  forall r1 r2 cont t1 t2 inp
    (ISTREE1: is_tree r1 cont inp t1)
    (ISTREE2: is_tree r2 cont inp t2),
    is_tree (Disjunction r1 r2) cont inp (Choice t1 t2)
| tree_sequence:
  (* adding next regex to the continuation *)
  forall r1 r2 cont t inp
    (CONT: is_tree r1 (Areg r2 :: cont) inp t),
    is_tree (Sequence r1 r2) cont inp t
(*| tree_star:
  forall r1 greedy cont titer tskip tquant inp gidl
    (* the list of capture groups to reset *)
    (RESET: gidl = def_groups r1)
    (* doing one iteration, then a check, then executing the next quantifier *)
    (ISTREE1: is_tree r1 (Acheck (current_str inp)::Areg (Star greedy r1)::cont) inp titer)
    (* skipping the star entirely *)
    (SKIP: is_tree Epsilon cont inp tskip)
    (CHOICE: tquant = greedy_choice greedy (GroupAction (Reset gidl) titer) tskip),
    is_tree (Star greedy r1) cont inp tquant*)
| tree_quant_minpos:
  forall r1 greedy min plus cont titer inp gidl
    (* the list of capture groups to reset *)
    (RESET: gidl = def_groups r1)
    (* doing one iteration *)
    (ISTREE1: is_tree r1 (Areg (Quantified greedy min plus r1)::cont) inp titer),
    is_tree (Quantified greedy (S min) plus r1) cont inp (GroupAction (Reset gidl) titer)
| tree_quant_minzero_pluszero:
  forall r1 greedy cont tskip inp
    (SKIP: is_tree Epsilon cont inp tskip),
    is_tree (Quantified greedy 0 (NoI.N 0) r1) cont inp tskip
| tree_quant_minzero_pluspos:
  forall r1 greedy plus cont titer tskip tquant inp gidl
    (* the list of capture groups to reset *)
    (RESET: gidl = def_groups r1)
    (* doing one iteration, then a check, then executing the next quantifier *)
    (ISTREE1: is_tree r1 (Acheck (current_str inp)::Areg (Quantified greedy 0 plus r1)::cont) inp titer)
    (* skipping the quantifier entirely *)
    (SKIP: is_tree Epsilon cont inp tskip)
    (CHOICE: tquant = greedy_choice greedy (GroupAction (Reset gidl) titer) tskip),
    is_tree (Quantified greedy 0 (NoI.N 1 + plus)%NoI r1) cont inp tquant
| tree_group:
  forall r1 cont treecont inp gid
    (TREECONT: is_tree r1 (Aclose gid :: cont) inp treecont),
    is_tree (Group gid r1) cont inp (GroupAction (Open gid) treecont).    


Definition backtree (r:regex) (str:string) (t:tree): Prop :=
  is_tree r [] (init_input str) t.

(* Adding Epsilon to the list of continuations *)
(*Lemma is_tree_eps':
  forall reg cont inp t, is_tree reg cont inp t -> forall cont1 cont2, cont = cont1 ++ (Areg Epsilon::cont2) -> is_tree reg (cont1 ++ cont2) inp t.
Proof.
  intros reg cont inp t His_tree.
  induction His_tree.
  (* TODO From now *)
  - (* tree_epsilon *)
    intros cont1 cont2 Habs. destruct cont1; discriminate.
  - (* tree_pop_reg *)
    intros cont1 cont2 H. destruct cont1 as [|x cont1].
    + inversion H. subst. assumption.
    + simpl in *. inversion H. subst. apply tree_pop_reg. apply IHHis_tree. reflexivity.
  - (* tree_pop_check *)
    intros cont1 cont2 H. destruct cont1 as [|x cont1].
    + inversion H.
    + simpl in H. inversion H. simpl. apply tree_pop_check.
      * assumption.
      * apply IHHis_tree. assumption.
  - (* tree_pop_check_fail *)
    intros [|x cont1] cont2 H; simpl in *.
    + inversion H.
    + inversion H. apply tree_pop_check_fail. assumption.
  - (* tree_pop_close *)
    intros [|x cont1] cont2 H; simpl in *.
    + inversion H.
    + inversion H. apply tree_pop_close. apply IHHis_tree. assumption.
  - (* tree_char *)
    intros cont1 cont2 H.
    eapply tree_char.
    + apply READ.
    + apply IHHis_tree. apply H.
  - (* tree_char_fail *)
    intros cont1 cont2 H. apply tree_char_fail. apply READ.
  - (* tree_disj *)
    intros cont1 cont2 H.
    apply tree_disj.
    + apply IHHis_tree1. apply H.
    + apply IHHis_tree2. apply H.
  - (* tree_sequence *)
    intros cont1 cont2 H.
    apply tree_sequence.
    subst cont.
    rewrite app_comm_cons.
    apply IHHis_tree.
    simpl. reflexivity.
  - (* tree_star *)
    intros cont1 cont2 H.
    eapply tree_star.
    + apply RESET.
    + subst cont.
      rewrite app_comm_cons. rewrite app_comm_cons.
      rewrite app_comm_cons in IHHis_tree1. rewrite app_comm_cons in IHHis_tree1.
      apply IHHis_tree1. reflexivity.
    + apply IHHis_tree2. assumption.
    + assumption.
  - (* tree_group *)
    intros cont1 cont2 H.
    subst cont.
    apply tree_group.
    rewrite app_comm_cons.
    apply IHHis_tree.
    simpl. reflexivity.
Qed.

Corollary is_tree_eps:
  forall reg cont1 cont2 inp t, is_tree reg (cont1 ++ Areg Epsilon :: cont2) inp t -> is_tree reg (cont1 ++ cont2) inp t.
Proof.
  intros reg cont1 cont2 inp t H.
  eapply is_tree_eps'.
  - apply H.
  - reflexivity.
Qed.*)


(** * Determinism  *)

Theorem is_tree_determ:
  forall r cont i t1 t2,
    is_tree r cont i t1 ->
    is_tree r cont i t2 ->
    t1 = t2.
Proof.
  intros r cont i t1 t2 H.
  generalize dependent t2.
  induction H; intros.
  - inversion H; subst; auto.
  - inversion H0; subst; auto.
  - inversion H0; subst; auto.
    + apply IHis_tree in TREECONT. subst. auto.
    + exfalso. apply PROGRESS. auto.
  - inversion H; subst; auto.
    exfalso. apply PROGRESS. auto.
  - inversion H0; subst; auto.
    apply IHis_tree in TREECONT. subst. auto.
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
Qed.

Corollary backtree_determ:
  forall r s t1 t2,
    backtree r s t1 ->
    backtree r s t2 ->
    t1 = t2.
Proof.
  unfold backtree. intros r s t1 t2 H H0. eapply is_tree_determ; eauto.
Qed.

(* We could also prove that there always exists a backtree for any regexes and string,
 bu that amounts to proving the termination of the backtree construction. *)


(** * Backtracking  *)
(* the result of backtracking is just the first branch of the corresponding tree *)

Inductive backtracking_result: regex -> string -> option leaf -> Prop :=
| bt_result:
  forall r str res tree
    (TREE: backtree r str tree)
    (FIRST: first_branch tree = res),
    backtracking_result r str res.

Lemma backtracking_determ:
  forall r str res1 res2,
    backtracking_result r str res1 ->
    backtracking_result r str res2 ->
    res1 = res2.
Proof.
  intros r str res1 res2 H H0. inversion H. subst.
  inversion H0. subst.
  specialize (backtree_determ _ _ _ _ TREE TREE0). intros. subst. auto.
Qed.
