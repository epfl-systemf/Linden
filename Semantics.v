Require Import List.
Import ListNotations.

Require Import Regex.
Require Import Tree.

(** * Lookaround tree correctness  *)
(* Positive lookarounds expect trees with a result, and negative ones expect trees without results *)

Definition lk_result (lk:lookaround) (t:tree) : Prop :=
  match (positivity lk) with
  | true => exists res, first_branch t = Some res
  | false => first_branch t = None
  end.


(** * Continuation Semantics *)
(* relating regexes and string to the corresponding backtree *)

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
Inductive is_tree: regex -> continuation -> input -> direction -> tree -> Prop :=
| tree_epsilon:
  (* on an empty continuation *)
  forall inp dir,
    is_tree Epsilon [] inp dir (Match inp)
| tree_pop_reg:
  (* pops a regex from the continuation list *)
  forall inp dir regcont tailcont treecont
    (TREECONT: is_tree regcont tailcont inp dir treecont),
    is_tree Epsilon (Areg regcont :: tailcont) inp dir treecont
| tree_pop_check:
(* pops a successful check from the continuation list *)
  forall inp dir strcheck tailcont treecont
    (PROGRESS: current_str inp dir <> strcheck)
    (TREECONT: is_tree Epsilon tailcont inp dir treecont),
    is_tree Epsilon (Acheck strcheck :: tailcont) inp dir (CheckPass strcheck treecont)
| tree_pop_check_fail:
(* pops a failing check from the continuation list *)
  forall inp dir strcheck tailcont
    (CHECKFAIL: current_str inp dir = strcheck),
    is_tree Epsilon (Acheck strcheck :: tailcont) inp dir (CheckFail strcheck)
| tree_pop_close:
(* pops the closing of a group from the continuation list *)
  forall inp dir tailcont treecont gid
    (TREECONT: is_tree Epsilon tailcont inp dir treecont),
    is_tree Epsilon (Aclose gid :: tailcont) inp dir (CloseGroup gid treecont)
| tree_char:
  forall c cd inp nextinp dir cont tcont
    (READ: read_char cd inp dir = Some (c, nextinp))
    (TREECONT: is_tree Epsilon cont nextinp dir tcont),
    is_tree (Character cd) cont inp dir (Read c tcont)
| tree_char_fail:
  forall cd inp dir cont
    (READ: read_char cd inp dir = None),
    is_tree (Character cd) cont inp dir Mismatch
| tree_disj:
  forall r1 r2 cont t1 t2 inp dir
    (ISTREE1: is_tree r1 cont inp dir t1)
    (ISTREE2: is_tree r2 cont inp dir t2),
    is_tree (Disjunction r1 r2) cont inp dir (Choice t1 t2)
| tree_sequence:
  (* adding next regex to the continuation *)
  forall r1 r2 cont t inp dir
    (CONT: is_tree r1 (Areg r2 :: cont) inp dir t),
    is_tree (Sequence r1 r2) cont inp dir t
| tree_quant_done:
  forall r1 cont tcont inp dir q
    (STATUS: status q = Done)
    (* when max reaches 0, the quantifier behaves like Epsilon *)
    (CONT: is_tree Epsilon cont inp dir tcont),
    is_tree (Quantifier q r1) cont inp dir tcont
| tree_quant_forced:
  (* when both min and max are greater than 0, there is a forced iteration with a reset *)
  forall r1 q cont titer inp dir gidl
    (STATUS: status q = Forced)
    (* the list of capture groups to reset *)
    (RESET: gidl = def_groups r1)
    (* the forced iteration followed by the next quantifier *)
    (ISTREE1: is_tree r1 (Areg (Quantifier (next_quant q) r1)::cont) inp dir titer),
    is_tree (Quantifier q r1) cont inp dir (ResetGroups gidl titer)
| tree_quant_free:
  forall r1 q cont titer tskip tquant inp dir gidl greedy
    (STATUS: status q = Free greedy)
    (* the list of capture groups to reset *)
    (RESET: gidl = def_groups r1)
    (* doing one iteration, then a check, then executing the next quantifier *)
    (ISTREE1: is_tree r1 (Acheck (current_str inp dir)::Areg (Quantifier (next_quant q) r1)::cont) inp dir titer)
    (* skipping the star entirely *)
    (SKIP: is_tree Epsilon cont inp dir tskip)
    (CHOICE: tquant = greedy_choice greedy (ResetGroups gidl titer) tskip),
    is_tree (Quantifier q r1) cont inp dir tquant
| tree_group:
  forall r1 cont treecont inp dir gid
    (TREECONT: is_tree r1 (Aclose gid :: cont) inp dir treecont),
    is_tree (Group gid r1) cont inp dir (OpenGroup gid treecont)
| tree_lk:
  forall lk r1 cont treecont treelk inp dir
    (* there is a tree for the lookaround *)
    (TREELK: is_tree r1 [] inp (lk_dir lk) treelk)
  (* this tree has the correct expected result (positivity) *)
    (RES_LK: lk_result lk treelk)
    (TREECONT: is_tree Epsilon cont inp dir treecont),
    is_tree (Lookaround lk r1) cont inp dir (LK lk treelk treecont)
| tree_lk_fail:
  forall lk r1 cont treelk inp dir
    (TREELK: is_tree r1 [] inp (lk_dir lk) treelk)
    (FAIL_LK: ~ lk_result lk treelk),
    is_tree (Lookaround lk r1) cont inp dir (LKFail lk treelk)
| tree_anchor:
  forall a cont treecont inp dir
    (ANCHOR: anchor_satisfied a inp = true)
    (TREECONT: is_tree Epsilon cont inp dir treecont),
    is_tree (Anchor a) cont inp dir (AnchorPass a treecont)
| tree_anchor_fail:
  forall a cont inp dir
    (ANCHOR: anchor_satisfied a inp = false),
    is_tree (Anchor a) cont inp dir (AnchorFail a).
    


Definition backtree (r:regex) (str:string) (t:tree): Prop :=
  is_tree r [] (init_input str) Forward t.


(** * Determinism  *)

Theorem is_tree_determ:
  forall r cont i dir t1 t2,
    is_tree r cont i dir t1 ->
    is_tree r cont i dir t2 ->
    t1 = t2.
Proof.
  intros r cont i dir t1 t2 H.
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
  - inversion H0; subst; auto; rewrite STATUS0 in STATUS; inversion STATUS.
  - inversion H0; subst; auto; rewrite STATUS0 in STATUS; inversion STATUS.
    apply IHis_tree in ISTREE1. subst. auto.
  - inversion H1; subst; auto; rewrite STATUS0 in STATUS; inversion STATUS.
    apply IHis_tree2 in SKIP.
    apply IHis_tree1 in ISTREE1.
    subst. auto.
  - inversion H0; subst; auto.
    apply IHis_tree in TREECONT. subst. auto.
  - inversion H1; subst; auto.
    2: { apply IHis_tree1 in TREELK. subst. exfalso. apply FAIL_LK. auto. }
    apply IHis_tree1 in TREELK. apply IHis_tree2 in TREECONT. subst. auto.
  - inversion H0; subst; auto.
    { apply IHis_tree in TREELK. subst. exfalso. apply FAIL_LK. auto. }
    apply IHis_tree in TREELK. subst. auto.
  - inversion H0; subst; auto; rewrite ANCHOR0 in ANCHOR; inversion ANCHOR. subst.
    apply IHis_tree in TREECONT. subst. auto.
  - inversion H; subst; auto; rewrite ANCHOR0 in ANCHOR; inversion ANCHOR.
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

    
