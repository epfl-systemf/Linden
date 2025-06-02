Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics PikeSubset.
From Warblre Require Import Base.


(* An alternate definition of the semantics, using a boolean to know if one can exit a loop *)
(* And not using a group_map to exhibit the uniform-future property by construction *)



(** * Loop Boolean  *)
(* The loop boolean, indicating if we can exit a loop iteration or not *)
(* CanExit means that we are allowed to exit any quantifier: we have read a character more recently than we have entered a free quantifier *)
(* CannotExit means we can't exit the most recent quantifier we entered, because we haven't read anything since *)
Inductive LoopBool : Type :=
| CanExit
| CannotExit.


(** * Boolean Semantics  *)
(* where checks consult the boolean instead of actually comparing strings *)

  Inductive bool_tree: actions -> input -> LoopBool -> tree -> Prop :=
  | tree_done:
    (* nothing to do on an empty list of actions *)
    forall inp b,
      bool_tree [] inp b Match
  | tree_check:
    (* pops a successful check from the action list *)
    (* NEW: this only checks the boolean allows exit and not the strcheck in the tree *)
    forall inp strcheck cont treecont
      (TREECONT: bool_tree cont inp CanExit treecont),
      bool_tree (Acheck strcheck :: cont) inp CanExit (Progress treecont)
  | tree_check_fail:
  (* pops a failing check from the action list *)
    forall inp strcheck cont,
      bool_tree (Acheck strcheck :: cont) inp CannotExit Mismatch
  | tree_close:
  (* pops the closing of a group from the action list *)
    forall inp b cont treecont gid
      (TREECONT: bool_tree cont inp b treecont),
      bool_tree (Aclose gid :: cont) inp b (GroupAction (Close gid) treecont)
  | tree_epsilon:
    forall inp b cont tcont
      (ISTREE: bool_tree cont inp b tcont),
      bool_tree ((Areg Epsilon)::cont) inp b tcont
  | tree_char:
    forall c cd inp b nextinp cont tcont
      (READ: read_char cd inp forward = Some (c, nextinp))
      (* NEW: changes the boolean to CanExit *)
      (TREECONT: bool_tree cont nextinp CanExit tcont),
      bool_tree (Areg (Regex.Character cd) :: cont) inp b (Read c tcont)
  | tree_char_fail:
    forall cd inp b cont
      (READ: read_char cd inp forward = None),
      bool_tree (Areg (Regex.Character cd) :: cont) inp b Mismatch
  | tree_disj:
    forall r1 r2 cont t1 t2 inp b
      (ISTREE1: bool_tree (Areg r1 :: cont) inp b t1)
      (ISTREE2: bool_tree (Areg r2 :: cont) inp b t2),
      bool_tree (Areg (Disjunction r1 r2) :: cont) inp b (Choice t1 t2)
  | tree_sequence:
    (* adding next regex to the continuation *)
    forall r1 r2 cont t inp b
      (CONT: bool_tree (Areg r1 :: Areg r2 :: cont) inp b t),
      bool_tree (Areg (Sequence r1 r2) :: cont) inp b t
  | tree_quant_forced:
    (* the quantifier is forced to iterate, because there is a strictly positive minimum *)
    forall r1 greedy min plus cont titer inp b gidl
      (* the list of capture groups to reset *)
      (RESET: gidl = def_groups r1)
      (* doing one iteration *)
      (ISTREE1: bool_tree (Areg r1 :: Areg (Quantified greedy min plus r1) :: cont) inp b titer),
      bool_tree (Areg (Quantified greedy (S min) plus r1) :: cont) inp b (GroupAction (Reset gidl) titer)
  | tree_quant_done:
    (* the quantifier is done iterating, because min and max are zero *)
    forall r1 greedy cont tskip inp b
      (SKIP: bool_tree cont inp b tskip),
      bool_tree (Areg (Quantified greedy 0 (NoI.N 0) r1) :: cont) inp b tskip
  | tree_quant_free:
    (* the quantifier is free to iterate or stop *)
    forall r1 greedy plus cont titer tskip tquant inp b gidl
      (* the list of capture groups to reset *)
      (RESET: gidl = def_groups r1)
      (* doing one iteration, then a check, then executing the next quantifier *)
      (* NEW: switchgint the boolean to CannotExit *)
      (ISTREE1: bool_tree (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 plus r1) :: cont) inp CannotExit titer)
      (* skipping the quantifier entirely *)
      (SKIP: bool_tree cont inp b tskip)
      (CHOICE: tquant = greedy_choice greedy (GroupAction (Reset gidl) titer) tskip),
      bool_tree (Areg (Quantified greedy 0 (NoI.N 1 + plus)%NoI r1) :: cont) inp b tquant
  | tree_group:
    forall r1 cont treecont inp b gid
      (TREECONT: bool_tree (Areg r1 :: Aclose gid :: cont) inp b treecont),
      bool_tree (Areg (Group gid r1) :: cont) inp b (GroupAction (Open gid) treecont)
  | tree_anchor:
    forall a cont treecont inp b
      (ANCHOR: anchor_satisfied a inp = true)
      (TREECONT: bool_tree cont inp b treecont),
      bool_tree (Areg (Anchor a) :: cont) inp b (AnchorPass a treecont)
  | tree_anchor_fail:
    forall a cont inp b
      (ANCHOR: anchor_satisfied a inp = false),
      bool_tree (Areg (Anchor a) :: cont) inp b Mismatch.


(** * Boolean Tree Equivalence  *)

(* As we go down the tree, the boolean should "encode" the continuation and the current string *)
(* Meaning that the boolean is true when we can exit with the current string *)
(* And the boolean is false when we cannot *)


(** * First Step: encoding the invariant  *)
Definition suffix (str1 str2:string) : Prop :=
  exists prefix, str2 = prefix ++ str1.

Definition strict_suffix (str1 str2:string) : Prop :=
  suffix str1 str2 /\ str1 <> str2.

Lemma cons_neq:
  forall A str pref (c:A),
    str = pref ++ c::str -> False.
Proof.
  intros A str pref c H.
  assert (List.length str = List.length pref + 1 + List.length str).
  { rewrite H at 1. rewrite app_length. simpl. lia. }
  lia.
Qed.

Lemma strict_cons:
  forall s c,
    strict_suffix s (c::s).
Proof.
  intros s c. unfold strict_suffix, suffix. split.
  - exists [c]. simpl. auto.
  - unfold not.
    replace (c::s) with ([] ++ c::s) by auto.
    apply cons_neq.
Qed.    

Lemma strict_app:
  forall str1 str2 c,
    strict_suffix (c::str1) str2 ->
    strict_suffix str1 str2.
Proof.
  unfold strict_suffix, suffix. intros str2 str0 c [[prefix APP] NEQ].
  split.
  - exists (prefix ++ [c]). rewrite <- app_assoc. simpl. auto.
  - unfold not. intros H. subst. eapply cons_neq; eauto.
Qed.
  

Inductive bool_encoding: LoopBool -> input -> actions -> Prop :=
(* an empty continuation can be encoded with any boolean *)
| nil_encode:
  forall str b,
    bool_encoding b str []
| cons_reg:
  forall b str cont r
    (ENCODE: bool_encoding b str cont),
    bool_encoding b str (Areg r::cont)
| cons_close:
  forall b str cont gid
    (ENCODE: bool_encoding b str cont),
    bool_encoding b str (Aclose gid::cont)
| cons_true:
  forall stk str head 
    (ENCODE: bool_encoding CanExit str stk)
    (STRICT: strict_suffix (current_str str forward) (current_str head forward)),
    bool_encoding CanExit str (Acheck head::stk)
| to_false:
  (* to switch to false, we need the head of the stack to be equal to the current string
   no progress has been made. *)
  forall stk str
    (ENCODE: bool_encoding CanExit str stk),
    bool_encoding CannotExit str (Acheck str::stk)
| cons_false:
  (* when the bool is already false, we can push the current string to the stack *)
  forall stk str
    (ENCODE: bool_encoding CannotExit str stk),
    bool_encoding CannotExit str (Acheck str::stk).

(* Generalizes the encoding to inputs *)
(* later: add direction, so that the input can be read in two directions *)
(* Inductive encodes : LoopBool -> input -> actions -> Prop := *)
(* | encode_forward: *)
(*   forall b next pref cont *)
(*     (ENCODE: bool_encoding b next cont), *)
(*     encodes b (Input next pref) cont. *)


(* when we are already encoded with true, reading a new character preserves this true encoding *)
(* when we are encoded with false, reading a new character switches to being encoded with true *)
Lemma true_encoding:
  forall str c pref cont b,
    bool_encoding b (Input (c::str) pref) cont ->
    bool_encoding CanExit (Input str (c::pref)) cont.
Proof.
  intros str c pref cont b H.
  remember (Input (c::str) pref) as prevstr.
  induction H; intros.
  - constructor.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto. rewrite Heqprevstr in STRICT. eapply strict_app; eauto.
  - constructor.
    + apply IHbool_encoding; auto.
    + rewrite Heqprevstr. apply strict_cons.
  - constructor.
    + apply IHbool_encoding; auto.
    + rewrite Heqprevstr. apply strict_cons.
Qed.


(* when entering a new quantifier, this pushes the current string on the stack *)
(* this makes the whole stack encoded with false *)
Lemma false_encoding:
  forall str cont b,
    bool_encoding b str cont ->
    bool_encoding CannotExit str (Acheck str::cont).
Proof.
  intros str cont b H.
  induction cont.
  - constructor. constructor.
  - destruct b.
    + apply to_false. auto.
    + apply cons_false. auto.
Qed.

(* if the string is different than the check, we know the boolean is true *)
Lemma encoding_different:
  forall b str strcheck cont,
    bool_encoding b str (Acheck strcheck::cont) ->
    str <> strcheck ->
    b = CanExit.
Proof.
  intros b0 str [strcheck pref] cont H.
  remember (Acheck (Input strcheck pref)::cont) as prevcont.
  induction H; intros; auto; inversion Heqprevcont;
    exfalso; auto.
Qed.

(* if the check is going to fail, we know the boolean is false *)
Lemma encoding_same:
  forall b str cont,
    bool_encoding b str (Acheck str::cont) -> b = CannotExit.
Proof.
  intros b str cont H.
  remember (Acheck str::cont) as prevcont.
  induction H; intros; auto; inversion Heqprevcont.
  subst. destruct STRICT as [_ NEQ].
  exfalso. apply NEQ. auto.
Qed.

Lemma encode_next:
  forall b inp cont r,
    bool_encoding b inp (Areg r::cont) <->
    bool_encoding b inp cont.
Proof.
  intros b inp cont r. split; intros H.
  - inversion H; subst.
    inversion ENCODE; subst; auto.
  - destruct inp. constructor. inversion H; subst; auto.
Qed.

Lemma encode_close:
  forall b inp cont g,
    bool_encoding b inp (Aclose g::cont) <->
    bool_encoding b inp cont.
Proof.
  intros b inp cont g. split; intros H.
  - inversion H; subst.
    inversion ENCODE; subst; auto.
  - destruct inp. constructor. inversion H; subst; auto.
Qed.



(** * Second Step: encoding equality  *)
(* the two tree constructions are equal *)

Theorem encode_equal:
  forall inp cont b t gm
    (PIKE: pike_actions cont)
    (ENCODE: bool_encoding b inp cont)
    (TREE: is_tree cont inp gm forward t),
    bool_tree cont inp b t.
Proof.
  intros inp cont b t gm PIKE ENCODE TREE.
  generalize dependent b.
  remember forward as dir.
  induction TREE; inversion PIKE; subst; intros;
    try solve[constructor; auto]; try solve [inversion H1; inversion H0].
  - assert (b = CanExit).
    { eapply encoding_different; eauto. }
    subst. constructor. eapply IHTREE; eauto.
    inversion ENCODE; subst; auto.
  - assert (b = CannotExit).
    { eapply encoding_same; eauto. }
    subst. constructor.
  - constructor; apply IHTREE; auto;
      inversion ENCODE; subst; auto.
  - constructor; apply IHTREE; auto;
      inversion ENCODE; subst; auto.
  - apply encode_next in ENCODE.
    subst. econstructor; eauto. apply IHTREE; auto.
    destruct nextinp. destruct inp. simpl in READ.
    destruct next0; inversion READ. destruct (char_match t cd); inversion READ; subst.
    eapply true_encoding; eauto.
  - apply encode_next in ENCODE. inversion H1. inversion H0. subst. constructor.
    + apply IHTREE1; auto.
      { constructor; try constructor; auto. }
      apply encode_next. auto.
    + apply IHTREE2; auto.
      { constructor; try constructor; auto. }
      apply encode_next. auto.
  - constructor. subst. simpl in IHTREE. apply IHTREE; eauto.
    { inversion H1. subst. inversion H0. subst.
      repeat progress (constructor; auto). }
    inversion ENCODE; subst; constructor; constructor; auto.
  (* - constructor; auto. apply IHTREE; auto. *)
    (* { inversion H1. inversion H0. } *)
    (* apply encode_next. apply encode_next. apply encode_next in ENCODE. auto. *)
  (* - constructor; auto. apply IHTREE; auto. *)
  (*   apply encode_next in ENCODE. auto. *)
  - destruct plus.
    { pike_subset. }
    eapply tree_quant_free; eauto.
    + eapply IHTREE1; auto.
      { inversion H1. inversion H0. subst.
        repeat progress (constructor; auto). }
      apply encode_next. eapply false_encoding; eauto.
    + subst. eapply IHTREE2; auto. apply encode_next in ENCODE. auto.
  - constructor. apply IHTREE; auto.
    { inversion H1. inversion H0. subst. repeat progress (constructor; auto). }
    apply encode_next in ENCODE.
    apply encode_next. apply encode_close. auto.
Qed.
    
Corollary boolean_correct:
  forall r str t,
    pike_regex r ->
    priotree r str t ->
    bool_tree [Areg r] (init_input str) CanExit t.
Proof.
  unfold priotree. intros r str t PIKE H.
  eapply encode_equal; eauto.
  { constructor; constructor; auto. }
  constructor. constructor. 
Qed.


(* Pie actions translate to Pike trees *)
Theorem subset_semantics:
  forall actions tree inp b
    (SUBSET: pike_actions actions)
    (ISTREE: bool_tree actions inp b tree),
    pike_subtree tree.
Proof.
  intros actions tree inp b SUBSET ISTREE.
  induction ISTREE; try eapply IHISTREE; pike_subset.
  - eapply IHISTREE1. pike_subset.
  - eapply IHISTREE2. pike_subset.
  - destruct plus; inversion H3. destruct greedy; pike_subset.
    + eapply IHISTREE1. pike_subset.
    + eapply IHISTREE1. pike_subset.
  - eapply IHISTREE. pike_subset.
Qed.
