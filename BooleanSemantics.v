Require Import List Lia.
Import ListNotations.

Require Import Regex Chars Groups.
Require Import Tree.
Require Import Semantics.

(* An alternate definition of the semantics, using a boolean to know if one can exit a loop *)

(** * Loop Boolean  *)
(* The loop boolean, indicating if we can exit a loop iteration or not *)
(* CanExit means that we are allowed to exit any quantifier: we have read a character more recently than we have entered a free quantifier *)
(* CannotExit means we can't exit the most recent quantifier we entered, because we haven't read anything since *)
Inductive LoopBool : Type :=
| CanExit
| CannotExit.


(** * Boolean Semantics  *)
(* where checks consult the boolean instead of actually comparing strings *)

Inductive bool_tree: regex -> continuation -> input -> LoopBool -> tree -> Prop :=
| bool_epsilon:
  (* on an empty continuation *)
  forall inp b,
    bool_tree Epsilon [] inp b Match
| bool_pop_reg:
  (* pops a regex from the continuation list *)
  forall inp regcont tailcont treecont b
    (TREECONT: bool_tree regcont tailcont inp b treecont),
    bool_tree Epsilon (Areg regcont :: tailcont) inp b treecont
| bool_pop_check:
  (* pops a successful check from the continuation list *)
  (* this only checks the boolean allows exit and not the strcheck in the tree *)
  forall inp strcheck tailcont treecont
    (TREECONT: bool_tree Epsilon tailcont inp CanExit treecont),
    bool_tree Epsilon (Acheck strcheck :: tailcont) inp CanExit (CheckPass strcheck treecont)
| bool_pop_check_fail:
  (* pops a failing check from the continuation list *)
  (* this require the boolean to disallow exit *)
  forall inp strcheck tailcont,
    bool_tree Epsilon (Acheck strcheck :: tailcont) inp CannotExit (CheckFail strcheck)
| bool_pop_close:
(* pops the closing of a group from the continuation list *)
  forall inp tailcont treecont gid b
    (TREECONT: bool_tree Epsilon tailcont inp b treecont),
    bool_tree Epsilon (Aclose gid :: tailcont) inp b (CloseGroup gid treecont)
| bool_char:
  (* changes the boolean so that we can now exit *)
  forall c cd inp nextinp cont tcont b
    (READ: read_char cd inp = Some (c, nextinp))
    (TREECONT: bool_tree Epsilon cont nextinp CanExit tcont),
    bool_tree (Character cd) cont inp b (Read c tcont)
| bool_char_fail:
  forall cd inp cont b
    (READ: read_char cd inp = None),
    bool_tree (Character cd) cont inp b Mismatch
| bool_disj:
  forall r1 r2 cont t1 t2 inp b
    (ISTREE1: bool_tree r1 cont inp b t1)
    (ISTREE2: bool_tree r2 cont inp b t2),
    bool_tree (Disjunction r1 r2) cont inp b (Choice t1 t2)
| bool_sequence:
  (* adding next regex to the continuation *)
  forall r1 r2 cont t inp b
    (CONT: bool_tree r1 (Areg r2 :: cont) inp b t),
    bool_tree (Sequence r1 r2) cont inp b t
| bool_star:
  forall r1 cont titer tskip tquant inp gidl b
    (* the list of capture groups to reset *)
    (RESET: gidl = def_groups r1)
    (* doing one iteration, then a check, then executing the next quantifier *)
    (* switching the boolean such that we can't exit right away *)
    (ISTREE1: bool_tree r1 (Acheck (current_str inp)::Areg (Star r1)::cont) inp CannotExit titer)
    (* skipping the star entirely *)
    (SKIP: bool_tree Epsilon cont inp b tskip)
    (CHOICE: tquant = Choice (ResetGroups gidl titer) tskip),
    bool_tree (Star r1) cont inp b tquant
| bool_group:
  forall r1 cont treecont inp gid b
    (TREECONT: bool_tree r1 (Aclose gid :: cont) inp b treecont),
    bool_tree (Group gid r1) cont inp b (OpenGroup gid treecont).


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
  

Inductive bool_encoding: LoopBool -> string -> continuation -> Prop :=
(* with an empty continuation we can be encoded with any boolean *)
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
    (STRICT: strict_suffix str head),
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
Inductive encodes : LoopBool -> input -> continuation -> Prop :=
| encode_forward:
  forall b next pref cont
    (ENCODE: bool_encoding b next cont),
    encodes b (Input next pref) cont.


(* when we are already encoded with true, reading a new character preserves this true encoding *)
(* when we are encoded with false, reading a new character switches to being encoded with true *)
Lemma true_encoding:
  forall str c cont b,
    bool_encoding b (c::str) cont ->
    bool_encoding CanExit str cont.
Proof.
  intros str c cont b H.
  remember (c::str) as prevstr.
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
  induction H.
  - constructor. constructor.
  - inversion IHbool_encoding; subst.
    + apply to_false. constructor. auto.
    + apply cons_false. constructor. auto.
  - inversion IHbool_encoding; subst.
    + apply to_false. constructor. auto.
    + apply cons_false. constructor. auto.
  - apply to_false. apply cons_true; auto.
  - apply cons_false. auto.
  - apply cons_false. auto.
Qed.

(* if the string is different than the check, we know the boolean is true *)
Lemma encoding_different:
  forall b str strcheck cont,
    bool_encoding b str (Acheck strcheck::cont) ->
    str <> strcheck ->
    b = CanExit.
Proof.
  intros b0 str strcheck cont H.
  remember (Acheck strcheck::cont) as prevcont.
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

(** * Second Step: encoding equality  *)
(* the two tree constructions are equal *)

Theorem encode_equal:
  forall r inp cont b t
    (ENCODE: encodes b inp cont)
    (TREE: is_tree r cont inp t),
    bool_tree r cont inp b t.
Proof.
  intros r inp cont b0 t ENCODE TREE.
  generalize dependent b0.
  induction TREE; intros.
  - constructor.
  - constructor.
    eapply IHTREE; eauto.
    inversion ENCODE; subst; constructor; inversion ENCODE0; auto.
  - assert (b0 = CanExit).
    { remember (Acheck strcheck::tailcont) as cont'.
      destruct ENCODE; subst; eapply encoding_different; eauto. }
    subst. constructor. eapply IHTREE; eauto.
    inversion ENCODE; subst; constructor; inversion ENCODE0; auto.
  - assert (b0 = CannotExit).
    { remember (Acheck strcheck :: tailcont) as cont'.
      destruct ENCODE; subst; eapply encoding_same; eauto. }
    subst. constructor.
  - constructor. apply IHTREE.
    inversion ENCODE; subst; constructor; inversion ENCODE0; auto.
  - econstructor; eauto. apply IHTREE.
    destruct nextinp. destruct ENCODE; constructor; simpl in READ.
    destruct next0; inversion READ. destruct (char_match c0 cd); inversion READ; subst. eapply true_encoding; eauto.
  - constructor; auto.
  - constructor; auto.
  - constructor. apply IHTREE; eauto.
    inversion ENCODE; subst; constructor; constructor; auto.
  - eapply bool_star; eauto.
    apply IHTREE1.
    destruct ENCODE; constructor; simpl; eapply false_encoding; constructor; eauto.
  - constructor. apply IHTREE.
    destruct ENCODE; constructor; constructor; auto.
Qed.
    
Corollary boolean_correct:
  forall r str t,
    backtree r str t ->
    bool_tree r [] (init_input str) CanExit t.
Proof.
  unfold backtree. intros r str t H.
  eapply encode_equal; eauto.
  constructor. constructor.
Qed.
