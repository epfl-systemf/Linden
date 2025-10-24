Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Semantics Tree FunctionalSemantics.
From Linden Require Import Parameters LWParameters.
From Linden Require Import StrictSuffix.
From Warblre Require Import Base RegExpRecord.

From Linden Require Import PikeSubset SeenSets.
From Linden Require Import Correctness FunctionalPikeVM.

Section Prefix.
  Context {params: LindenParameters}.

(* Tactic for rewriting decidable equalities into propositional ones *)
Ltac wt_eq := repeat match goal with
  | [ H: (?x ==? ?y)%wt = true |- _ ] => rewrite EqDec.inversion_true in H; subst
  | [ H: (?x ==? ?y)%wt = false |- _ ] => rewrite EqDec.inversion_false in H
  | [ |- context[(?x ==? ?y)%wt] ] => destruct (x ==? y)%wt eqn:?Heq
  | [ H: context[(?x ==? ?y)%wt] |- _ ] => destruct (x ==? y)%wt eqn:?Heq
end.


Inductive starts_with: string -> string -> Prop :=
| StartsWith_nil: forall s, starts_with [] s
| StartsWith_cons: forall h t1 t2, starts_with t1 t2 -> starts_with (h :: t1) (h :: t2).

Hint Constructors starts_with : prefix.

Lemma starts_with_cons_iff: forall h1 t1 h2 t2,
  starts_with (h1 :: t1) (h2 :: t2) <-> h1 = h2 /\ starts_with t1 t2.
Proof.
  split; intros. 
  - inversion H; auto.
  - destruct H. subst. auto with prefix.
Qed.

Lemma starts_with_refl:
  forall s, starts_with s s.
Proof. intros. induction s; auto with prefix. Qed.

Lemma starts_with_trans: 
  Relation_Definitions.transitive _ starts_with.
Proof.
  unfold Relation_Definitions.transitive.
  intros s1 s2 s3 H1.

  generalize dependent s3.
  induction H1; intros; inversion H; auto with prefix.
Qed.

#[global] Add Relation string starts_with
  reflexivity proved by starts_with_refl
  transitivity proved by starts_with_trans
  as starts_with_rel.

Lemma starts_with_app_right:
  forall s1 s2 s3,
    starts_with s1 s3 -> starts_with s1 (s3 ++ s2).
Proof.
  intros s1 s2 s3 H.
  induction H; constructor; auto.
Qed.

Lemma starts_with_app_left:
  forall s1 s2 s3,
    starts_with (s1 ++ s2) s3 -> starts_with s1 s3.
Proof.
  intro s1.
  induction s1 as [| h t IH]; intros.
  - constructor.
  - inversion H.
    constructor.
    eapply IH. eauto.
Qed.

Hint Resolve starts_with_refl starts_with_app_right : prefix.

(** * Substring search *)

(* Typeclass describing a substring search routine and its axioms *)
Class StrSearch := {
  str_search : string -> string -> option nat;

  (* the found position starts with the searched substring *)
  starts_with_ss: forall s ss i, str_search ss s = Some i -> starts_with ss (List.skipn i s);
  (* there is no earlier position that starts with the searched substring *)
  no_earlier_ss: forall s ss i, str_search ss s = Some i -> forall i', i' < i -> ~ (starts_with ss (List.skipn i' s));
  (* if the substring is not found, it cannot appear at any position of the haystack *)
  not_found: forall s ss, str_search ss s = None -> forall i, i < length s -> ~ (starts_with ss (List.skipn i s))
}.

(* substring search operating on inputs rather than strings *)
Definition input_search {strs: StrSearch} (p: string) (inp: input): option input :=
  match str_search p (next_str inp) with
  | Some i => Some (advance_input_n inp i forward)
  | None => None
  end.

(* returned results are the initial input or strict prefixes of it *)
Lemma input_search_strict_suffix {strs: StrSearch}:
  forall i1 i2 p, input_search p i1 = Some i2 -> i2 = i1 \/ strict_suffix i2 i1 forward.
Proof.
  unfold input_search; intros until p.

  destruct str_search; intros [=]; eauto using advance_input_n_suffix.
Qed.

Lemma input_search_starts_with {strs: StrSearch}:
  forall i1 i2 p, input_search p i1 = Some i2 -> starts_with p (next_str i2).
Proof.
  unfold input_search.
  intros i1 i2 p H.
  destruct str_search as [n|] eqn:Hsearch; [|discriminate].
  injection H as <-.
  destruct i1. simpl.
  eauto using starts_with_ss.
Qed.

(* low inclusive, high exclusive *)
Notation input_between ilow ihigh i := ((i = ilow \/ strict_suffix i ilow forward) /\ strict_suffix ihigh i forward).

Lemma input_search_no_earlier {strs: StrSearch}:
  forall i1 i2 p,
    input_search p i1 = Some i2 ->
    forall i, input_between i1 i2 i ->
    ~ (starts_with p (next_str i)).
Proof.
Admitted.

Lemma input_search_not_found {strs: StrSearch}:
  forall i1 p, input_search p i1 = None ->
  forall i, i = i1 \/ strict_suffix i i1 forward ->
  ~ (starts_with p (next_str i)).
Proof.
Admitted.

(** * Literals *)

Inductive literal : Type :=
| Exact (s : string) (* the entire match is exactly `s` *)
| Prefix (s : string) (* the match starts with `s` *)
| Impossible. (* this indicates a match cannot exist, as opposed to Prefix [] which means we do not know anything about the match *)

Notation Nothing := (Exact []).
Notation Unknown := (Prefix []).

Definition literal_eq_dec: forall (l1 l2: literal), { l1 = l2 } + { l1 <> l2 }.
Proof. decide equality; apply string_eq_dec. Defined.
Instance literal_EqDec: EqDec literal := EqDec.make literal literal_eq_dec.

Definition prefix (l : literal) :=
  match l with
  | Exact s => s
  | Prefix s => s
  | Impossible => []
  end.

(* the concatenation of two literals *)
Definition chain_literals (l1 l2 : literal) : literal :=
  match l1 with
  | Exact s1 => match l2 with
    | Exact s2 => Exact (s1 ++ s2)
    | Prefix s2 => Prefix (s1 ++ s2)
    | Impossible => Impossible
  end
  | Prefix s1 => match l2 with
    | Impossible => Impossible
    | _ => Prefix s1
  end
  | Impossible => Impossible
  end.

Fixpoint repeat_literal (l: literal) (base: literal) (n: nat) : literal :=
  match n with
  | 0 => base
  | S n' => chain_literals l (repeat_literal l base n')
  end.

Lemma chain_literals_assoc:
  forall l1 l2 l3,
    chain_literals l1 (chain_literals l2 l3) = chain_literals (chain_literals l1 l2) l3.
Proof.
  destruct l1, l2, l3; simpl.
  all: rewrite ?app_assoc; reflexivity.
Qed.

Lemma chain_literals_impossible:
  forall l1 l2,
    chain_literals l1 l2 = Impossible <-> (l1 = Impossible \/ l2 = Impossible).
Proof.
  intros. split; intro H.
  - destruct l1, l2; (easy || auto).
  - destruct H as [H | H]; subst.
    + easy.
    + destruct l1; easy.
Qed.

(* the longest string that is a prefix of both strings *)
Fixpoint common_prefix (s1 s2 : string) : string :=
  match s1, s2 with
  | h1 :: t1, h2 :: t2 => if h1 == h2 then h1 :: common_prefix t1 t2 else []
  | _, _ => []
  end.

(* the common literal of two literals *)
Definition merge_literals (l1 l2 : literal) : literal :=
  if l1 == l2 then l1 else Prefix (common_prefix (prefix l1) (prefix l2)).

Lemma starts_with_common_prefix: forall s1 s2,
  starts_with (common_prefix s1 s2) s1.
Proof.
  induction s1; simpl.
  - reflexivity.
  - destruct s2; wt_eq; constructor; auto.
Qed.

Lemma starts_with_chain_merge_literals: forall l1 l2 l3,
  starts_with (prefix (chain_literals (merge_literals l1 l2) l3)) (prefix (chain_literals l1 l3)).
Proof.
  (*
    The more general lemma of
    forall l1 l2 l3,
      starts_with (prefix l1) (prefix l2) ->
      starts_with (prefix (chain_literals l1 l3)) (prefix (chain_literals l2 l3))
    does not hold (consider l1 = Exact [], l2 = Impossible)
    thus this lemma focuses on the specific case of merging literals *)
  unfold merge_literals; intros.
  wt_eq.
  - reflexivity.
  - destruct l3; try constructor; simpl.
    + destruct l1; simpl.
      * transitivity s0. apply starts_with_common_prefix. apply starts_with_app_right. reflexivity.
      * apply starts_with_common_prefix.
      * reflexivity.
    + destruct l1; simpl.
      * transitivity s0. apply starts_with_common_prefix. apply starts_with_app_right. reflexivity.
      * apply starts_with_common_prefix.
      * reflexivity.   
Qed.

Lemma common_prefix_comm:
  forall s1 s2,
    common_prefix s1 s2 = common_prefix s2 s1.
Proof.
  induction s1; destruct s2; simpl; wt_eq; congruence.
Qed.

Lemma merge_literals_comm:
  forall l1 l2,
    merge_literals l1 l2 = merge_literals l2 l1.
Proof.
  unfold merge_literals; intros.
  wt_eq; try congruence.
  rewrite common_prefix_comm; reflexivity.
Qed.

Lemma merge_literals_impossible:
  forall l1 l2,
    merge_literals l1 l2 = Impossible <-> (l1 = Impossible /\ l2 = Impossible).
Proof.
  unfold merge_literals; intros. split; intros.
  - wt_eq; easy.
  - destruct H; wt_eq; subst; easy.
Qed.

(* extracting literals from a character description *)
Fixpoint extract_literal_char (cd: char_descr) : literal :=
  match cd with
  | CdEmpty => Impossible
  | CdDot => Unknown
  | CdAll => Unknown
  | CdSingle c => Exact [c]
  | CdDigits => Unknown
  | CdNonDigits => Unknown
  | CdWhitespace => Unknown
  | CdNonWhitespace => Unknown
  | CdWordChar => Unknown
  | CdNonWordChar => Unknown
  | CdUnicodeProp p => Unknown
  | CdNonUnicodeProp p => Unknown
  | CdInv cd' => Unknown
  | CdRange l h => if l == h then Exact [l] else Unknown
  | CdUnion cd1 cd2 => merge_literals (extract_literal_char cd1) (extract_literal_char cd2)
  end.

(* extracting literals from a regex *)
Fixpoint extract_literal (r: regex) : literal :=
  match r with
  | Epsilon => Nothing
  | Regex.Character cd => extract_literal_char cd
  | Disjunction r1 r2 => merge_literals (extract_literal r1) (extract_literal r2)
  | Sequence r1 r2 => chain_literals (extract_literal r1) (extract_literal r2)
  | Quantified _ min (NoI.N 0) r1 => repeat_literal (extract_literal r1) Nothing min
  | Quantified _ min _ r1 => repeat_literal (extract_literal r1) Unknown min
  | Lookaround _ r1 => Unknown (* TODO: possible by merging the literals around but that requires a different way of computing literals. For instance /(?=abc)p/ => None, /(?<=abc)c/ => 'c' (but not exact nor prefix) *)
  | Group _ r1 => extract_literal r1
  | Anchor _ => Nothing (* TODO: can be used to detect impossible matches, like /\b\B/, but this requires restructuring this function *)
  | Backreference _ => Unknown (* TODO: possible to incorporate by having a group map from group id to `literal`. Then something like /(abc)\1/ can be extracted as `abcabc` *)
  end.

Definition extract_action_literal (a : action) : literal :=
  match a with
  | Areg r => extract_literal r
  | Acheck _ => Nothing
  | Aclose _ => Nothing
  end.

Fixpoint extract_actions_literal (acts : list action) : literal :=
  match acts with
  | [] => Nothing
  | a :: rest => chain_literals (extract_action_literal a) (extract_actions_literal rest)
  end.

Hint Unfold
  prefix
  chain_literals
  merge_literals
  common_prefix
  merge_literals
  extract_action_literal
  extract_actions_literal : prefix.
Hint Resolve
  starts_with_common_prefix : prefix.
Hint Rewrite
  common_prefix_comm
  merge_literals_comm : prefix.

Section LiteralExtraction.
  Context (rer: RegExpRecord).
  Context (no_i_flag : RegExpRecord.ignoreCase rer = false).

Lemma char_match_range_same: forall c l,
  char_match rer c (CdRange l l) = true -> c = l.
Proof.
  unfold char_match, char_match'. intros ? ? H.
  rewrite
    Character.numeric_pseudo_bij,
    CharSet.exist_canonicalized_equiv,
    CharSet.exist_spec in H.
  unfold CharSet.Exists in H.
  destruct H as [x [H1 H2]].
  assert (x = l). {
    rewrite CharSet.range_spec in H1.
    assert (Character.numeric_value x = Character.numeric_value l) as H3 by lia.
    assert (Character.from_numeric_value (Character.numeric_value x) = Character.from_numeric_value (Character.numeric_value l)) as H4 by auto.
    
    repeat rewrite Character.numeric_pseudo_bij in H4.
    assumption.
  } subst.

  repeat rewrite (canonicalize_casesenst rer _ no_i_flag) in H2.
  symmetry. apply EqDec.inversion_true. assumption.
Qed.

Lemma chain_literals_extract_char:
  forall rest s c cd,
    starts_with (prefix rest) s ->
    char_match rer c cd = true ->
    starts_with (prefix (chain_literals (extract_literal_char cd) rest)) (c :: s).
Proof.
  intros rest s c cd Hstart Hmatch.

  Ltac unfold_match H :=
    unfold char_match in H; rewrite (canonicalize_casesenst _ _ no_i_flag) in H.

  induction cd;
    (* there is no known literal *)
    try solve[simpl; destruct rest; constructor].
  (* CdSingle *)
  - unfold_match Hmatch.
    assert (c = c0). {
      simpl in Hmatch. rewrite (canonicalize_casesenst _ _ no_i_flag) in Hmatch.
      wt_eq. reflexivity.
    } subst.
    simpl.
    destruct rest; simpl; eauto with prefix.
  (* CdRange *)
  - simpl. wt_eq.
    2: destruct rest; constructor.
    apply char_match_range_same in Hmatch. subst.

    destruct rest; simpl; eauto with prefix.
  (* CdUnion *)
  - unfold_match Hmatch. simpl in Hmatch.
    apply Bool.orb_prop in Hmatch. destruct Hmatch.
    + etransitivity.
      * eapply starts_with_chain_merge_literals.
      * eapply IHcd1. unfold char_match. rewrite canonicalize_casesenst; eauto.
      + simpl. rewrite merge_literals_comm.
      etransitivity.
      * eapply starts_with_chain_merge_literals.
      * eapply IHcd2. unfold char_match. rewrite canonicalize_casesenst; eauto.
Qed.

(* generalization of extract_literal_prefix on the group map and the list of actions *)
Lemma extract_literal_prefix_general:
  forall acts tree inp gm,
    is_tree rer acts inp Groups.GroupMap.empty forward tree ->
    (exists result, tree_res tree gm inp forward = Some result) ->
    starts_with (prefix (extract_actions_literal acts)) (next_str inp).
Proof.
  intros acts tree inp gm Htree [result Hleaf].

  remember (forward) as dir.
  generalize dependent result.
  generalize dependent gm.
  induction Htree; intros; subst;
    (* the prefix is empty *)
    try solve[(constructor || simpl; destruct (extract_actions_literal cont); constructor)];
    (* the literal is that of the rest of the actions *)
    try solve[simpl in *;
      destruct (extract_actions_literal cont); eapply IHHtree; eauto with prefix];
    (* mismatch violating tree_res result *)
    try discriminate Hleaf.
  
  (* tree_char *)
  - (* there is a character to read *)
    unfold read_char in READ; destruct inp; destruct next; try discriminate READ; subst;
    
    (* the character matches *)
    destruct char_match eqn:Heqmatch; try discriminate READ; injection READ; intros; subst.

    apply chain_literals_extract_char; eauto.
  (* tree_disj *)
  - simpl in Hleaf. unfold seqop in Hleaf.
    destruct (tree_res t1) eqn:Heqres.
    + etransitivity; eauto using starts_with_chain_merge_literals.
    + simpl. rewrite merge_literals_comm.
      etransitivity; eauto using starts_with_chain_merge_literals.
  (* tree_sequence *)
  - simpl. rewrite <-chain_literals_assoc.
    eauto.
  (* tree_quant_forced *)
  - simpl.
    destruct min.
    (* min = 0 *)
    + destruct plus. destruct n.
      (* max > 0 *)
      2, 3: rewrite <- chain_literals_assoc; eapply IHHtree; eauto.
      (* min = max = 0 *)
      simpl in *. destruct extract_actions_literal; destruct extract_literal; simpl;
      try rewrite app_nil_r;
      (eapply starts_with_app_left; eapply IHHtree; eauto) ||
      eauto.
      (* min > 0 *)
    + destruct plus. destruct n.
      all: rewrite <- chain_literals_assoc; eapply IHHtree; eauto.
  (* tree_quant_free *)
  - simpl.
    destruct plus; destruct extract_actions_literal; constructor.
Qed.

Lemma extract_literal_char_impossible_tree_res:
  forall cont cd c inp gm,
    extract_literal_char cd = Impossible ->
    char_match rer c cd = true ->
    tree_res cont gm inp forward = None.
Proof.
  intros cont cd c inp gm Hextract Hmatch.
  induction cd;
    (* the cd does not produce Impossible *)
    try solve[discriminate].
  
  - (* CdRange *)
    simpl in Hextract. wt_eq; discriminate.
  - (* CdUnion *)
    simpl in Hextract.
    apply merge_literals_impossible in Hextract as [Hcd1 Hcd2].

    unfold char_match in *. simpl in Hmatch.
    apply Bool.orb_prop in Hmatch as [Hm1 | Hm2]; eauto.
Qed.

Lemma extract_literal_impossible_general:
  forall acts tree inp gm,
    is_tree rer acts inp Groups.GroupMap.empty forward tree ->
    extract_actions_literal acts = Impossible ->
    tree_res tree gm inp forward = None.
Proof.
  intros acts tree inp gm Htree Hextract.

  remember (forward) as dir.
  generalize dependent gm.
  induction Htree; intros; subst;
    (* the result is that of the rest of the actions *)
    try solve[simpl in *; destruct (extract_actions_literal cont); eauto].
  
  (* tree_done *)
  - discriminate.
  (* tree_char *)
  - (* there is a character to read *)
    unfold read_char in READ. destruct inp, next; [discriminate|].
    (* the character matches *)
    destruct char_match eqn:Hmatch; [|discriminate].

    apply chain_literals_impossible in Hextract as [Hcd | Hcont].
    + eapply extract_literal_char_impossible_tree_res; eauto.
    + simpl. unfold advance_input'.
      injection READ as <-. subst. eauto.
  (* tree_disj *)
  - simpl in Hextract. simpl. unfold seqop.
    simpl in IHHtree1, IHHtree2. rewrite chain_literals_impossible in IHHtree1, IHHtree2.
    apply chain_literals_impossible in Hextract as [Hmerge | Hcont].
    + apply merge_literals_impossible in Hmerge as [Hex1 Hex2].
      erewrite IHHtree1, IHHtree2; auto.
    + erewrite IHHtree1, IHHtree2; auto.
  (* tree_sequence *)
  - simpl in Hextract, IHHtree.
    rewrite chain_literals_assoc in IHHtree.
    eapply IHHtree; eauto.
  (* tree_quant_forced *)
  - simpl in Hextract |- *.
    apply chain_literals_impossible in Hextract as [Hrep | Hcont].
    + destruct plus; [destruct n|];
        apply chain_literals_impossible in Hrep as [? | ?];
        eapply IHHtree; auto;
        simpl; do 2 rewrite chain_literals_impossible; auto.
    + eapply IHHtree; auto.
      simpl; do 2 rewrite chain_literals_impossible; auto.
  (* tree_quant_free *)
  - assert (Hex: extract_actions_literal cont = Impossible). {
      simpl in Hextract. destruct plus; now destruct extract_actions_literal.
    }
    unfold greedy_choice.
    destruct greedy.
    + simpl. unfold seqop.
      rewrite IHHtree1, IHHtree2; auto.
      simpl. rewrite Hex. destruct plus; [destruct n|]; destruct (extract_literal r1); reflexivity.
    + simpl. unfold seqop.
      rewrite IHHtree1, IHHtree2; auto.
      simpl. rewrite Hex. destruct plus; [destruct n|]; destruct (extract_literal r1); reflexivity.
  (* tree_lk *)
  - simpl in Hextract |- *.
    destruct extract_actions_literal eqn:Heqex in Hextract; try easy.
     
    rewrite IHHtree2 by auto.
    destruct positivity.
    + admit. (* FIXME: probably needs dir to be generalized *)
    + now destruct tree_res.
  (* tree_backref *)
  - (* since there is no result on nextinp, read_backref must have failed. Contradiction. *)
    admit.
Admitted.

Lemma extract_actions_literal_regex:
  forall r, extract_actions_literal [Areg r] = extract_literal r.
Proof.
  intros.
  unfold extract_actions_literal. simpl. destruct extract_literal.
  1: simpl; rewrite app_nil_r.
  all: reflexivity.
Qed.

(* main theorem: every match starts with the extracted literal *)
Theorem extract_literal_prefix:
  forall r tree inp,
    is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree ->
    (exists result, first_leaf tree inp = Some result) ->
    starts_with (prefix (extract_literal r)) (next_str inp).
Proof.
  intros.
  rewrite <- (extract_actions_literal_regex r).
  eapply extract_literal_prefix_general; eassumption.
Qed.

Lemma is_none_iff_not_exists_some:
  forall {A: Type} (o: option A),
    o = None <-> ~ (exists x: A, o = Some x).
Proof.
  split; intro H.
  - intros [? ?]. now subst.
  - destruct o; [exfalso|]; eauto.
Qed.

(* the contraposition of extract_literal_prefix *)
Corollary extract_literal_prefix_contra:
  forall r tree inp,
    is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree ->
    ~(starts_with (prefix (extract_literal r)) (next_str inp)) ->
    first_leaf tree inp = None.
Proof.
  intros.
  rewrite is_none_iff_not_exists_some.
  eauto using extract_literal_prefix.
Qed.

(* extracting Impossible means there can be no match *)
Theorem extract_literal_impossible:
  forall r tree inp,
    is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree ->
    extract_literal r = Impossible ->
    first_leaf tree inp = None.
Proof.
  intros.
  rewrite <- (extract_actions_literal_regex r) in *.
  eapply extract_literal_impossible_general; eassumption.
Qed.

End LiteralExtraction.

Section PrefixedEngine.
  Context (rer: RegExpRecord).
  Context {VMS: VMSeen}.
  Context (no_i_flag : RegExpRecord.ignoreCase rer = false).

(* interface of an executable engine *)
Class Engine := {
  exec: regex -> input -> option leaf;

  (* asserts the supported subset of regexes *)
  supported_regex: regex -> Prop;

  (* the execution follows the backtracking tree semantics *)
  exec_correct: forall r inp ol,
    supported_regex r ->
      ((exists tree,
        is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree /\
        first_leaf tree inp = ol) <->
      exec r inp = ol)
}.

(* relation that one input is a non-strict prefix of another *)
Inductive input_prefix : input -> input -> Prop :=
| ip_eq : forall inp, input_prefix inp inp
| ip_prev : forall inp1 inp2 inp3,
    advance_input inp1 forward = Some inp2 ->
    input_prefix inp2 inp3 ->
    input_prefix inp1 inp3.

Lemma ip_prev':
  forall inp1 inp2 inp3,
    input_prefix inp1 inp2 ->
    advance_input inp2 forward = Some inp3 ->
    input_prefix inp1 inp3.
Proof. induction 1; eauto using ip_prev, ip_eq. Qed.

(* equivalence between input_prefix and strict_suffix *)
Lemma input_prefix_strict_suffix:
  forall i1 i2,
    input_prefix i1 i2 <->
      i2 = i1 \/ strict_suffix i2 i1 forward.
Proof.
  split; intros H.
  - induction H; [auto|].
    destruct IHinput_prefix; subst; eauto using ss_advance, ss_next'.
  - destruct H; [subst; auto using ip_eq|].
    remember forward as dir.
    induction H; subst; eauto using ip_eq, ip_prev, ip_prev'.
Qed.

(* for each input position we run the engine and return the earliest match *)
Fixpoint search_from {engine:Engine} (r: regex) (next: string) (prev: string): option leaf :=
  match (exec r (Input next prev)) with
  | Some leaf => Some leaf
  | None => match next with
            | [] => None
            | c::t => search_from r t (c::prev)
            end
  end.

Definition pref_str (i: input) : string :=
  match i with
  | Input _ pref => pref
  end.

(* the string-quadratic algorithm described in RegExpBuiltinExec *)
Definition BuiltinExec {engine:Engine} (r:regex) (inp:input) : option leaf :=
  search_from r (next_str inp) (pref_str inp).

(* prefixed version *)
Definition BuiltinExecPrefixed {strs:StrSearch} {engine:Engine} (r:regex) (inp:input) : option leaf :=
  let lit := extract_literal r in
  if lit == Impossible then None else
    let p := prefix lit in
    (* we skip the initial input that does not match the prefix *)
    match (input_search p inp) with
    | None => None (* if prefix is not present anywhere, then we cannot match *)
    | Some i => search_from r (next_str i) (pref_str i)
    end.

Lemma is_tree_productivity: forall r inp gm dir,
  exists tree, is_tree rer [Areg r] inp gm dir tree.
Proof. eexists. apply FunctionalUtils.compute_tr_reg_is_tree. Qed.

Lemma search_from_before_jump_eq {strs:StrSearch} {engine:Engine}:
  forall i r inp inp',
    supported_regex r ->
    input_search (prefix (extract_literal r)) inp = Some inp' ->
    input_prefix i inp' ->
    input_prefix inp i ->
    search_from r (next_str i) (pref_str i) = search_from r (next_str inp') (pref_str inp').
Proof.
  intros i r inp inp' Hsubset Hsearch Hprefix Hlow.
  induction Hprefix.
  - reflexivity.
  - pose proof H as Hadvance.
    specialize (IHHprefix Hsearch).
    unfold advance_input in H. destruct inp1 as [next1 pref1] eqn:Hinp1, next1 eqn:Hnext1; [easy|].
    inversion H. rewrite <-H1 in IHHprefix.

    assert (Hnone: exec r (Input (t :: s) pref1) = None). {
      assert (Hbetween: input_between inp inp3 inp1). {
        rewrite input_prefix_strict_suffix in Hprefix, Hlow.
        split; destruct Hprefix, Hlow; subst; eauto using ss_next', ss_advance.
      }

      subst.
      pose proof (is_tree_productivity r (Input (t :: s) pref1) Groups.GroupMap.empty forward) as [tree Htree].
      rewrite <-exec_correct; [|assumption].
      eauto using input_search_no_earlier, extract_literal_prefix_contra.
    }
    simpl.
    rewrite Hnone.
    eauto using ip_prev'.
Qed.

Lemma input_search_exec_none {strs:StrSearch} {engine:Engine}:
  forall i r inp,
    supported_regex r ->
    input_search (prefix (extract_literal r)) inp = None ->
    input_prefix inp i ->
    exec r i = None.
Proof.
  intros i r inp Hsubset Hsearch Hlow.
  rewrite input_prefix_strict_suffix in Hlow.
  rewrite <-exec_correct; [|assumption].
  pose proof (is_tree_productivity r i Groups.GroupMap.empty forward) as [tree Htree].
  eauto using input_search_not_found, extract_literal_prefix_contra.
Qed.

Lemma search_from_none_prefix {strs:StrSearch} {engine:Engine}:
  forall i r inp,
    supported_regex r ->
    input_search (prefix (extract_literal r)) inp = None ->
    input_prefix inp i ->
    search_from r (next_str i) (pref_str i) = None.
Proof.
  intros [next pref] r inp Hsubset Hsearch Hprefix.
  generalize dependent pref.
  induction next; intros pref Hprefix.
  - simpl; erewrite input_search_exec_none; eauto using ip_eq.
  - simpl in *.
    erewrite IHnext. erewrite input_search_exec_none.
    all: eauto using ip_prev'.
Qed.

Lemma input_search_exec_impossible {strs:StrSearch} {engine:Engine}:
  forall inp r,
    supported_regex r ->
    extract_literal r = Impossible ->
    exec r inp = None.
Proof.
  intros inp r Hsubset Hextract.
  rewrite <-exec_correct; [|assumption].
  pose proof (is_tree_productivity r inp Groups.GroupMap.empty forward) as [tree Htree].
  eauto using extract_literal_impossible.
Qed.

Lemma search_from_impossible_prefix {strs:StrSearch} {engine:Engine}:
  forall inp r,
    supported_regex r ->
    extract_literal r = Impossible ->
    search_from r (next_str inp) (pref_str inp) = None.
Proof.
  intros [next pref] r Hsubset Hextract.
  generalize dependent pref.
  induction next; intros pref.
  - simpl; erewrite input_search_exec_impossible; eauto.
  - simpl in *.
    erewrite IHnext. erewrite input_search_exec_impossible; eauto.
Qed.

Theorem builtin_exec_equiv {strs:StrSearch} {engine:Engine}:
  forall r inp,
    supported_regex r ->
    BuiltinExec r inp = BuiltinExecPrefixed r inp.
Proof.
  intros r inp Hsubset.
  unfold BuiltinExec, BuiltinExecPrefixed.
  wt_eq.
  + eapply search_from_impossible_prefix; eauto.
  + destruct input_search eqn:Hsearch.
    - assert (input_prefix inp i). {
        apply input_search_strict_suffix in Hsearch.
        now rewrite <-input_prefix_strict_suffix in Hsearch.
      }
      eapply search_from_before_jump_eq; eauto using ip_eq.
    - eapply search_from_none_prefix; eauto using ip_eq.
Qed.

(* TODO: replace with theorem where the fuel is derived from the complexity of the PikeVM *)
Axiom pike_vm_fuel: forall r inp, pike_vm_match rer r inp <> OutOfFuel.

(* we show that the PikeVM fits the scheme of an engine *)
#[refine]
Instance PikeVMEngine: Engine := {
  exec r inp := match pike_vm_match rer r inp with
                | OutOfFuel => None
                | Finished res => res
                end;
  supported_regex := pike_regex;
}.
  (* exec_correct *)
  intros r inp ol Hsubset.
  destruct pike_vm_match eqn:Hmatch; [pose proof pike_vm_fuel r inp; contradiction|].
  split.
  - intros [tree [Htree Hleaf]].
    subst. eauto using pike_vm_match_correct, pike_vm_correct.
  - intros ?; subst.
    pose proof (is_tree_productivity r inp Groups.GroupMap.empty forward) as [tree Htree].
    exists tree.
    split.
    + eassumption.
    + symmetry. eauto using pike_vm_match_correct, pike_vm_correct.
Qed.

End PrefixedEngine.
End Prefix.
