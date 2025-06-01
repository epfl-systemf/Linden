Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeTree PikeVM.
From Linden Require Import PikeTreeSeen PikeVMSeen.
From Linden Require Import PikeEquiv PikeSubset.
From Warblre Require Import Base.

(** * Canonicalization  *)

(* removes epsilon in sequences as much as possible *)
Fixpoint rm_eps (r:regex) : regex :=
  match r with
  | Epsilon => Epsilon
  | Regex.Character _ | Lookaround _ _ | Anchor _ | Backreference _ => r
  | Disjunction r1 r2 => Disjunction (rm_eps r1) (rm_eps r2)
  | Quantified greedy min delta r1 => Quantified greedy min delta (rm_eps r1)
  | Group gid r1 => Group gid (rm_eps r1)
  | Sequence r1 r2 =>
      match (rm_eps r1) with
      | Epsilon => rm_eps r2
      | rm1 =>
          match (rm_eps r2) with
          | Epsilon => rm1
          | rm2 => Sequence rm1 rm2
          end
      end
  end.

(* split sequences into individual actions. only sequences at the top-level *)
(* and removes epsilon inside regexes *)
Fixpoint canonicalize (a:actions) : actions :=
  match a with
  | [] => []
  | Acheck str :: cont => Acheck str :: canonicalize cont
  | Aclose gid :: cont => Aclose gid :: canonicalize cont
  | Areg r :: cont =>
      match rm_eps r with
      | Epsilon => canonicalize cont
      | Sequence r1 r2 => Areg r1 :: Areg r2 :: canonicalize cont
      | r' => Areg r' :: canonicalize cont
      end
  end.


(* The previous definition implies an induction over the list of actions AND an induction over the regex in some proofs *)
(* Maybe it's better to define a single inductive relation, and reason by induction over this relation *)
(* ind_can a1 a2 when a2 is the canonicalization of a1 *)
Inductive ind_can: actions -> actions -> Prop :=
| can_empty:
  ind_can [] []
| can_check:
  forall str cont cancont
    (CAN: ind_can cont cancont),
    ind_can (Acheck str::cont) (Acheck str::cancont)
| can_close:
  forall gid cont cancont
    (CAN: ind_can cont cancont),
    ind_can (Aclose gid::cont) (Aclose gid::cancont)
| can_epsilon:
  forall r cont cancont
    (EPS: rm_eps r = Epsilon)
    (CAN: ind_can cont cancont),
    ind_can (Areg r::cont) cancont
| can_seq:
  forall r r1 r2 cont cancont
    (SEQ: rm_eps r = Sequence r1 r2)
    (CAN: ind_can cont cancont),
    ind_can (Areg r::cont) (Areg r1::Areg r2::cancont)
| can_reg:
  forall r cont cancont
    (NOEPS: rm_eps r <> Epsilon)
    (NOSEQ: forall r1 r2, rm_eps r <> Sequence r1 r2)
    (CAN: ind_can cont cancont),
    ind_can (Areg r::cont) (Areg (rm_eps r)::cancont).

(* the functional and inductive versions are equivalent *)
Theorem canonicalize_correct:
  forall act1 act2, canonicalize act1 = act2 <-> ind_can act1 act2.
Proof.
  intros act1 act2. split; intros.
  - generalize dependent act2.
    induction act1; intros; simpl in H.
    { subst. constructor. }
    destruct a; try solve[rewrite <- H; constructor; eauto].
    destruct (rm_eps r) eqn:RMR;
      try solve[rewrite <- H; rewrite <- RMR; apply can_reg; auto; rewrite RMR;
                try intros r1 r2 NOT; try intros NOT; inversion NOT].
    { constructor; auto. }
    rewrite <- H. apply can_seq; auto.
  - induction H; try solve[simpl; subst; auto].
    + simpl. rewrite EPS. auto.
    + simpl. rewrite SEQ. rewrite IHind_can. auto.
    + simpl. destruct (rm_eps r) eqn:RMR; try contradiction;
        try solve[f_equal; auto].
      specialize (NOSEQ r0_1 r0_2). contradiction.
Qed.

(* removing epsilons preserves groups *)
Lemma rm_eps_def_groups:
  forall r, def_groups r = def_groups (rm_eps r).
Proof.
  intros r. induction r; try solve[simpl; auto].
  { simpl. rewrite IHr1. rewrite IHr2. auto. }
  2: { simpl. f_equal. auto. } 
  simpl. destruct (rm_eps r1) eqn:RM1;
    solve[simpl in IHr1; rewrite IHr1; auto; simpl;
          rewrite IHr2; destruct (rm_eps r2) eqn:RM2; simpl; auto;
          rewrite app_nil_r; auto].
Qed.

(* removing epsilon preserves pike subset *)
Lemma rm_eps_subset:
  forall r,
    pike_regex r ->
    pike_regex (rm_eps r).
Proof.
  intros r H. induction H; pike_subset.
  simpl. destruct (rm_eps r1) eqn:RM1; auto; destruct (rm_eps r2) eqn:RM2; pike_subset.
Qed.

Lemma subset_rm_eps:
  forall r,
    pike_regex (rm_eps r) ->
    pike_regex r.
Proof.
  intros r H. induction r; pike_subset;
    try solve [try apply IHr1; try apply IHr2; try apply IHr; inversion H; pike_subset].
  - simpl in H.
    destruct (rm_eps r1) eqn:RM1; destruct (rm_eps r2) eqn:RM2; try apply IHr1; pike_subset.
  - simpl in H.
    destruct (rm_eps r1) eqn:RM1; destruct (rm_eps r2) eqn:RM2; try apply IHr2; pike_subset.
Qed.    

Lemma rm_eps_not_subset:
  forall r,
    ~ pike_regex r ->
    ~ pike_regex (rm_eps r).
Proof.
  unfold not. intros r H H0. apply H. apply subset_rm_eps. auto.
Qed.

(* a representation implies the canonical representation *)
Lemma rm_eps_rep:
  forall r code pcstart pcend,
    nfa_rep r code pcstart pcend ->
    nfa_rep (rm_eps r) code pcstart pcend.
Proof.
  intros r code pcstart pcend H.
  induction H;
    try solve [simpl; econstructor; eauto; rewrite <- rm_eps_def_groups; auto].
  2: { apply nfa_unsupported; auto. apply rm_eps_not_subset. auto. }
  simpl. destruct (rm_eps r1) eqn:RM1;
    try solve[destruct (rm_eps r2) eqn:RM2; try solve[econstructor; eauto];
      inversion IHnfa_rep2; try in_subset; subst; auto].
  inversion IHnfa_rep1; try in_subset; subst. auto.
Qed.    

(* same on actions *)
(* here we need the pike_actions hypothesis *)
(* because r1;r2 could be represented with a single KillThread instruction *)
(* when r2 is not in subset *)
(* but by splitting the sequence, we would require a representation for r1 *)
(* nfa_rep is only deterministic for the pike subset *)
Theorem canonicalize_rep:
  forall act code pc n,
    pike_actions act ->
    actions_rep act code pc n ->
    actions_rep (canonicalize act) code pc n.
Proof.
  intros act code pc n SUBSET H. induction H;
    try solve[simpl; econstructor; eauto].
  simpl. destruct a; try solve[econstructor; eauto; pike_subset].
  inversion ACTION; subst.
  apply rm_eps_rep in NFA as RMNFA. 
  destruct (rm_eps r) eqn:RM;
    try solve[econstructor; eauto; try solve[pike_subset]; constructor; auto; pike_subset].
  - inversion RMNFA; try in_subset. subst. auto; pike_subset.
  - inversion RMNFA; subst.
    2: { pike_subset. apply rm_eps_subset in H1. rewrite RM in H1. pike_subset. in_subset. }
    repeat (econstructor; eauto); pike_subset.
Qed.

(** * Trees of canonicalized ations  *)

Lemma eps_tree:
  forall r cont inp b t,
    bool_tree cont inp b t ->
    rm_eps r = Epsilon ->
    bool_tree (Areg r::cont) inp b t.
Proof.
  intros r cont inp b t TREE RMR.
  generalize dependent t. generalize dependent cont. generalize dependent inp. generalize dependent b.
  induction r; intros; try solve[inversion RMR].
  { constructor. auto. }
  simpl in RMR.
  destruct (rm_eps r1) eqn:RM1; destruct (rm_eps r2) eqn:RM2; inversion RMR.
  constructor. eapply IHr1; eauto.
Qed.

Lemma seq_tree:
  forall r r1 r2 cont inp b t,
    bool_tree (Areg r1::Areg r2::cont) inp b t ->
    rm_eps r = Sequence r1 r2 ->
    bool_tree (Areg r::cont) inp b t.
Proof.
  intros r r1 r2 cont inp b t TREE RMR.


  generalize dependent r1. generalize dependent r2.
  generalize dependent cont. generalize dependent b. generalize dependent t.
  induction r; intros; try solve[inversion RMR].
  constructor.
  destruct (rm_eps r1) eqn:RM1.
  - admit.
  - simpl in RMR. rewrite RM1 in RMR. destruct (rm_eps r2) eqn:RM2; inversion RMR; subst.
    +
      (* the induction hypotheses are unusable *)
  
  (* destruct r; try solve[inversion RMR]. *)
  (* assert (rm_eps r3 <> Epsilon). *)
  (* { intros H. simpl in RMR. rewrite H in RMR. *)

Admitted.


Theorem canonic_tree':
  forall act canact inp b t,
    ind_can act canact -> 
    bool_tree canact inp b t ->
    bool_tree act inp b t.
Proof.
  intros act canact inp b t H H0.
  generalize dependent t. generalize dependent b. generalize dependent inp.
  induction H; intros; auto.
  - inversion H0; subst; constructor.
    apply IHind_can. auto.
  - inversion H0; subst; constructor.
    apply IHind_can. auto.
  - apply eps_tree; auto.
  - eapply seq_tree; eauto.
    admit.
  (* missing some results about equivalent continuations? *)
  - admit.
Admitted.


(* the previous version, before the inductive canonicalize *)
Theorem canonic_tree:
  forall act inp b t,
    bool_tree (canonicalize act) inp b t ->
    bool_tree act inp b t.
Proof.
  intros act inp b t H.
  remember (canonicalize act) as can.
  generalize dependent act.
  induction H; intros.
  - induction act.
    { constructor. }
    simpl in Heqcan. destruct a; try solve[inversion Heqcan].
    destruct (rm_eps r) eqn:RMR; try solve[inversion Heqcan].
    generalize dependent act.
    induction r; intros; try solve[inversion RMR].
    + constructor. auto.
    + simpl in RMR.
      destruct (rm_eps r1) eqn:RMR1; destruct (rm_eps r2) eqn:RM2; inversion RMR; auto.
      constructor. apply IHr1; auto. simpl. rewrite RM2. auto.
  - induction act.
    { inversion Heqcan. }
    simpl in Heqcan. destruct a; try solve[inversion Heqcan].
    destruct (rm_eps r) eqn:RMR; try solve[inversion Heqcan].
    2: { inversion Heqcan. apply IHbool_tree in H2. constructor. auto. }
    generalize dependent act.
    induction r; intros; try solve[inversion RMR].
    + constructor. auto.
    + simpl in RMR.
      destruct (rm_eps r1) eqn:RMR1; destruct (rm_eps r2) eqn:RM2; inversion RMR; auto.
      constructor. apply IHr1; auto. simpl. rewrite RM2. auto.
  (* yet another triple nested induction... *)
  (* I should extract separate lemmas *)
  -
Admitted.


(** * Unicity of canonical representation  *)


Lemma epsilon_rep:
  forall r code pcstart pcend,
    nfa_rep r code pcstart pcend ->
    pcstart = pcend ->
    r = Epsilon.
Proof.
  intros r code pcstart pcend H H0. induction H; auto; try solve[lia].
  - subst.
Admitted.

Lemma canonic_eps_nfa:
  forall r1 r2 c1 c2 code pcstart pcend
    (EPS1: c1 = rm_eps r1)
    (EPS2: c2 = rm_eps r2)
    (REP1: nfa_rep c1 code pcstart pcend)
    (REP2: nfa_rep c2 code pcstart pcend),
    c1 = c2.
Proof.
  intros r1 r2 c1 c2 code pcstart pcend EPS1 EPS2 REP1 REP2.
  generalize dependent r1. generalize dependent r2. generalize dependent c2.
  induction REP1; intros.
  - remember lbl as PC. rewrite HeqPC in REP2 at 1.
    induction REP2; auto.
    + lia.
    + 
Admitted.  

    


Theorem canonic_rep_unicity:
  forall c1 c2 act1 act2 code pc n,
    ind_can act1 c1 ->
    ind_can act2 c2 ->
    actions_rep c1 code pc n ->
    actions_rep c2 code pc n ->
    c1 = c2.
Proof.
  intros c1 c2 act1 act2 code pc n CAN1 CAN2 REP1 REP2.
  generalize dependent c2. generalize dependent act2.
  generalize dependent act1.
  induction REP1; intros.
  (* empty actions *)
  { 
Admitted.    
