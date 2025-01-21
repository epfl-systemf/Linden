Require Import List Lia.
Import ListNotations.

Require Import Regex Chars Groups.
Require Import Tree.
Require Import Semantics.

(** * NFA Bytecdode *)

Definition label : Type := nat.

Inductive bytecode: Type :=
| Accept
| Consume: char_descr -> bytecode
| Jmp: label -> bytecode
| Fork: label -> label -> bytecode
| SetRegOpen: group_id -> bytecode
| SetRegClose: group_id -> bytecode
| ResetRegs: list group_id -> bytecode
| BeginLoop: bytecode
| EndLoop: label -> bytecode.    (* also contains the backedge instead of adding a jump *)

Definition code : Type := list bytecode.

Definition get_pc (c:code) (pc:label) : option bytecode :=
  List.nth_error c pc.

(** * Bytecode Properties  *)
Lemma get_prefix:
  forall c pc prev,
    get_pc (prev ++ c) (length prev + pc) = get_pc c pc.
Proof.
  unfold get_pc. intros.
  rewrite nth_error_app2; try f_equal; lia.
Qed.

Corollary get_first:
  forall c prev,
    get_pc (prev ++ c) (length prev) = get_pc c 0.
Proof.
  intros. replace (length prev) with (length prev + 0) by lia.
  apply get_prefix.
Qed.

Corollary get_first_0:
  forall c prev x,
    x = length prev ->
    get_pc (prev ++ c) (x) = get_pc c 0.
Proof.
  intros. subst. apply get_first.
Qed.

Corollary get_second:
  forall c prev,
    get_pc (prev ++ c) (S (length prev)) = get_pc c 1.
Proof.
  intros. replace (S (length prev)) with (length prev + 1) by lia.
  apply get_prefix.
Qed.

Corollary get_third:
  forall c prev,
    get_pc (prev ++ c) (S (S (length prev))) = get_pc c 2.
Proof.
  intros. replace (S (S (length prev))) with (length prev + 2) by lia.
  apply get_prefix.
Qed.

Lemma get_suffix:
  forall c suffix pc i,
    get_pc c pc = Some i ->
    get_pc (c++suffix) pc = Some i.
Proof.
  unfold get_pc. intros c suffix pc i H.
  assert (pc < length c).
  { apply nth_error_Some. rewrite H. unfold not. intros. inversion H0. }
  rewrite nth_error_app1; auto.
Qed.

Definition next_pcs (pc:label) (b:bytecode) : list label :=
  match b with
  | Consume _ | SetRegOpen _ | SetRegClose _ | ResetRegs _ | BeginLoop => [S pc]
  | Accept => []
  | Jmp l | EndLoop l => [l]
  | Fork l1 l2 => [l1; l2]
  end.

(** * NFA Compilation  *)

(* also returns the next fresh label *)
Fixpoint compile (r:regex) (fresh:label) : code * label :=
  match r with
  | Epsilon => ([], fresh)
  | Character cd => ([Consume cd], S fresh)
  | Disjunction r1 r2 =>
      let (bc1, f1) := compile r1 (S fresh) in
      let (bc2, f2) := compile r2 (S f1) in
      ([Fork (S fresh) (S f1)] ++ bc1 ++ [Jmp f2] ++ bc2, f2)
  | Sequence r1 r2 =>
      let (bc1, f1) := compile r1 fresh in
      let (bc2, f2) := compile r2 f1 in
      (bc1 ++ bc2, f2)
  | Star r1 =>
      let (bc1, f1) := compile r1 (S (S (S fresh))) in
      ([Fork (S fresh) (S f1); BeginLoop; ResetRegs (def_groups r1)] ++ bc1 ++ [EndLoop fresh], S f1)
  | Group gid r1 =>
      let (bc1, f1) := compile r1 (S fresh) in
      ([SetRegOpen gid] ++ bc1 ++ [SetRegClose gid], S f1)
  end.

(** * Inductive NFA characterization *)
(* like a representation predicate *)

Inductive is_nfa : regex -> code -> label -> label -> Prop :=
| is_nfa_epsilon:
  forall c lbl,
    is_nfa Epsilon c lbl lbl
| is_nfa_char:
  forall c cd lbl
    (CONSUME: get_pc c lbl = Some (Consume cd)),
    is_nfa (Character cd) c lbl (S lbl)
| is_nfa_disj:
  forall c r1 r2 start end1 end2
    (FORK: get_pc c start = Some (Fork (S start) (S end1)))
    (NFA1: is_nfa r1 c (S start) end1)
    (JMP: get_pc c end1 = Some (Jmp end2))
    (NFA2: is_nfa r2 c (S end1) end2),
    is_nfa
      (Disjunction r1 r2) c start end2
| is_nfa_seq:
  forall c r1 r2 start end1 end2
    (NFA1: is_nfa r1 c start end1)
    (NFA2: is_nfa r2 c end1 end2),
    is_nfa (Sequence r1 r2) c start end2
| is_nfa_star:
  forall c r1 start end1
    (FORK: get_pc c start = Some (Fork (S start) (S end1)))
    (BEGIN: get_pc c (S start) = Some (BeginLoop))
    (RESET: get_pc c (S (S start)) = Some (ResetRegs (def_groups r1)))
    (NFA1: is_nfa r1 c (S (S (S start))) end1)
    (END: get_pc c end1 = Some (EndLoop start)),
    is_nfa (Star r1) c start (S end1)
| is_nfa_group:
  forall c r1 gid start end1
    (OPEN: get_pc c start = Some (SetRegOpen gid))
    (NFA1: is_nfa r1 c (S start) end1)
    (CLOSE: get_pc c end1 = Some (SetRegClose gid)),
    is_nfa (Group gid r1) c start (S end1).

(** * Compile Characterization  *)

Lemma cons_app:
  forall A (x:A) l, x::l = [x] ++ l.
Proof. intros. simpl. auto. Qed.

Lemma is_nfa_extend:
  forall r c start endl suffix,
    is_nfa r c start endl ->
    is_nfa r (c++suffix) start endl.
Proof.
  intros r c start endl suffix H. generalize dependent suffix.
  induction H; intros; econstructor;
    try (erewrite get_suffix; eauto); try apply IHis_nfa;
    try apply IHis_nfa1; try apply IHis_nfa2.
Qed.

(* correctness of the returned fresh label *)
Lemma fresh_correct:
  forall r fresh l next,
    compile r fresh = (l, next) ->
    fresh + List.length l = next.
Proof.
  intros r.
  induction r; intros fresh l next COMPILE.
  - inversion COMPILE. subst. simpl. lia.
  - inversion COMPILE. subst. simpl. lia.
  - inversion COMPILE.
    destruct (compile r1 (S fresh)) as [bc1 f1] eqn:COMP1. destruct (compile r2 (S f1)) as [bc2 f2] eqn:COMP2.
    inversion H0. subst f2. apply IHr1 in COMP1. apply IHr2 in COMP2. simpl.
    rewrite <- COMP1 in COMP2. simpl in COMP2. rewrite app_length. simpl. lia.
  - inversion COMPILE.
    destruct (compile r1 fresh) as [bc1 f1] eqn:COMP1. destruct (compile r2 f1) as [bc2 f2] eqn:COMP2.
    inversion H0. subst f2. apply IHr1 in COMP1. apply IHr2 in COMP2.
    rewrite <- COMP1 in COMP2. rewrite app_length. lia.
  - inversion COMPILE.
    destruct (compile r (S (S (S fresh)))) as [bc1 f1] eqn:COMP1. inversion H0. apply IHr in COMP1.
    subst. simpl. rewrite app_length. simpl. lia.
  - inversion COMPILE.
    destruct (compile r (S fresh)) as [bc1 f1] eqn:COMP1. inversion H0. apply IHr in COMP1.
    subst. simpl. rewrite app_length. simpl. lia.
Qed.

Theorem compile_is_nfa:
  forall r c start endl prev,
    compile r start = (c, endl) ->
    start = List.length prev ->
    is_nfa r (prev ++ c) start endl.
Proof.
  intros r. induction r; intros.
  - inversion H. subst. rewrite app_nil_r. constructor.
  - inversion H. subst. constructor. apply get_first.
  - inversion H. destruct (compile r1 (S start)) as [bc1 end1] eqn:COMP1. destruct (compile r2 (S end1)) as [bc2 end2] eqn:COMP2.
    inversion H2. subst. apply is_nfa_disj with (end1:=end1).
    + rewrite get_first. simpl. auto.
    + apply IHr1 with (prev:=prev ++ [Fork (S (length prev)) (S end1)]) in COMP1.
      2: { rewrite app_length. simpl. lia. }
      replace (prev ++ Fork (S (length prev)) (S end1) :: bc1 ++ Jmp endl :: bc2) with
        (((prev ++ [Fork (S (length prev)) (S end1)]) ++ bc1) ++ (Jmp endl :: bc2)).
      2:{ rewrite <- app_assoc. rewrite <- app_assoc. auto. }
      apply is_nfa_extend. auto.
    + apply fresh_correct in COMP1. rewrite <- COMP1.
      replace (S (length prev) + length bc1) with (length prev + (S (length bc1))) by lia.
      rewrite get_prefix. rewrite cons_app. rewrite app_assoc. apply get_first.
    + apply IHr2 with (prev:= prev ++ Fork (S (length prev)) (S end1) :: bc1 ++ [Jmp endl]) in COMP2.
      * replace (prev ++ Fork (S (length prev)) (S end1) :: bc1 ++ Jmp endl :: bc2) with
          ((prev ++ Fork (S (length prev)) (S end1) :: bc1 ++ [Jmp endl]) ++ bc2).
        2: { rewrite <- app_assoc. simpl. apply f_equal. apply f_equal. rewrite <- app_assoc. auto. }
        auto.
      * apply fresh_correct in COMP1. rewrite <- COMP1. simpl.
        rewrite app_length. simpl. rewrite app_length. simpl. lia.
  - inversion H. destruct (compile r1 start) as [bc1 end1] eqn:COMP1. destruct (compile r2 end1) as [bc2 end2] eqn:COMP2.
    inversion H2. subst. econstructor.
    + apply IHr1 with (prev:=prev) in COMP1; auto.
      rewrite app_assoc. apply is_nfa_extend. eauto.
    + apply IHr2 with (prev:=prev ++ bc1) in COMP2; auto.
      * rewrite app_assoc. auto.
      * apply fresh_correct in COMP1. rewrite app_length. lia.
  - inversion H. destruct (compile r (S (S (S start)))) as [bc1 end1] eqn:COMP1. inversion H2. subst. constructor.
    + rewrite get_first. simpl. auto.
    + rewrite get_second. simpl. auto.
    + rewrite get_third. simpl. auto.
    + apply IHr with (prev:=prev ++ [Fork (S (length prev)) (S end1); BeginLoop; ResetRegs (def_groups r)]) in COMP1.
      * rewrite <- app_assoc in COMP1. simpl in COMP1.
        replace (prev ++ Fork (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1 ++ [EndLoop (length prev)]) with
          ((prev ++ Fork (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1) ++ [EndLoop (length prev)]).
        2: { rewrite <- app_assoc. auto. }
        apply is_nfa_extend. auto.
      * rewrite app_length. simpl. lia.
    + replace (prev ++ Fork (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1 ++ [EndLoop (length prev)]) with
          ((prev ++ Fork (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1) ++ [EndLoop (length prev)]).
      2: { rewrite <- app_assoc. auto. }
      apply fresh_correct in COMP1. subst. apply get_first_0.
      simpl. rewrite app_length. simpl. lia.
  - inversion H. destruct (compile r (S start)) as [bc1 end1] eqn:COMP1. inversion H2. subst.
    constructor.
    + rewrite get_first. simpl. auto.
    +  apply IHr with (prev:=prev ++ [SetRegOpen id]) in COMP1.
       2: { rewrite app_length. simpl. lia. }
       replace (prev ++ SetRegOpen id :: bc1 ++ [SetRegClose id]) with ((prev ++ SetRegOpen id :: bc1) ++ [SetRegClose id]).
       2:{ rewrite <- app_assoc. auto. }
       apply is_nfa_extend. rewrite <- app_assoc in COMP1. simpl in COMP1. auto.
    + replace (prev ++ SetRegOpen id :: bc1 ++ [SetRegClose id]) with ((prev ++ SetRegOpen id :: bc1) ++ [SetRegClose id]).
      2:{ rewrite <- app_assoc. auto. }
      apply get_first_0. apply fresh_correct in COMP1. subst. rewrite app_length. simpl. lia.
Qed.
