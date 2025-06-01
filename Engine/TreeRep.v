Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeTree PikeVM.
From Linden Require Import PikeTreeSeen PikeVMSeen.
From Linden Require Import PikeEquiv PikeSubset.
From Warblre Require Import Base.


(* A predicate showing that a tree is represented at a given point in the code *)


Inductive tree_rep: tree -> code -> label -> input -> LoopBool -> nat -> Prop :=
| tr_match:
  forall code pc inp b
    (ACCEPT: get_pc code pc = Some Accept),
    tree_rep Match code pc inp b 0
| tr_jmp:
  forall code pc nextpc inp b t n
    (JMP: get_pc code pc = Some (Jmp nextpc))
    (TR: tree_rep t code nextpc inp b n),
    tree_rep t code pc inp b (S n)
| tr_begin:
  forall code pc inp b t n
    (BEGIN: get_pc code pc = Some BeginLoop)
    (TR: tree_rep t code (S pc) inp CannotExit n),
    tree_rep t code pc inp b n
| tr_choice:
  forall code pc pc1 pc2 inp b t1 t2 n1 n2
    (FORK: get_pc code pc = Some (Fork pc1 pc2))
    (TR1: tree_rep t1 code pc1 inp b n1)
    (TR2: tree_rep t2 code pc2 inp b n2),
    tree_rep (Choice t1 t2) code pc inp b (n1 + n2)
| tr_read:
  forall code pc inp nextinp b cd c t n
    (CONSUME: get_pc code pc = Some (Consume cd))
    (READ: read_char cd inp forward = Some (c, nextinp))
    (TR: tree_rep t code (S pc) nextinp CanExit n),
    tree_rep (Read c t) code pc inp b n
| tr_progress:
  forall code pc nextpc inp t n
    (ENDLOOP: get_pc code pc = Some (EndLoop nextpc))
    (TR: tree_rep t code nextpc inp CanExit n),
    tree_rep (Progress t) code pc inp CanExit n
| tr_open:
  forall code pc gid inp b t n
    (OPEN: get_pc code pc = Some (SetRegOpen gid))
    (TR: tree_rep t code (S pc) inp b n),
    tree_rep (GroupAction (Open gid) t) code pc inp b n
| tr_close:
  forall code pc gid inp b t n
    (CLOSE: get_pc code pc = Some (SetRegClose gid))
    (TR: tree_rep t code (S pc) inp b n),
    tree_rep (GroupAction (Close gid) t) code pc inp b n
| tr_reset:
  forall code pc gidl inp b t n
    (RESET: get_pc code pc = Some (ResetRegs gidl))
    (TR: tree_rep t code (S pc) inp b n),
    tree_rep (GroupAction (Reset gidl) t) code pc inp b n
| tr_readfail:
  forall code pc inp b cd
    (CONSUME: get_pc code pc = Some (Consume cd))
    (READ: read_char cd inp forward = None),
    tree_rep Mismatch code pc inp b 0
| tr_progressfail:
  forall code pc nextpc inp
    (ENDLOOP: get_pc code pc = Some (EndLoop nextpc)),
    tree_rep Mismatch code pc inp CannotExit 0.


Ltac same_instr :=
  match goal with
  | [ H1 : get_pc ?code ?pc = ?i1, H2: get_pc ?code ?pc = ?i2 |- _ ] => rewrite H1 in H2; inversion H2; subst
  end.                                                                                                       

(* Determinism of the tree representation *)
Lemma tree_rep_determ:
  forall code pc inp b t1 t2 n1 n2,
    tree_rep t1 code pc inp b n1 ->
    tree_rep t2 code pc inp b n2 ->
    t1 = t2 /\ n1 = n2.
Proof.
  intros code pc inp b t1 t2 n1 n2 H H0.
  generalize dependent t2. generalize dependent n2.
  induction H; intros.
  - inversion H0; subst; auto; same_instr.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ _ TR) as [EQT EQN].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
  - inversion H1; subst; auto; same_instr.
    specialize (IHtree_rep1 _ _ TR1) as [EQT1 EQN1].
    specialize (IHtree_rep2 _ _ TR2) as [EQT2 EQN2].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr;
      rewrite READ0 in READ; inversion READ; subst.
    specialize (IHtree_rep _ _ TR) as [EQT EQN].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ _ TR) as [EQT EQN].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ _ TR) as [EQT EQN].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ _ TR) as [EQT EQN].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ _ TR) as [EQT EQN].
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    rewrite READ0 in READ. inversion READ.
  - inversion H0; subst; auto; same_instr.
Qed.
