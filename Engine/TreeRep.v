Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeTree PikeVM.
From Linden Require Import PikeTreeSeen PikeVMSeen.
From Linden Require Import PikeEquiv PikeSubset.
From Warblre Require Import Base.


(* A predicate showing that a tree is represented at a given point in the code *)


Inductive tree_rep: tree -> code -> label -> input -> LoopBool -> Prop :=
| tr_match:
  forall code pc inp b
    (ACCEPT: get_pc code pc = Some Accept),
    tree_rep Match code pc inp b
| tr_choice:
  forall code pc pc1 pc2 inp b t1 t2
    (FORK: get_pc code pc = Some (Fork pc1 pc2))
    (TR1: tree_rep t1 code pc1 inp b)
    (TR2: tree_rep t2 code pc2 inp b),
    tree_rep (Choice t1 t2) code pc inp b
| tr_read:
  forall code pc inp nextinp b cd c t
    (CONSUME: get_pc code pc = Some (Consume cd))
    (READ: read_char cd inp forward = Some (c, nextinp))
    (TR: tree_rep t code (S pc) nextinp CanExit),
    tree_rep (Read c t) code pc inp b
| tr_progress:
  forall code pc nextpc inp t
    (ENDLOOP: get_pc code pc = Some (EndLoop nextpc))
    (TR: tree_rep t code nextpc inp CanExit),
    tree_rep (Progress t) code pc inp CanExit
| tr_open:
  forall code pc gid inp b t
    (OPEN: get_pc code pc = Some (SetRegOpen gid))
    (TR: tree_rep t code (S pc) inp b),
    tree_rep (GroupAction (Open gid) t) code pc inp b
| tr_close:
  forall code pc gid inp b t
    (CLOSE: get_pc code pc = Some (SetRegClose gid))
    (TR: tree_rep t code (S pc) inp b),
    tree_rep (GroupAction (Close gid) t) code pc inp b
| tr_reset:
  forall code pc gidl inp b t
    (RESET: get_pc code pc = Some (ResetRegs gidl))
    (TR: tree_rep t code (S pc) inp b),
    tree_rep (GroupAction (Reset gidl) t) code pc inp b
| tr_readfail:
  forall code pc inp b cd
    (CONSUME: get_pc code pc = Some (Consume cd))
    (READ: read_char cd inp forward = None),
    tree_rep Mismatch code pc inp b
| tr_progressfail:
  forall code pc nextpc inp
    (ENDLOOP: get_pc code pc = Some (EndLoop nextpc)),
    tree_rep Mismatch code pc inp CannotExit.
  

Ltac same_instr :=
  match goal with
  | [ H1 : get_pc ?code ?pc = ?i1, H2: get_pc ?code ?pc = ?i2 |- _ ] => rewrite H1 in H2; inversion H2; subst
  end.                                                                                                       

(* Determinism of the tree representation *)
Lemma tree_rep_determ:
  forall code pc inp b t1 t2,
    tree_rep t1 code pc inp b ->
    tree_rep t2 code pc inp b ->
    t1 = t2.
Proof.
  intros code pc inp b t1 t2 H H0.
  generalize dependent t2. induction H; intros.
  - inversion H0; subst; auto; same_instr.
  - inversion H1; subst; auto; same_instr.
    subst. f_equal; auto.
  - inversion H0; subst; auto; same_instr.
    + rewrite READ0 in READ. inversion READ. subst. f_equal; auto.
    + rewrite READ0 in READ. inversion READ.
  - inversion H0; subst; auto; same_instr. f_equal; auto.
  - inversion H0; subst; auto; same_instr. f_equal; auto.
  - inversion H0; subst; auto; same_instr. f_equal; auto.
  - inversion H0; subst; auto; same_instr. f_equal; auto.
  - inversion H0; subst; auto; same_instr.
    rewrite READ0 in READ. inversion READ.
  - inversion H0; subst; auto; same_instr.
Qed.
