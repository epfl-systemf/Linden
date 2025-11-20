(** * Equivalence between MemoBT algorithm and MemoTree algorithm  *)

Require Import List Lia.
Import ListNotations.


From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import Parameters SeenSets.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import PikeEquiv MemoTree MemoBT.


Section MemoEquiv.
  Context {params: LindenParameters}.
  Context {MS: MemoSet params}.
  Context (rer: RegExpRecord).
  
  (* FIXME: these are generalizations of definitions used in the PikeEquiv proof *)
  (* it could be nice to only use the generalized version everywhere *)

  (* a tree and a configuration are equivalent when they are about to execute the same thing *)
  (* this means when the tree represents a given list of actions, *)
  (* the config is at a pc that will execute the nfa of that same list of actions *)
  Inductive tree_config (code:code) : (tree * group_map * input) -> config -> Prop :=
  | tc_eq:
    forall inp tree gm pc b actions
      (TREE: bool_tree rer actions inp b tree)
      (CONT: actions_rep actions code pc)
      (SUBSET: pike_actions actions),
      tree_config code (tree, gm, inp) (pc, gm, b, inp)
  | tc_reset:
    forall inp tree gm pc b gidl
      (TT: tree_config code (tree,GroupMap.reset gidl gm,inp) (pc+1,GroupMap.reset gidl gm,b,inp))
      (RESET: get_pc code pc = Some (ResetRegs gidl)),
      tree_config code (GroupAction (Reset gidl) tree, gm, inp) (pc,gm,b,inp)
  | tc_begin:
    forall inp tree gm pc b
      (TT: tree_config code (tree,gm,inp) (pc+1,gm,CannotExit,inp))
      (BEGIN: get_pc code pc = Some BeginLoop),
      tree_config code (tree,gm,inp) (pc,gm,b,inp).
  
  
  (* the initial active config and the initial active tree are related with the invariant *)
  Lemma initial_tree_thread:
    forall r code tree inp
      (COMPILE: compilation r = code)
      (TREE: bool_tree rer [Areg r] inp CanExit tree)
      (SUBSET: pike_regex r),
      tree_config code (tree, GroupMap.empty,inp) (0, GroupMap.empty, CanExit,inp).
  Proof.
    intros r code tree inp COMPILE TREE SUBSET.
    unfold compilation in COMPILE. destruct (compile r 0) as [c fresh] eqn:COMP.
    apply compile_nfa_rep with (prev := []) in COMP as REP; auto. simpl in REP.
    apply fresh_correct in COMP. simpl in COMP. subst.
    subst. eapply tc_eq; eauto.
    2: { repeat (constructor; auto). }
    apply cons_bc with (pcmid := length c).
    - constructor. apply nfa_rep_extend. auto.
    - constructor. replace (length c) with (length c + 0) by auto. rewrite get_prefix. auto.
  Qed.


  (* lifting the equivalence predicate to lists *)
  Inductive list_tree_config (code:code) : list (tree * group_map * input) -> list config -> Prop :=
  | ltc_nil: list_tree_config code [] []
  | ltc_cons:
    forall inp treelist threadlist tree gm pc b
      (LTC: list_tree_config code treelist threadlist)
      (TT: tree_config code (tree, gm, inp) (pc, gm, b, inp)),
      list_tree_config code ((tree,gm,inp)::treelist) ((pc,gm,b,inp)::threadlist).
  
  Lemma ltc_app:
    forall code tl1 tl2 vl1 vl2
      (LTT1: list_tree_config code tl1 vl1)
      (LTT2: list_tree_config code tl2 vl2),
      list_tree_config code (tl1 ++ tl2) (vl1 ++ vl2).
  Proof.
    intros. induction LTT1; auto. simpl. econstructor; eauto.
  Qed.

  (* This is not, strictly speaking, an inclusion, which explains the second case of this disjunction *)
  (* Sometimes, we add seen pcs on the MemoBT side that do not correspond yet to any seen tree on the MemoTree side *)
  (* this happens during stuttering steps: such pcs are always stuttering, equivalent to the current active tree, *)
  (* but these pcs are not equal to the current pc : they're smaller *)
  (* the relation is then indexed by the current pc *)
  Definition seen_inclusion (c:code) (treeseen:seentrees) (memoset:memoset) (current:option (tree*group_map*input)) (currentpc:label): Prop :=
    forall pc b inp
      (SEEN: is_memo memoset pc b inp = true),
      (exists t gm,
          inseen treeseen t = true /\
            tree_config c (t, gm, inp) (pc, gm, b, inp))
      \/
        (stutters pc c = true /\
           exists t gm, pc < currentpc /\ current = Some (t,gm,inp) /\
                     tree_config c (t,gm,inp) (pc,gm,b,inp)).
  
  Definition head_pc (stk:list config) : label :=
    match stk with
    | [] => 0
    | (pc,_,_,_)::_ => pc
    end.

  (* Simulation Invariant *)
  Inductive memo_inv (code:code): mtree_state -> mbt_state -> Prop :=
  | memoinv:
    forall treestk treeseen stk memoset
      (STACK: list_tree_config code treestk stk)
      (SEEN: seen_inclusion code treeseen memoset (hd_error treestk) (head_pc stk)),
      memo_inv code (MTree treestk treeseen) (MBT stk memoset)
  | memoinv_final:
    forall result,
      memo_inv code (MTree_final result) (MBT_final result).

  Theorem invariant_preservation:
  forall code mts1 mbs1 mbs2
    (STWF: stutter_wf rer code)
    (INV: memo_inv code mts1 mbs1)
    (MEMOSTEP: memobt_step rer code mbs1 mbs2),
    (* either we make a step on both sides, preserving invariant *)
    (
      exists mts2,
        memotree_step mts1 mts2 /\
          memo_inv code mts2 mbs2
    )
    \/
      (* or we make a stuttering step, preserving invariant with mts1 *)
      (
          memo_inv code mts1 mbs2
      ).
  Proof.
  Admitted.

End MemoEquiv.
