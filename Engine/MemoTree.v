(** * MemoTree algorithm  *)
(* A backtracking algorithm, with memoization, on trees *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import Parameters SeenSets.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import MemoBT PikeTree.


Section MemoTree.
  Context {params: LindenParameters}.
  Context {TS: TSeen params}.

  (* configurations to be explored by the memoized backtracking engine *)
  Definition tree_config: Type := tree * group_map * input.
  Definition tree_stack: Type := list tree_config.
  
  (* states of the MemoBT algorithm *)
  Inductive mtree_state : Type :=
  | MTree (stk:tree_stack) (ts: seentrees): mtree_state
  | MTree_final (res:option leaf) : mtree_state.

  Definition initial_tree_state (t:tree) (i:input) : mtree_state :=
    MTree [(t, GroupMap.empty, i)] initial_seentrees.

  (** * MemoTree small-step semantics *)

  Inductive exec_tree_result : Type :=
  | TMatch: leaf -> exec_tree_result
  | TExplore: list tree_config -> exec_tree_result.

  Definition TDead : exec_tree_result := TExplore [].

  (* computes the next trees in a depth-first seach order *)
  Definition exec_tree (tc:tree_config) : exec_tree_result :=
    match tc with
    | (t, gm, i) =>
        match t with
        | Mismatch | ReadBackRef _ _ | LK _ _ _ | LKFail _ _ => TDead
        | Match => TMatch (i, gm)
        | Choice t1 t2 => TExplore [(t1,gm,i);(t2,gm,i)]
        | Read _ t1 => TExplore [(t1,gm,next_inp i)]
        | Progress t1 | AnchorPass _ t1 => TExplore [(t1,gm,i)]
        | GroupAction a t1 => TExplore [(t1,GroupMap.update (idx i) a gm, i)]
        end
    end.


  Inductive memotree_step: mtree_state -> mtree_state -> Prop :=
  (* we exhausted all configurations, there is no match *)
  | mtree_nomatch: forall ts,
      memotree_step (MTree [] ts) (MTree_final None)
  (* the memoization allows to skip the current configuration *)
  | mtree_skip:
    forall ts t gm i stk
      (SEEN: inseen ts t = true),
      memotree_step (MTree ((t,gm,i)::stk) ts) (MTree stk ts)
  (* a match is found, we discard the stack *)
  | mtree_match:
    forall ts t gm i leaf stk
      (MATCH: exec_tree (t,gm,i) = TMatch leaf),
      memotree_step (MTree ((t,gm,i)::stk) ts) (MTree_final (Some leaf))
  (* we keep exploring, and add each handled tree to the treeseen set *)
  | mtree_explore:
    forall ts t gm i nextconfs stk
      (EXPLORE: exec_tree (t,gm,i) = TExplore nextconfs),
      memotree_step (MTree ((t,gm,i)::stk) ts) (MTree (nextconfs++stk) (add_seentrees ts t)).
  
  (** * MemoTree properties  *)

  Theorem memotree_progress:
    forall stk ts,
    exists ms, memotree_step (MTree stk ts) ms.
  Proof.
    intros stk ts. destruct stk as [|[[t gm] i] stk].
    { eexists. econstructor. }
    destruct (exec_tree (t,gm,i)) eqn:EXEC.
    - eexists. eapply mtree_match. eauto.
    - eexists. eapply mtree_explore. eauto.
  Qed.

  (** * MemoTree Correctness  *)
  (* This algorithm always returns the leftmost accepting result of the initial tree *)
  
  
End MemoTree.
