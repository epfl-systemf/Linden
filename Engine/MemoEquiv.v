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

  Lemma tc_same_tree:
    forall code inp t1 gm1 t2 gm2 pc b
      (TC1: tree_config code (t1,gm1,inp) (pc,gm1,b,inp))
      (TC2: tree_config code (t2,gm2,inp) (pc,gm2,b,inp)),
      t1 = t2.
  Proof.
    intros code inp t1 gm1 t2 gm2 pc b TC1 TC2.
  Admitted.

  
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

  Lemma skip_inclusion:
    forall code inp treeseen memoset tree gm currentpc
      (INCL: seen_inclusion code treeseen memoset (Some (tree, gm, inp)) currentpc)
      (SEEN: inseen treeseen tree = true),
    forall current nextpc,
      seen_inclusion code treeseen memoset current nextpc.
  Proof.
    intros code inp treeseen threadseen tree gm currentpc INCL SEEN current nextpc.
    unfold seen_inclusion in *.
    intros pc b inp0 SEENPC.
    specialize (INCL pc b inp0 SEENPC).
    destruct INCL as [[ts [gms [SEENs TTs]]] | [ST [ts [gms [GEQ [EQ TTS]]]]]].
    - left. exists ts. exists gms. split; auto.
    - left. exists ts. exists gms. split; auto. inversion EQ. subst. auto.
  Qed.

  
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
      (INCL: seen_inclusion code treeseen memoset (hd_error treestk) (head_pc stk)),
      memo_inv code (MTree treestk treeseen) (MBT stk memoset)
  | memoinv_final:
    forall result,
      memo_inv code (MTree_final result) (MBT_final result).


  (* identifying states of MemoBT that are going to take a skip step *)
  Definition skip_state (mbs:mbt_state) : bool :=
    match mbs with
    | MBT_final _ => false
    | MBT stk memoset =>
        match stk with
        | [] => false
        | (pc,gm,b,inp)::stk => is_memo memoset pc b inp
        end
    end.

  (* fixme: this resembles generate_match from PikeEquiv.
     what should be the general version? *)
  Lemma exec_match:
    forall t pc gm b inp code leaf,
      exec_tree (t, gm, inp) = TMatch leaf ->
      tree_config code (t, gm, inp) (pc, gm, b, inp) ->
      stutters pc code = false ->
      exec_instr rer code (pc, gm, b, inp) = FoundMatch leaf.
  Proof.
    intros t pc gm b inp code leaf TREESTEP TC NOSTUTTER.
    unfold exec_tree in TREESTEP. destruct t; inversion TREESTEP; subst. clear TREESTEP.
    inversion TC; subst; try no_stutter.
    remember Match as TMATCH.
    (* here we have to proceed by induction because there are many ways to get a Match tree *)
    (* it could be epsilon, it could be epsilon followed by epsilon etc *)
    induction TREE; intros; subst; try inversion HeqTMATCH.
    - simpl. invert_rep. rewrite ACCEPT. auto.
    - repeat invert_rep. apply IHTREE; auto. pike_subset.
    - repeat invert_rep. apply IHTREE; auto.
      repeat (econstructor; eauto). pike_subset.
    - repeat invert_rep. apply IHTREE; auto. pike_subset.
    - destruct greedy; inversion CHOICE.
  Qed.
    
  
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
    intros code mts1 mbs1 mbs2 STWF INV MEMOSTEP.
    inversion INV; subst.
    (* Final states make no step *)
    2: { inversion MEMOSTEP. }
    destruct (skip_state (MBT stk memoset)) eqn:SKIP.
    (* skip steps are performed in lockstep *)
    { left. destruct stk as [|[[[pc gm] b] inp] stk]; simpl in SKIP, INCL.
      { inversion SKIP. }
      inversion MEMOSTEP; try (rewrite UNSEEN in SKIP; inversion SKIP); subst.
      inversion STACK; subst.
      apply INCL in SKIP as [[teq [gmeq [SEENEQ TTEQ]]] | [STUTTER [t' [gm' [GEQ [EQ TTS]]]]]].
      2: { lia. }
      assert (teq = tree); subst.
      { eapply tc_same_tree; eauto. }
      exists (MTree treelist treeseen). split; constructor; auto.
      eapply skip_inclusion; eauto.
    }
    destruct treestk as [|[[t gm] inp] treestk].
    (* no more active trees or configs: no match found *)
    { inversion STACK. subst.
      left. inversion MEMOSTEP. subst. exists (MTree_final None). split; constructor; auto.
    }
    (* there is an active tree/config *)
    destruct stk as [|[[[pc gm'] b] inp'] stk]; inversion STACK; subst.
    rename gm' into gm. rename inp' into inp.
    destruct (stutters pc code) eqn:STUTTERS.
    (* Stuttering step *)
    { admit. }
    left. simpl in SKIP. destruct (exec_tree (t, gm, inp)) eqn:EXEC.
    (* Match is found *)
    { eapply exec_match in EXEC as EXEC_INSTR; eauto.
      assert (mbs2 = MBT_final (Some l)); subst.
      { eapply memobt_deterministic; eauto. constructor; auto. }
      exists (MTree_final (Some l)). split; constructor; auto.
      }
    (* We keep exploring *)
    admit.
  Admitted.
      
      

    


End MemoEquiv.
