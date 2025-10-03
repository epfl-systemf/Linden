Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Groups Tree.
From Linden Require Import PikeSubset NFA BooleanSemantics.
From Linden Require Import Parameters.
From Warblre Require Import Base.


(** * Seen Sets of Trees  *)
(* The PikeTree algorithm needs to maintain a set of seen trees *)
(* Our definitions are parameterized by an inmplementation of such sets. *)

(* what we need from these sets is just these few definitions and properties *)
Class TSeen (params:LindenParameters) :=
  Tmake {
      seentrees: Type;
      initial_seentrees: seentrees;
      add_seentrees: seentrees -> tree -> seentrees;
      inseen : seentrees -> tree -> bool;
      (* Axiomatization of the seen set *)
      in_add: forall seen t1 t2,
        inseen (add_seentrees seen t2) t1 = true <->
          t1 = t2 \/ inseen seen t1 = true;
      initial_nothing: forall t,
        inseen initial_seentrees t = false;
    }.

(* one instanciation using lists, but you could use anything else *)
#[refine]
Instance TSlist (params:LindenParameters) : TSeen params :=
  { seentrees := list tree;
    
    initial_seentrees := [];
    
    add_seentrees (s:list tree) (t:tree) := t::s;
    
    inseen (s:list tree) (t:tree) :=
      List.existsb (fun x => tree_eqb x t) s;
  }.
(* in_add *)
- intros seen t1 t2. simpl. unfold tree_eqb. destruct (tree_eq_dec t2 t1) as [H1|H2];
    subst; split; intros; auto.
  destruct H as [Heq|Hin]; auto.
(* initial_nothing *)
- auto.
Defined.


(** * Sets of seen pcs *)

Class VMSeen :=
  Vmake {
      seenpcs: Type;
      initial_seenpcs: seenpcs;
      add_seenpcs: seenpcs -> label -> LoopBool -> seenpcs;
      inseenpc : seenpcs -> label -> LoopBool -> bool;
      (* Axiomatization of the seen set *)
      inpc_add: forall seen pc1 b1 pc2 b2,
        inseenpc (add_seenpcs seen pc2 b2) pc1 b1 = true <->
          ((pc1,b1) = (pc2,b2)) \/ inseenpc seen pc1 b1 = true;
      initial_nothing_pc: forall pc b,
        inseenpc initial_seenpcs pc b = false;
    }.

(* one instantiation using lists, but you could use anything else *)
Definition lblbool_eq_dec : forall (l1 l2 : (label*LoopBool)), { l1 = l2 } + { l1 <> l2 }.
Proof. repeat decide equality. Defined.
  
Definition lblbool_eqb l1 l2 : bool :=
  match lblbool_eq_dec l1 l2 with | left _ => true | _ => false end.
  
#[refine]
  Instance VMSlist : VMSeen :=
  { seenpcs := list (label * LoopBool);

    initial_seenpcs := [];

    add_seenpcs (s:list(label*LoopBool)) (l:label) (b:LoopBool) := (l,b)::s;

    inseenpc (s:list(label*LoopBool)) (l:label) (b:LoopBool) :=
      List.existsb (fun x => lblbool_eqb x (l,b)) s;
  }.
(* inpc_add *)
- intros seen pc1 b1 pc2 b2. simpl. unfold lblbool_eqb.
  destruct (lblbool_eq_dec (pc2,b2) (pc1,b1)) as [H1|H2];
      subst; split; intros; auto.
  destruct H as [Heq|Hin]; auto.
(* initial_nothing_pc *)
- auto.
Defined.
