(* Defining Capture Groups Registers *)
(* Keeping an index of when was a group opened and closed *)

Require Import List Lia.
Import ListNotations.
Require Import MSetList OrdersAlt PeanoNat FMapList.


From Linden Require Import Chars.

(** * Group Manipulation  *)

Module GroupId <: OrderedTypeWithLeibniz.
  Include Nat.
  Lemma eq_leibniz : forall x y, Nat.eq x y -> x = y. Proof. trivial. Qed.
End GroupId.
Definition group_id : Type := GroupId.t.

(** ** Group Sets *)

Definition group_set : Type := list group_id.

(** ** Group actions *)
(* The possible operations done on group maps during matching *)
Inductive groupaction : Type :=
| Open (g: group_id)
| Close (g: group_id)
| Reset (gl: group_set) (* for capture reset *)
.

(** ** Group Maps *)

(* Partial-Maps from group ids to captures *)
Module GroupMap.

  (* Capture groups are represented by their range in the matched string. *)
  (* The start and end indices are inclusive and exclusive respectively. *)
  (* A group is considered open when it has no end index, and closed o.w. *)
  Record range : Type := Range { startIdx : nat; endIdx : option nat }.

  Definition OpenRange (startIdx : nat) : range :=
    Range startIdx None.
  Definition CloseRange (endIdx : nat) '(Range startIdx _) : range :=
    Range startIdx (Some endIdx).

  Module MapS <: FMapInterface.S.
    Module GroupId' <: OrderedTypeOrig := OrdersAlt.Backport_OT GroupId.
    Include FMapList.Make GroupId'.
  End MapS.
  Definition t := MapS.t range.

  Definition empty : t := MapS.empty range.

  Definition find : group_id -> t -> option range := MapS.find (elt := range).

  Section ops.
    Variable currIdx : nat. (* The current index in the string being matched *)

    Definition open (gid : group_id) : t -> t :=
      MapS.add gid (Range currIdx None).

    (* Assumes, but does not check, the g is associated to an open range *)
    Definition close (gid : group_id) (gm : t) : t :=
      match find gid gm with
      | Some (Range startIdx _) => MapS.add gid (Range startIdx (Some currIdx)) gm
      | None => gm
      end.

    Definition reset : group_set -> t -> t :=
      List.fold_left (fun s gid => MapS.remove (elt := range) gid s).

    Definition update (op : groupaction) : t -> t :=
      match op with
      | Open g => open g
      | Close g => close g
      | Reset gs => reset gs
      end.

  End ops.

  Axiom eq_dec : forall gm1 gm2 : t, { gm1 = gm2 } + { gm1 <> gm2 }.
  (* used in state_eq_dec, which is used in equiv_matches *)
  (* to decide between applying equiv_matches_not_seen, or the others. *)

End GroupMap.
Definition group_map : Type := GroupMap.t.