(* Defining Capture Groups Registers *)
(* Keeping an index of when was a group opened and closed *)

Require Import List Lia.
Import ListNotations.


From Linden Require Import Chars.

Definition group_id : Type := nat.

(* Storing the values of each group and a function indicating if each group is opened or closed *)
Parameter group_map: Type.
Parameter empty_group_map : group_map.

Parameter open_group: group_map -> group_id -> nat -> group_map.
Parameter close_group: group_map -> group_id -> nat -> group_map.
Parameter reset_group: group_map -> group_id -> group_map.

Definition reset_groups (g:group_map) (idl:list group_id) : group_map :=
  List.fold_left reset_group idl g.

Parameter get_begin : group_map -> group_id -> option nat.
Parameter get_end : group_map -> group_id -> option nat.


(** * Axiomatisation  *)

Axiom empty_none_begin:
  forall gid, get_begin empty_group_map gid = None.

Axiom empty_none_end:
  forall gid, get_end empty_group_map gid = None.

Axiom group_open_begin:
  forall gid idx gm, get_begin (open_group gm gid idx) gid = Some idx.

Axiom group_close_end:
  forall gid idx gm, get_end (close_group gm gid idx) gid = Some idx.

Axiom get_reset_begin:
  forall gid gm, get_begin (reset_group gm gid) gid = None.

Axiom get_reset_end:
  forall gid gm, get_end (reset_group gm gid) gid = None.

Axiom get_other_begin_open:
  forall gid1 gid2 gm idx,
    gid1 <> gid2 ->
    get_begin (open_group gm gid1 idx) gid2 = get_begin gm gid2.
(* TODO: and so many more like this *)
