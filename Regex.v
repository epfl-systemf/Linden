Require Import List Lia.
Import ListNotations.

(** * Characters and Strings  *)
Parameter Char:Type.
Definition string := list Char.

(* In the semantics, the input string is represented with both the next characters to read
   and the reversed list of previously read characters (in case we change direction for a lookbehind) *)
Inductive input : Type :=
| Input (next: string) (pref: string).

Parameter char_eq_dec : forall (x y : Char), { x = y } + { x <> y }.
Definition string_eq_dec : forall (x y : string), { x = y } + { x <> y }.
Proof.
  decide equality. apply char_eq_dec.
Defined.
Definition input_eq_dec: forall (i1 i2: input), { i1 = i2 } + { i1 <> i2 }.
Proof. decide equality; apply string_eq_dec. Defined.

(* indicating which character is a word character for anchors *)
Parameter word_char : Char -> bool.

(** * Character Descriptors  *)
(* by character descriptors, we mean everything that can represent a single character *)
(* the character itself, the dot, an escape, a character group like \d, character classes *)
Parameter char_descr : Type.

(* common character descriptors *)
Parameter dot : char_descr.
(* dot is not all characters without multiline flag *)
Parameter all: char_descr.
(* single char *)
Parameter single : Char -> char_descr.

Parameter char_match : Char -> char_descr -> bool.

Axiom single_match:
  forall c1 c2, char_match c1 (single c2) = true <-> c1 = c2.

Axiom all_match:
  forall c, char_match c all = true.

Parameter char_descr_eq_dec : forall (cd1 cd2: char_descr), { cd1 = cd2 } + { cd1 <> cd2 }.


(** * Reading Characters in the String *)

(* read_char cd i returns None if the next character of i is accepted by cd *)
(* otherwise it returns the next input after reading the character, as well as the character actually read *)
Definition read_char (cd:char_descr) (i:input) : option (Char * input) :=
  match i with
  | Input next pref =>
      match next with
      | [] => None
      | h::next' => if char_match h cd
                  then Some (h, Input next' (h::pref))
                  else None
      end
  end.


Definition next_str (i:input) : string :=
  match i with
  | Input s _ => s
  end.

Definition current_str (i:input) : string :=
  match i with
  | Input next pref => next
  end.

Definition init_input (str:string) : input :=
  Input str [].

 
(** * Regex Syntax  *)
Definition group_id : Type := nat.

Inductive regex : Type :=
| Epsilon 
| Character (cd : char_descr)   (* includes character classes and dot *)
| Disjunction (r1 r2 : regex) 
| Sequence (r1 r2 : regex)
| Star (r1: regex)
| Group (id : group_id) (r : regex).

Definition regex_eq_dec : forall (x y : regex), { x = y } + { x <> y }.
Proof.
  decide equality. apply char_descr_eq_dec. apply PeanoNat.Nat.eq_dec. 
Defined.

(** * Group Manipulation  *)

(* getting all groups defined in a regex for the reset *)
Fixpoint def_groups (r:regex) : list group_id :=
  match r with
  | Epsilon | Character _  => []
  | Sequence r1 r2 | Disjunction r1 r2 => def_groups r1 ++ def_groups r2
  | Star r1 => def_groups r1
  | Group id r1 => id::(def_groups r1)  
  end.

(* Storing the values of each group and a function indicating if each group is opened or closed *)
Definition group_map : Type :=
  (group_id -> option string) * (group_id -> bool).

Definition empty_group_map : group_map :=
  (fun _ => None, fun _ => false).

Definition open_group (g:group_map) (id:group_id) : group_map :=
  ((fun id2 => if (Nat.eqb id2 id) then Some [] else fst g id2),
    (fun id2 => if (Nat.eqb id2 id) then true else snd g id2)).

Definition close_group (g:group_map) (id:group_id) : group_map :=
  ((fst g),
    (fun id2 => if (Nat.eqb id2 id) then false else (snd g) id2)).

Definition add_char (g:group_map) (c:Char) : group_map :=
  ((fun id =>
      if snd g id then
        match fst g id with
        | None => Some [c]       (* None should never happen when the boolean is true *)
        | Some l  => Some (c::l)
        end
      else fst g id),
    snd g).

Definition reset_group (g:group_map) (id:group_id) : group_map :=
  ((fun id2 => if (Nat.eqb id2 id) then None else fst g id2),
    (* we could let snd g unchanged: when we reset, the groups should be closed *)
    (fun id2 => if (Nat.eqb id2 id) then false else snd g id2)).

Definition reset_groups (g:group_map) (idl:list group_id) : group_map :=
  List.fold_left reset_group idl g.

