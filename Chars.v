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
