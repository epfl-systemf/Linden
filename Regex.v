Require Import List Lia.
Import ListNotations.

(** * Direction  *)
(* the semantics can go through the string forward or backward (when inside lookbehinds) *)
Inductive direction : Type :=
| Forward
| Backward.

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

(* deprecated in favor of read_char *)
Definition next_char (i:input) (dir:direction) : option (Char * input) :=
  match i with
  | Input next pref =>
      match dir with
      | Forward =>
          match next with
          | [] => None
          | c::next' => Some (c, Input next' (c::pref))
          end
      | Backward =>
          match pref with
          | [] => None
          | c::pref' => Some (c, Input (c::next) pref')
          end
      end
  end.

(* read_char cd i d returns None if the next character of i with direction d is accepted by cd *)
(* otherwise it returns the next input after reading the character, as well as the character actually read *)
Definition read_char (cd:char_descr) (i:input) (dir:direction) : option (Char * input) :=
  match i with
  | Input next pref =>
      match dir with
      | Forward =>
          match next with
          | [] => None
          | h::next' => if char_match h cd
                      then Some (h, Input next' (h::pref))
                      else None
          end
      | Backward =>
          match pref with
          | [] => None
          | h::pref' => if char_match h cd
                      then Some (h, Input (h::next) pref')
                      else None
          end
      end
  end.

(* next_char_match c i1 d i2 means that the next character of i1 according to direction d matches c,
   and the next input after consuming that character is i2 *)
(* deprecated in favor of read_char *)
Inductive next_char_match: Char -> input -> direction -> input -> Prop :=
| next_forward:
  forall c next pref,
    next_char_match c (Input (c::next) pref) Forward (Input next (c::pref))
| next_backward:
  forall c next pref,
    next_char_match c (Input next (c::pref)) Backward (Input (c::next) pref).

Definition next_str (i:input) : string :=
  match i with
  | Input s _ => s
  end.

Definition current_str (i:input) (dir:direction) : string :=
  match i with
  | Input next pref =>
      match dir with
      | Forward => next
      | Backward => pref
      end
  end.

Definition init_input (str:string) : input :=
  Input str [].

(** * Lookarounds  *)
Inductive lookaround : Type :=
| LookAhead
| LookBehind
| NegLookAhead
| NegLookBehind.

Definition lk_dir (lk:lookaround) : direction :=
  match lk with
  | LookAhead | NegLookAhead => Forward
  | LookBehind | NegLookBehind => Backward
  end.

Definition positivity (lk:lookaround) : bool :=
  match lk with
  | LookAhead | LookBehind => true
  | NegLookAhead | NegLookBehind => false
  end.

(** * Anchors  *)
Inductive anchor : Type :=
| BeginInput
| EndInput
| WordBoundary
| NonWordBoundary.

Definition is_boundary (i:input) : bool :=
  match i with
  | Input next pref =>
      match next, pref with
      | [], [] => false
      | [], c::p' => word_char c
      | c::n', [] => word_char c
      | c1::n', c2::p' =>
          xorb (word_char c1) (word_char c2)
      end
  end.

(* independent of the direction *)
Definition anchor_satisfied (a:anchor) (i:input) : bool :=
  match i with
  | Input next pref =>
      match a with
      | BeginInput =>
          match pref with | [] => true | _ => false end
      | EndInput =>
          match next with | [] => true | _ => false end
      | WordBoundary =>
          is_boundary i
      | NonWordBoundary =>
          negb (is_boundary i)
      end
  end.


(** * Quantifiers  *)
Inductive nat_or_inf : Type :=
| Nat (n:nat) : nat_or_inf
| Infinity : nat_or_inf.

Inductive quantifier : Type :=
| Quant (min:nat) (max:nat_or_inf) (greedy: bool).

Lemma quant_eq_dec: forall (q1 q2:quantifier), { q1 = q2 } + { q1 <> q2 }.
Proof. intros. decide equality; decide equality; decide equality. Qed.

(* common quantifiers *)
Definition star : quantifier :=
  Quant 0 Infinity true.
Definition plus : quantifier :=
  Quant 1 Infinity true.
Definition qmark : quantifier :=
  Quant 0 (Nat 1) true.
Definition lazy_star : quantifier :=
  Quant 0 Infinity false.
Definition lazy_plus : quantifier :=
  Quant 1 Infinity false.
Definition lazy_qmark : quantifier :=
  Quant 0 (Nat 1) false.

(* quantifier after having done one iteration *)
Definition next_quant (q:quantifier) : quantifier :=
  match q with
  | Quant min max greedy =>
      match max with
      | Infinity => Quant (min-1) Infinity greedy
      | Nat max' => Quant (min-1) (Nat (max'-1)) greedy
      end
  end.

Inductive quant_status : Type :=
| Done                          (* no more iterations allowed *)
| Forced                        (* iteration is forced *)
| Free (greedy:bool).              (* one can either iterate or stop *)

Definition status (q:quantifier) : quant_status :=
  match q with
  | Quant min max greedy =>
      match max with
      | Nat 0 => Done
      | _ =>
          match min with
          | 0 => Free greedy
          | _ => Forced
          end
      end
  end.
 
(** * Regex Syntax  *)
Definition group_id : Type := nat.

Inductive regex : Type :=
| Epsilon 
| Character (cd : char_descr)   (* includes character classes and dot *)
| Disjunction (r1 r2 : regex) 
| Sequence (r1 r2 : regex)
| Quantifier (q:quantifier) (r1: regex)
| Group (id : group_id) (r : regex)
| Lookaround (lk : lookaround) (r : regex)
| Anchor (a:anchor).

Definition regex_eq_dec : forall (x y : regex), { x = y } + { x <> y }.
Proof.
  decide equality. apply char_descr_eq_dec. apply quant_eq_dec. apply PeanoNat.Nat.eq_dec. decide equality. decide equality.
Defined.

(** * Group Manipulation  *)

(* getting all groups defined in a regex for the reset *)
Fixpoint def_groups (r:regex) : list group_id :=
  match r with
  | Epsilon | Character _ | Anchor _ => []
  | Sequence r1 r2 | Disjunction r1 r2 => def_groups r1 ++ def_groups r2
  | Quantifier _ r1 | Lookaround _ r1 => def_groups r1
  | Group id r1 => id::(def_groups r1)  
  end.

(* Stroting the values of each group and a functio nindicating if each group is opened or closed *)
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

