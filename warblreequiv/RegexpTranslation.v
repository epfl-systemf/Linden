From Warblre Require Import Patterns Result Errors Coercions Notation Base.
From Linden Require Import Regex CharsWarblre LindenParameters Chars.
Import Notation.
Import Result.
Import Result.Notations.
Local Open Scope result_flow.

Fixpoint to_warblre_regex (r: regex): Result Patterns.Regex CompileError :=
  match r with
  | Epsilon => Success Patterns.Empty
  | Character cd => char_descr_to_regex cd
  | Disjunction r1 r2 =>
    let! wr1 =<< to_warblre_regex r1 in
    let! wr2 =<< to_warblre_regex r2 in
    Success (Patterns.Disjunction wr1 wr2)
  | Sequence r1 r2 =>
    let! wr1 =<< to_warblre_regex r1 in
    let! wr2 =<< to_warblre_regex r2 in
    Success (Patterns.Seq wr1 wr2)
  | Star greedy r1 =>
    let! wr1 =<< to_warblre_regex r1 in
    Success (Patterns.Quantified wr1 (if greedy then Patterns.Greedy Patterns.Star else Patterns.Lazy Patterns.Star))
  | Group id r =>
    let! wr =<< to_warblre_regex r in
    Success (Patterns.Group None wr)
  end.

(* Ensuring that the group IDs of the translation correspond to those of the original regexp *)
Fixpoint num_groups (r: regex): nat :=
  match r with
  | Epsilon | Character _ => 0
  | Disjunction r1 r2 => num_groups r1 + num_groups r2
  | Sequence r1 r2 => num_groups r1 + num_groups r2
  | Star _ r1 => num_groups r1
  | Group _ r1 => S (num_groups r1)
  end.

Inductive well_parenthesized' : nat -> regex -> Prop :=
| wp_eps: forall n, well_parenthesized' n Epsilon
| wp_char: forall n cd, well_parenthesized' n (Character cd)
| wp_disj: forall n r1 r2, well_parenthesized' n r1 -> well_parenthesized' (num_groups r1 + n) r2 -> well_parenthesized' n (Disjunction r1 r2)
| wp_seq: forall n r1 r2, well_parenthesized' n r1 -> well_parenthesized' (num_groups r1 + n) r2 -> well_parenthesized' n (Sequence r1 r2)
| wp_star: forall n greedy r, well_parenthesized' n r -> well_parenthesized' n (Star greedy r)
| wp_group: forall n r, well_parenthesized' (S n) r -> well_parenthesized' n (Group (S n) r).

Definition well_parenthesized (r: regex) := well_parenthesized' 0 r.


Inductive equiv_regex: Patterns.Regex -> regex -> Prop :=
| Equiv_empty: equiv_regex Patterns.Empty Epsilon
| Equiv_char: forall c: Char, equiv_regex (Patterns.Char c) (Character (Chars.single c))
| Equiv_dot: equiv_regex Patterns.Dot (Character Chars.dot)
| Equiv_disj: forall wr1 wr2 r1 r2, equiv_regex wr1 r1 -> equiv_regex wr2 r2 -> equiv_regex (Patterns.Disjunction wr1 wr2) (Disjunction r1 r2)
| Equiv_seq: forall wr1 wr2 r1 r2, equiv_regex wr1 r1 -> equiv_regex wr2 r2 -> equiv_regex (Patterns.Seq wr1 wr2) (Sequence r1 r2)
| Equiv_star_lazy: forall wr r, equiv_regex wr r -> equiv_regex (Patterns.Quantified wr (Patterns.Lazy Patterns.Star)) (Star false r)
| Equiv_star_greedy: forall wr r, equiv_regex wr r -> equiv_regex (Patterns.Quantified wr (Patterns.Greedy Patterns.Star)) (Star true r)
| Equiv_group: forall name wr gid r, equiv_regex wr r -> equiv_regex (Patterns.Group name wr) (Group gid r).