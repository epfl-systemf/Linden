From Warblre Require Import Patterns Result Errors Coercions Notation Base.
From Linden Require Import Regex CharsWarblre LindenParameters Chars.
Import Notation.
Import Result.
Import Result.Notations.
Local Open Scope result_flow.

(*Fixpoint to_warblre_regex (r: regex): Result Patterns.Regex CompileError :=
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
  end.*)

(* Ensuring that the group IDs of the translation correspond to those of the original regexp *)
Fixpoint num_groups (r: regex): nat :=
  match r with
  | Epsilon | Character _ => 0
  | Disjunction r1 r2 => num_groups r1 + num_groups r2
  | Sequence r1 r2 => num_groups r1 + num_groups r2
  | Star _ r1 => num_groups r1
  | Group _ r1 => S (num_groups r1)
  end.


(* equiv_regex' wreg lreg n means that the two regexes wreg and lreg are equivalent, where the number of parentheses before wreg/lreg is n *)
Inductive equiv_regex': Patterns.Regex -> regex -> nat -> Prop :=
| Equiv_empty: forall n: nat, equiv_regex' Patterns.Empty Epsilon n
| Equiv_char: forall (n: nat) (c: Char), equiv_regex' (Patterns.Char c) (Character (Chars.single c)) n
| Equiv_dot: forall n: nat, equiv_regex' Patterns.Dot (Character Chars.dot) n
| Equiv_disj: forall n wr1 wr2 lr1 lr2,
    equiv_regex' wr1 lr1 n -> equiv_regex' wr2 lr2 (num_groups lr1 + n) ->
    equiv_regex' (Patterns.Disjunction wr1 wr2) (Disjunction lr1 lr2) n
| Equiv_seq: forall n wr1 wr2 lr1 lr2,
    equiv_regex' wr1 lr1 n -> equiv_regex' wr2 lr2 (num_groups lr1 + n) ->
    equiv_regex' (Patterns.Seq wr1 wr2) (Sequence lr1 lr2) n
| Equiv_star_lazy: forall n wr lr, equiv_regex' wr lr n -> equiv_regex' (Patterns.Quantified wr (Patterns.Lazy Patterns.Star)) (Star false lr) n
| Equiv_star_greedy: forall n wr lr, equiv_regex' wr lr n -> equiv_regex' (Patterns.Quantified wr (Patterns.Greedy Patterns.Star)) (Star true lr) n
| Equiv_group: forall name n wr lr, equiv_regex' wr lr (S n) -> equiv_regex' (Patterns.Group name wr) (Group (S n) lr) n.

Definition equiv_regex (wreg: Patterns.Regex) (lreg: regex) := equiv_regex' wreg lreg 0.