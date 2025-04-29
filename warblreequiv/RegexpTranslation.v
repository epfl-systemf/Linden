From Warblre Require Import Patterns Result Errors Coercions Notation Base.
From Linden Require Import Regex LindenParameters Chars.
Import Notation.
Import Result.
Import Result.Notations.
Local Open Scope result_flow.

(** * Relation defining equivalence between Warblre regexes and Linden regexes *)

(* Computes the number of capture groups of the regex r. *)
Fixpoint num_groups (r: regex): nat := (* actually len (def_groups r); TODO replace later or prove lemma *)
  match r with
  | Epsilon | Character _ => 0
  | Disjunction r1 r2 => num_groups r1 + num_groups r2
  | Sequence r1 r2 => num_groups r1 + num_groups r2
  | Quantified _ _ _ r1 => num_groups r1
  | Group _ r1 => S (num_groups r1)
  | Lookaround _ r1 => num_groups r1
  end.

(* Equivalence of greedy/lazy quantifier prefixes. *)
Inductive equiv_greedylazy: (Patterns.QuantifierPrefix -> Patterns.Quantifier) -> bool -> Prop :=
| Equiv_greedy: equiv_greedylazy Patterns.Greedy true
| Equiv_lazy: equiv_greedylazy Patterns.Lazy false.

(* Equivalence of quantifiers. *)
Inductive equiv_quantifier: Patterns.QuantifierPrefix -> (bool -> regex -> regex) -> Prop :=
| Equiv_star: equiv_quantifier Patterns.Star (fun greedy => Quantified greedy 0 +∞)
| Equiv_plus: equiv_quantifier Patterns.Plus (fun greedy => Quantified greedy 1 +∞)
| Equiv_question: equiv_quantifier Patterns.Question (fun greedy => Quantified greedy 0 (NoI.N 1))
| Equiv_repexact: forall n, equiv_quantifier (Patterns.RepExact n) (fun greedy => Quantified greedy n (NoI.N 0))
| Equiv_reppartialrange: forall n, equiv_quantifier (Patterns.RepPartialRange n) (fun greedy => Quantified greedy n +∞)
| Equiv_reprange: forall mini maxi, mini <= maxi -> equiv_quantifier (Patterns.RepRange mini maxi) (fun greedy => Quantified greedy mini (NoI.N (maxi-mini))).

(* Equivalence of lookaheads. *)
Inductive equiv_lookahead: (Patterns.Regex -> Patterns.Regex) -> lookaround -> Prop :=
| Equiv_lookahead: equiv_lookahead Patterns.Lookahead LookAhead
| Equiv_neglookahead: equiv_lookahead Patterns.NegativeLookahead NegLookAhead.
(* TODO Lookbehinds *)

(* equiv_regex' wreg lreg n means that the two regexes wreg and lreg are equivalent, where the number of left capturing parentheses before wreg/lreg is n. *)
Inductive equiv_regex': Patterns.Regex -> regex -> nat -> Prop :=
| Equiv_empty: forall n: nat, equiv_regex' Patterns.Empty Epsilon n
| Equiv_char: forall (n: nat) (c: Char), equiv_regex' (Patterns.Char c) (Character (Chars.single c)) n
(* Dot is not axiomatized for now in Linden.
| Equiv_dot: forall n: nat, equiv_regex' Patterns.Dot (Character Chars.dot) n *)
| Equiv_disj: forall n wr1 wr2 lr1 lr2,
    equiv_regex' wr1 lr1 n -> equiv_regex' wr2 lr2 (num_groups lr1 + n) ->
    equiv_regex' (Patterns.Disjunction wr1 wr2) (Disjunction lr1 lr2) n
| Equiv_seq: forall n wr1 wr2 lr1 lr2,
    equiv_regex' wr1 lr1 n -> equiv_regex' wr2 lr2 (num_groups lr1 + n) ->
    equiv_regex' (Patterns.Seq wr1 wr2) (Sequence lr1 lr2) n
| Equiv_quant:
  forall n wr lr wquant lquant wgreedylazy greedy,
    equiv_regex' wr lr n ->
    equiv_quantifier wquant lquant -> equiv_greedylazy wgreedylazy greedy ->
    equiv_regex' (Patterns.Quantified wr (wgreedylazy wquant)) (lquant greedy lr) n
| Equiv_group: forall name n wr lr, equiv_regex' wr lr (S n) -> equiv_regex' (Patterns.Group name wr) (Group (S n) lr) n
| Equiv_lk: forall n wr lr wlk llk, equiv_regex' wr lr n -> equiv_lookahead wlk llk -> equiv_regex' (wlk wr) (Lookaround llk lr) n.


(* Equivalence of root regexes. *)
Definition equiv_regex (wreg: Patterns.Regex) (lreg: regex) := equiv_regex' wreg lreg 0.
