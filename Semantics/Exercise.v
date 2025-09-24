Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree.
From Warblre Require Import Numeric Base RegExpRecord.
From Linden Require Import Semantics FunctionalSemantics.
From Linden Require Import Parameters LWParameters.

Section Exercise.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (* In this exercise, we will prove that the regexes
     ε, εε, εεε, εεεε... all behave the same way.
     To do so, we will prove that for any input, their backtracking trees
     (as defined in Figure 4) are all the same: a single Match node.
     For this exercise, we expect basic familiarity with a Rocq editor
     (writing and stepping through a proof).
   *)

  (* First, we define such sequences of ε with the following function *)
  Fixpoint n_epsilon (n:nat) : regex :=
    match n with
    | 0 => Epsilon
    | S m => Sequence Epsilon (n_epsilon m)
    end.

  (* We can check that this function computes these ε sequences *)
  Eval cbn in (n_epsilon 0).
  Eval cbn in (n_epsilon 3).
  Eval cbn in (n_epsilon 10).

  (* Now, we prove that for any input `inp` and any `n`,
     the backtracking tree of the nth ε-sequence for `inp` is a `Match` tree. *)
  Theorem n_epsilon_tree:
    forall n inp,
      is_tree rer [Areg (n_epsilon n)] inp GroupMap.empty forward Match.
  Proof.
    (* Solve this exercise by replacing the `admit.` with tactics that solve the current goal.
       When you're done, you can replace the final `Admitted.' with a `Qed.` ! *)
        
    (* First, we introduce all our variables *)
    intros n inp.
    (* We then proceed by induction over `n` *)
    induction n; simpl.
    -
      (*
        In the base case (n = 0), our regex is a single ε.
        We would like to use rule EPSILON of Figure 4, followed
        by rule MATCH of Figure 4.

        These rules have slightly different names in the Rocq development,
        to find them, you can look at the `is_tree` definition in `Semantics/Semantics.v`.
        To apply a rule, you can simply use the proof tactic
        `apply rulename.`
        For instance, you could use `apply tree_group.` to apply the GROUP rule of Fig 4.
       *)
      admit.
    -
      (*
        In the recursive case, our regex is a sequence.
        We would like to use the SEQFORWARD rule.
        After that, we will likely need to use the EPSILON rule again,
        as well as our Induction hypothesis, `IHn`.
       *)
      admit.
  Admitted.


(* Solution:
   If you are stuck, below  is a base64-encoded string of the solution:

UHJvb2YuDQppbnRyb3MgbiBpbnAuDQppbmR1Y3Rpb24gbjsgc2ltcGwuDQotIGFwcGx5IHRyZWVfZXBzaWxvbi4NCiAgYXBwbHkgdHJlZV9kb25lLiAgICAgIA0KLSBhcHBseSB0cmVlX3NlcXVlbmNlLg0KICBhcHBseSB0cmVlX2Vwc2lsb24uDQogIGFwcGx5IElIbi4NClFlZC4NCg==

You can decode it by pasting it in a decoder, like https://www.base64decode.net/ 
 *)
  
End Exercise.
