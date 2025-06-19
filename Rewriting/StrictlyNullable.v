(** * Correctness of the STrictly Nullable Optimization *)
(* replacing r* with epsilon when r can only match the empty string *)

From Linden.Rewriting Require Import ProofSetup.

Section StrictlyNullable.
  Context {char: Parameters.Character.class}.

  (* The following function is a static under-approximation  of when is a regex striclty nullable. *)
  (* this definition is adapted from the warblre definition *)

Fixpoint strictly_nullable (r:regex) : bool :=
  match r with
  | Epsilon | Lookaround _ _ | Anchor _ => true
  | Character _ | Backreference _ => false
  | Disjunction r1 r2 | Sequence r1 r2 => andb (strictly_nullable r1) (strictly_nullable r2)
  | Quantified _ _ _ r1 | Group _ r1 => strictly_nullable r1
  end.

  Theorem strictly_nullable_correct:
    forall r, strictly_nullable r = true -> 
         Quantified true 0 NoI.Inf r ≅ Epsilon.
  Proof.
  Admitted.
End StrictlyNullable.
