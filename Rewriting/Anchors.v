From Linden.Rewriting Require Import ProofSetup.

Section Anchors.
  Context {params: LindenParameters}.

  Definition desugar_anchor (a: anchor) :=
    match a with
    | BeginInput =>
        Lookaround NegLookBehind (Character CdAll)
    | EndInput =>
        Lookaround NegLookAhead (Character CdAll)
    | WordBoundary =>
        Disjunction
          (Sequence
             (Lookaround NegLookBehind (Character CdWordChar))
             (Lookaround LookAhead (Character CdWordChar)))
          (Sequence
             (Lookaround LookBehind (Character CdWordChar))
             (Lookaround NegLookAhead (Character CdWordChar)))
    | NonWordBoundary =>
        Sequence
          (Disjunction
             (Lookaround LookBehind (Character CdWordChar))
             (Lookaround NegLookAhead (Character CdWordChar)))
          (Disjunction
             (Lookaround NegLookBehind (Character CdWordChar))
             (Lookaround LookAhead (Character CdWordChar)))
    end.

  Ltac destr :=
    repeat match goal with
      | _ => progress simpl
      | [  |- context[match ?x with _ => _ end] ] =>
          lazymatch x with
          | context[match _ with _ => _ end] => fail
          | _ => destruct x eqn:?
          end
      end; reflexivity.

  Theorem desugar_anchor_correct (a: anchor):
    Anchor a ≅ desugar_anchor a.
  Proof.
    destruct a; tree_equiv_rw.
    all: destruct dir; tree_equiv_symbex.
    all: reflexivity.
  Qed.
End Anchors.
