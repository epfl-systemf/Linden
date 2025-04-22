From Linden Require Import RegexpTranslation LindenParameters.
From Warblre Require Import StaticSemantics.
From Coq Require Import Lia.

Lemma num_groups_equiv:
  forall wreg lreg n,
    equiv_regex' wreg lreg n ->
    num_groups lreg = countLeftCapturingParensWithin_impl wreg.
Proof.
  intros wreg lreg n Hequiv.
  induction Hequiv as [
    n |
    n c |
    n |
    n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
    n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
    n wr lr wquant lquant wgreedylazy greedy Hequiv IH Hequivquant Hequivgreedy |
    name n wr lr Hequiv IH
    ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. lia.
  - simpl. lia.
  - inversion Hequivquant; inversion Hequivgreedy; simpl; assumption.
  - simpl. f_equal. assumption.
Qed.
