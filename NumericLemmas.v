From Warblre Require Import Numeric.


(* The plus one operation is injective *)
Lemma plus_one_inj:
  forall (n m: non_neg_integer_or_inf),
    (NoI.N 1 + n)%NoI = (NoI.N 1 + m)%NoI -> n = m.
Proof.
  intros n m Heq.
  destruct n; destruct m; simpl in *; try discriminate; auto.
  now injection Heq as ->.
Qed.
