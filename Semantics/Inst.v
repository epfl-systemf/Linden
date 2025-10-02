From Warblre Require Import Inst API Parameters RegExpRecord.
Import NaiveEngine.
From Linden Require Import Parameters.

Instance character_class: Character.class := @Parameters.character_class parameters.

Lemma canonicalize_casesenst: forall rer chr, RegExpRecord.ignoreCase rer = false -> Character.canonicalize rer chr = chr.
Proof.
  intros rer chr Hcasesenst.
  unfold Character.canonicalize, character_class, Parameters.character_class, parameters, NaiveEngineParameters.Character.canonicalize.
  rewrite Hcasesenst. reflexivity.
Qed.

Instance naive_params: LindenParameters := make
    (@Parameters.character_class parameters)
    (@Parameters.unicode_property_class parameters)
    (@Parameters.set_class parameters)
    canonicalize_casesenst.
