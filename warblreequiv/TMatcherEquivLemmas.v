From Linden Require Import TMatcherEquivDef TreeMSInterp Tree LindenParameters.
From Warblre Require Import Result Notation Base Errors Parameters.
Import Notation.
Import Result.Notations.

Local Open Scope result_flow.

Lemma equiv_choice:
  forall (ms: MatchState) (gl: open_groups) resopt1 topt1 resopt2 topt2,
    equiv_results topt1 ms gl resopt1 -> equiv_results topt2 ms gl resopt2 ->
    equiv_results (
        let! z =<< topt1 in
        let! z' =<< topt2 in
        Success (Choice z z')
      ) ms gl (
        let! z =<< resopt1 in
        if (z !=? None)%wt then
          Success z
        else
          resopt2
      ).
Proof.
  intros ms gl resopt1 topt1 resopt2 topt2 Hequiv1 Hequiv2.
  inversion Hequiv1 as [ t1 ms' gl' res1 Hequiv1' Heqt1 Heqms' Heqgl' Heqres1 |
                       | ].
  2,3: constructor.
  subst ms' gl'.
  inversion Hequiv2 as [ t2 ms' gl' res2 Hequiv2' Heqt2 Heqms' Heqgl' Heqres2 |
                       | ]; simpl.
  - replace (if (res1 !=? None)%wt then _ else _)
      with (Success (F := MatchError) (if (res1 !=? None)%wt then res1 else res2
           )) by now destruct res1.
    constructor.
    simpl.
    rewrite <- Hequiv1'.
    rewrite <- Hequiv2'.
    now destruct res1.
  - constructor.
  - (* Something is happening here; may be simplified later *)
    destruct res1; simpl. 2: constructor.
    destruct topt2.
    + simpl. constructor. simpl. rewrite <- Hequiv1'. reflexivity.
    + constructor.
Qed.

Lemma func_monad_swap {F} `{Result.AssertionError F}:
  forall topt1 topt2 (f1 f2: tree -> tree),
    (let! t1 =<< topt1 in
     let! t2 =<< topt2 in
     Success (F := F) (Choice (f1 t1) (f2 t2))
    ) = (
          let! t1 =<<
               let! t1 =<< topt1 in
               Success (F := F) (f1 t1)
          in
          let! t2 =<<
               let! t2 =<< topt2 in
               Success (F := F) (f2 t2)
          in
          Success (F := F) (Choice t1 t2)
        ).
Proof.
  intros topt1 topt2 f1 f2.
  destruct topt1; destruct topt2; simpl; reflexivity.
Qed.

Lemma monad_id {T F} `{Result.AssertionError F}:
  forall res: Result T F,
    (let! x =<< res in Success x) = res.
Proof.
  intro res.
  now destruct res.
Qed.
