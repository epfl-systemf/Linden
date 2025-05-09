From Warblre Require Import Parameters RegExpRecord.
Require Import List.
Import ListNotations.
Require Import Ascii.

(** * Instantiation of Character typeclass with Coq ASCII characters *)
(* This file remains unused for now *)

Definition all_ascii := List.map ascii_of_nat (List.seq 0 256).
Definition ascii_digits := (["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"])%char.
Definition ascii_whitespaces := ([" "; "009"; "010"])%char.
Parameter ascii_word_characters: list ascii.
Parameter ascii_canonicalize: RegExpRecord -> ascii -> ascii.

Definition ascii_of_nat_2 (n: nat): ascii :=
  if Nat.ltb n 256 then ascii_of_nat n else ascii_of_nat 255.

Lemma ascii_of_nat_2_lt256: forall n: nat, n < 256 -> ascii_of_nat_2 n = ascii_of_nat n.
Proof.
  intros n Hlt.
  unfold ascii_of_nat_2.
  rewrite <- PeanoNat.Nat.ltb_lt in Hlt.
  rewrite Hlt.
  reflexivity.
Qed.

#[refine] Instance ascii_Character: Character.class := {|
    Character.type := ascii;
    Character.from_numeric_value := ascii_of_nat_2;
    Character.numeric_value := nat_of_ascii;
    Character.canonicalize := ascii_canonicalize;
    
    Character.all := all_ascii;
    Character.line_terminators := ["010"%char];
    Character.digits := ascii_digits;
    Character.white_spaces := ascii_whitespaces;
    Character.ascii_word_characters := ascii_word_characters |}.
Proof.
  - constructor. apply ascii_dec.
  - intro c.
    transitivity (ascii_of_nat (nat_of_ascii c)).
    + apply ascii_of_nat_2_lt256. apply nat_ascii_bounded.
    + apply ascii_nat_embedding.
  - admit.
Admitted.

Transparent ascii_Character.

