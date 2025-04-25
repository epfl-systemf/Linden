From Warblre Require Import Semantics Frontend Result Errors Base.
From Linden Require Import LindenParameters RegexpTranslation Regex Chars Tree Groups Semantics Utils.
From Coq Require Import List.
Import ListNotations.
Import Result.
Import Result.Notations.
Import Coercions.

Local Open Scope result_flow.

(** * Frontend equivalence theorem *)

Definition equiv_flags: RegExpFlags := {|
  RegExpFlags.d := true;
  RegExpFlags.g := false;
  RegExpFlags.i := false;
  RegExpFlags.m := false;
  RegExpFlags.s := false;
  RegExpFlags.u := tt;
  RegExpFlags.y := true
  |}.
