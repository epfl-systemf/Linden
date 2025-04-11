From Coq Require Import List.
Import ListNotations.

Fixpoint nth_opt {A: Type} (n: nat) (l: list A): option A :=
  match n, l with
  | _, nil => None
  | 0, x::_ => Some x
  | S n', _::q => nth_opt n' q
  end.