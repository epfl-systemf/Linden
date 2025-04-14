From Warblre Require Import Semantics Frontend Result Errors Base.
From Linden Require Import LindenParameters RegexpTranslation Regex Chars Tree Groups Semantics Utils.
From Coq Require Import List.
Import ListNotations.
Import Result.
Import Result.Notations.
Import Coercions.

Local Open Scope result_flow.

(* TODO Fix this *)
Definition equiv_flags: RegExpFlags := {|
  RegExpFlags.d := true;
  RegExpFlags.g := false;
  RegExpFlags.i := false;
  RegExpFlags.m := false;
  RegExpFlags.s := false;
  RegExpFlags.u := tt;
  RegExpFlags.y := true
  |}.

Definition warblre_exec (r: regex) (s: string): Result (option ExecResult) CompileError :=
  let! warblre_r =<< to_warblre_regex r in
  match regExpInitialize (specParameters := LindenParameters) warblre_r equiv_flags with
  | Error _ => None
  | Success rei =>
    match regExpBuiltinExec rei s with
    | Error _ => None
    | Success res => Some res
    end
  end.

Definition group_maps_equal (li: list (option (nat*nat))) (l: option leaf) : Prop :=
  match l with
  | None => False
  | Some lf => forall n: nat, match nth_opt n li with
    | None | Some None => get_begin lf n = None /\ get_end lf n = None
    | Some (Some (bg, ed)) => get_begin lf n = Some bg /\ get_end lf n = Some ed
    end
  end.

Theorem linden_warblre_equiv:
  forall r s t,
  well_parenthesized r ->
  backtree (Group 0 r) s t ->
  match warblre_exec r s with
  | Error _ => True
  | Success None => False
  | Success (Some res) => match res with
    | Null _ => first_branch t = None
    | Exotic {| ExecArrayExotic.indices_array := ia |} _ =>
      match ia with
      | None => False
      | Some li => group_maps_equal li (first_branch t)
      end
    end
  end.
Proof.
  intros r s t Hwellparen Hbt.
  unfold warblre_exec.
Abort.