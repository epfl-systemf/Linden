From Warblre Require Import Semantics Frontend Result.
From Linden Require Import LindenParameters RegexpTranslation Regex Chars Tree Groups Semantics.
From Coq Require Import List.
Import ListNotations.

Definition equiv_flags: RegExpFlags := {|
    RegExpFlags.d := true;
    RegExpFlags.g := false;
    RegExpFlags.i := false;
    RegExpFlags.m := false;
    RegExpFlags.s := false;
    RegExpFlags.u := tt;
    RegExpFlags.y := true
    |}.

Definition warblre_exec (r: regex) (s: string): option ExecResult :=
    let warblre_r := to_warblre_regex r in
    match regExpInitialize (specParameters := LindenParameters) warblre_r equiv_flags with
    | Error _ => None
    | Success rei =>
        match regExpBuiltinExec rei s with
        | Error _ => None
        | Success res => Some res
        end
    end.

Fixpoint nth_opt {A: Type} (n: nat) (l: list A): option A :=
    match n, l with
    | _, nil => None
    | 0, x::_ => Some x
    | S n', _::q => nth_opt n' q
    end.

Definition group_maps_equal (li: list (option (nat*nat))) (l: option leaf) : Prop :=
    match l with
    | None => False
    | Some lf => forall n: nat, match nth_opt n li with
        | None | Some None => get_begin lf n = None /\ get_end lf n = None
        | Some (Some (bg, ed)) => get_begin lf n = Some bg /\ get_end lf n = Some ed
        end
    end.

Fixpoint num_groups (r: regex): nat :=
    match r with
    | Epsilon | Character _ => 0
    | Disjunction r1 r2 => num_groups r1 + num_groups r2
    | Sequence r1 r2 => num_groups r1 + num_groups r2
    | Star _ r1 => num_groups r1
    | Group _ r1 => S (num_groups r1)
    end.

Inductive well_parenthesized' : nat -> regex -> Prop :=
| wp_eps: forall n, well_parenthesized' n Epsilon
| wp_char: forall n cd, well_parenthesized' n (Character cd)
| wp_disj: forall n r1 r2, well_parenthesized' n r1 -> well_parenthesized' (num_groups r1 + n) r2 -> well_parenthesized' n (Disjunction r1 r2)
| wp_seq: forall n r1 r2, well_parenthesized' n r1 -> well_parenthesized' (num_groups r1 + n) r2 -> well_parenthesized' n (Sequence r1 r2)
| wp_star: forall n greedy r, well_parenthesized' n r -> well_parenthesized' n (Star greedy r)
| wp_group: forall n r, well_parenthesized' (S n) r -> well_parenthesized' n (Group (S n) r).

Definition well_parenthesized (r: regex) := well_parenthesized' 0 r.

Theorem linden_warblre_equiv:
    forall r s t,
    well_parenthesized r ->
    backtree (Group 0 r) s t ->
    match warblre_exec r s with
    | None => False
    | Some res => match res with
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