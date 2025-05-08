From Warblre Require Import Parameters Result RegExpRecord Typeclasses.
From Coq Require Import List.
Import ListNotations.

Module CharSetExt.
  Class class `{Character.class}: Type :=
    make
      {
        (* Operations required by the CharSet typeclass *)
        type: Type;
        empty: type;
        from_list: list Character -> type;
        union: type -> type -> type;
        singleton: Character -> type;
        size: type -> nat;
        remove_all: type -> type -> type;
        is_empty: type -> bool;
        contains: type -> Character -> bool;
        range: Character -> Character -> type;
        unique: forall {F: Type} {_: Result.AssertionError F}, type -> Result Character F;
        filter: type -> (Character -> bool) -> type;
        exist: type -> (Character -> bool) -> bool;
        exist_canonicalized: RegExpRecord -> type -> Character -> bool;

        (* Extra operations *)
        elements: type -> list Character;

        (* Properties required by the CharSet class *)
        exist_canonicalized_equiv:
        forall (rer: RegExpRecord) (s: type) (c: Character),
          exist_canonicalized rer s c = exist s (fun c': Character => (Character.canonicalize rer c' ==? c)%wt);

        (* Predicates and extra properties *)
        In: Character -> type -> Prop;
        Equal s1 s2 := forall c, In c s1 <-> In c s2;
        Empty s := forall c, ~In c s;
        Exists (P: Character -> Prop) s := exists c, In c s /\ P c;
        empty_spec: forall c, ~ In c empty;
        from_list_spec: forall c l, In c (from_list l) <-> List.In c l; (* Custom *)
        union_spec: forall c s1 s2, In c (union s1 s2) <-> In c s1 \/ In c s2;
        singleton_spec: forall x c, In x (singleton c) <-> c = x; (* = instead of fixed equivalence relation *)
        size_spec: forall s, size s = List.length (elements s);
        remove_all_spec: forall c s1 s2, In c (remove_all s1 s2) <-> In c s1 /\ ~In c s2;
        is_empty_spec: forall s, is_empty s = true <-> Empty s; (* custom *)
        contains_spec: forall c s, contains s c = true <-> In c s;
        range_spec: forall c l h, In c (range l h) <-> Character.numeric_value l <= Character.numeric_value c /\ Character.numeric_value c <= Character.numeric_value h; (* custom *)
        unique_succ_spec: forall {F: Type} `{_: Result.AssertionError F} (c: Character) (s: type),
          unique s = Success c <-> Equal s (singleton c);
        unique_succ_error: forall {F: Type} {H: Result.AssertionError F} (s: type),
          (exists c, unique s = Success c) \/ unique s = Error (@Result.f F H);
        filter_spec: forall f c s,
          In c (filter s f) <-> In c s /\ f c = true;
        exist_spec: forall f s,
          exist s f = true <-> Exists (fun c => f c = true) s;
        elements_spec1: forall c s, List.In c (elements s) <-> In c s;
        elements_spec2: forall s, NoDup (elements s)
      }.
  Notation CharSetExt := CharSetExt.type.

  Section Lemmas.
    Context `{charSetExtClass: class}.

    Lemma singleton_size: forall c, size (singleton c) = 1.
    Proof.
    Admitted.

    Lemma singleton_exist: forall c p, exist (singleton c) p = p c.
    Admitted.

    Lemma singleton_unique: forall {F: Type} {af: Result.AssertionError F} c, @unique _ _ F af (singleton c) = Success c.
    Admitted.
  End Lemmas.
End CharSetExt.
