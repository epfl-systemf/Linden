Require Import List Lia.
Import ListNotations.
From Linden Require Import Utils.
Import Utils.List.
From Warblre Require Import Base Typeclasses.

(** * Characters and Strings  *)

Section Chars.
  Context `{characterClass: Character.class}.

  Definition string := list Character.

  (* In the semantics, the input string is represented with both the next characters to read
   and the reversed list of previously read characters (in case we change direction for a lookbehind) *)
  Inductive input : Type :=
  | Input (next: string) (pref: string).

  Definition string_eq_dec : forall (x y : string), { x = y } + { x <> y }.
  Proof.
    decide equality. apply Character.eq_dec.
  Defined.
  #[export] Instance string_EqDec: EqDec string := EqDec.make string string_eq_dec.

  Definition input_eq_dec: forall (i1 i2: input), { i1 = i2 } + { i1 <> i2 }.
  Proof. decide equality; apply string_eq_dec. Defined.
  #[export] Instance input_EqDec: EqDec input := EqDec.make input input_eq_dec.


  Definition next_str (i:input) : string :=
    match i with
    | Input s _ => s
    end.

  Definition current_str (i:input) (dir: Direction) : string :=
    match i with
    | Input next pref =>
        match dir with forward => next | backward => pref end
    end.

  Definition input_str (i: input): string :=
    match i with
    | Input next pref => List.rev pref ++ next
    end.

  (* Getting a substring from an input *)
  Definition substr (inp: input) (startIdx endIdx: nat): string :=
    List.firstn (endIdx-startIdx) (List.skipn startIdx (input_str inp)).

  Definition init_input (str:string) : input :=
    Input str [].


  (* Definition of when an input is compatible with (i.e. represents) a given input string str0. *)
  Inductive input_compat: input -> string -> Prop :=
  | Input_compat: forall next pref str0, List.rev pref ++ next = str0 -> input_compat (Input next pref) str0.


  (* Deciding whether a character is a word character, to check for word boundaries and for character classes \w and \W *)
  Definition word_char c := inb c Character.ascii_word_characters.

  (* Axiom specifying that char_all contains all characters. TODO Do we want that? *)
  Axiom char_all_in: forall c, In c Character.all.

  (* Lemma for boolean version of In *)
  Lemma char_all_inb: forall c, inb c Character.all = true.
  Proof.
    intro c. rewrite inb_spec. apply char_all_in.
  Qed.


  (** * Character Descriptors  *)
  (* by character descriptors, we mean everything that can represent a single character *)
  (* the character itself, the dot, an escape, a character group like \d, character classes *)
  Inductive char_descr: Type :=
  | CdEmpty
  | CdDot
  | CdAll
  | CdSingle (c: Character)
  | CdDigits
  | CdWhitespace
  | CdWordChar
  | CdInv (cd: char_descr)
  | CdRange (l h: Character)
  | CdUnion (cd1 cd2: char_descr).

  
  Fixpoint char_match (c: Character) (cd: char_descr): bool :=
    match cd with
    | CdEmpty => false
    | CdDot => true (* Temporary; at the end, we'd like to take the multiline flag into account *)
    | CdAll => true
    | CdSingle c' => c == c'
    | CdDigits => inb c Character.digits
    | CdWhitespace => inb c Character.white_spaces || inb c Character.line_terminators
    | CdWordChar => inb c Character.ascii_word_characters (* Temporary; at the end, we'd like to use a rer *)
    | CdInv cd' => negb (char_match c cd')
    | CdRange l h => (Character.numeric_value l <=? Character.numeric_value c) && (Character.numeric_value c <=? Character.numeric_value h)
    | CdUnion cd1 cd2 => char_match c cd1 || char_match c cd2
    end.


  Lemma single_match:
    forall c1 c2, char_match c1 (CdSingle c2) = true <-> c1 = c2.
  Proof.
    intros c1 c2. simpl. apply EqDec.inversion_true.
  Qed.

  Definition char_descr_eq_dec : forall (cd1 cd2: char_descr), { cd1 = cd2 } + { cd1 <> cd2 }.
  Proof. decide equality; apply Character.eq_dec. Defined.


  (** * Reading Characters in the String *)

  (* read_char cd i dir returns None if the next character of i with direction dir is accepted by cd *)
  (* otherwise it returns the next input after reading the character, as well as the character actually read *)
  Definition read_char (cd:char_descr) (i:input) (dir: Direction) : option (Character * input) :=
    match i with
    | Input next pref =>
        match dir with
        | forward =>
            match next with
            | [] => None
            | h::next' => if char_match h cd
                        then Some (h, Input next' (h::pref))
                        else None
            end
        | backward =>
            match pref with
            | [] => None
            | h::pref' => if char_match h cd
                        then Some (h, Input (h::next) pref')
                        else None
            end
        end
    end.

  Inductive ReadResult  : Type :=
  | CanRead
  | CannotRead.

  (* the function above is useful when defining trees *)
  (* however, the VMs do it differently: they will test the same character of the input multiple times before advancing *)
  (* instead, we use the two following functions to read and advance *)

  (* simply checks if the next character of the input corresponds to the given character descriptor *)
  Definition check_read (cd:char_descr) (i:input) (dir: Direction) : ReadResult :=
    match i with
    | Input next pref =>
        match dir with
        | forward =>
            match next with
            | [] => CannotRead
            | h::next' => if char_match h cd
                        then CanRead
                        else CannotRead
            end
        | backward =>
            match pref with
            | [] => CannotRead
            | h::pref' => if char_match h cd
                        then CanRead
                        else CannotRead
            end
        end
    end.

  (* Advance input to the next or previous character depending on direction *)
  Definition advance_input (i:input) (dir: Direction) : option input :=
    match i with
    | Input next pref =>
        match dir with
        | forward =>
            match next with
            | [] => None
            | h::next' => Some (Input next' (h::pref))
            end
        | backward =>
            match pref with
            | [] => None
            | h::pref' => Some (Input (h::next) pref')
            end
        end
    end.

  (* Advancing input several times *)
  Definition advance_input_n (i: input) (n: nat) (dir: Direction): input :=
    match i with
    | Input next pref =>
        match dir with
        | forward =>
            let nnext := List.skipn n next in
            let read := List.firstn n next in
            Input nnext (List.rev read ++ pref)
        | backward =>
            let npref := List.skipn n pref in
            let read := List.firstn n pref in
            Input (List.rev read ++ next) npref
        end
    end.

  (* the proof of equivalence between the two *)
  Theorem can_read_correct:
    forall i1 cd dir i2,
    (exists c, read_char cd i1 dir = Some (c, i2)) <->
      check_read cd i1 dir = CanRead /\ advance_input i1 dir = Some i2.
  Proof.
    intros i1 cd dir i2. split; intros.
    - destruct H as [c H].
      destruct i1. simpl. simpl in H. destruct dir.
      + destruct next. inversion H. destruct (char_match t cd); inversion H; auto.
      + destruct pref. inversion H. destruct (char_match t cd); inversion H; auto.
    - destruct i1. simpl. simpl in H. destruct dir.
      + destruct next; inversion H; inversion H1.
        exists t. destruct (char_match t cd); inversion H0. auto.
      + destruct pref; inversion H; inversion H1.
        exists t. destruct (char_match t cd); inversion H0. auto.
  Qed.

  Theorem cannot_read_correct:
    forall i cd dir,
      read_char cd i dir = None <-> check_read cd i dir = CannotRead.
  Proof.
    intros i cd dir. destruct i. simpl. destruct dir.
    - destruct next; split; auto.
      + destruct (char_match t cd); auto. inversion 1.
      + destruct (char_match t cd); auto. inversion 1.
    - destruct pref; split; auto.
      + destruct (char_match t cd); auto. inversion 1.
      + destruct (char_match t cd); auto. inversion 1.
  Qed.

  (* Inductive relation of next_inputs *)
  Inductive next_input : input -> input -> Direction -> Prop :=
  | nextin: forall i1 i2 dir (ADVANCE: advance_input i1 dir = Some i2),
      next_input i1 i2 dir.
End Chars.
