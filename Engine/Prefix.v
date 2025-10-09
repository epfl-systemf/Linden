Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Semantics Tree.
From Linden Require Import Parameters LWParameters.
From Linden Require Import StrictSuffix.
From Warblre Require Import Base RegExpRecord.

Context {params: LindenParameters}.

Definition starts_with (p s : string) := p = List.firstn (length p) s.

Lemma starts_with_cons_iff: forall h1 t1 h2 t2,
	starts_with (h1 :: t1) (h2 :: t2) <-> h1 = h2 /\ starts_with t1 t2.
Proof.
	split; intros. 
	- unfold starts_with in H. injection H. intros. split; assumption.
	- unfold starts_with in *. destruct H. simpl. rewrite H. rewrite <-H0. reflexivity. 
Qed.

Lemma starts_with_trans: forall s1 s2 s3,
	starts_with s1 s2 -> starts_with s2 s3 -> starts_with s1 s3.
Proof.
	admit.
Admitted.

Class StrSearch := {
	str_search : string -> string -> option nat;
	starts_with_ss: forall s ss i, str_search s ss = Some i -> starts_with ss (List.skipn i s);
	no_earlier_ss: forall s ss i, str_search s ss = Some i -> forall i', i' < i -> ~ (starts_with ss (List.skipn i' s));
	not_found: forall s ss, str_search s ss = None -> forall i, i < length s -> ~ (starts_with ss (List.skipn i s))
}.

Definition input_search {strs: StrSearch} (inp: input) (p: string) : option input :=
	None.


Lemma input_search_strict_suffix {strs: StrSearch}:
	forall i1 i2 p, input_search i1 p = Some i2 -> strict_suffix i1 i2 forward.
Proof.
	intros (a1, b1) (a2, b2) p H.
	unfold input_search in H.
	destruct (str_search a1 p) eqn:Heq; try discriminate.
Qed.


Lemma input_search_starts_with {strs: StrSearch}:
	forall a1 b1 a2 b2 p, input_search (Input a1 b1) p = Some (Input a2 b2) -> starts_with p a2.
Proof.
	admit.
Admitted.


Lemma input_search_no_earlier {strs: StrSearch}:
	forall a1 b1 a2 b2 p, input_search (Input a1 b1) p = Some (Input a2 b2) -> forall s1 s2, a1 = s1 ++ s2 ++ a2 -> ~ (starts_with p s2).
Proof.
	admit.
Admitted.

Lemma input_search_not_found {strs: StrSearch}:
	forall a1 b1 p, input_search (Input a1 b1) p = None -> forall s1 s2, a1 = s1 ++ s2 -> ~ (starts_with p s2).
Proof.
	admit.
Admitted.

(* ------ *)

(* 
Inductive regex : Type :=
| Character (cd : char_descr)   (* includes character classes and dot *)
| Disjunction (r1 r2 : regex) 
| Quantified (greedy:bool) (min: nat) (delta: non_neg_integer_or_inf) (r1: regex) (* means any number of repetitions of r1 between min and min+delta *)
| Anchor (a: anchor)

Inductive char_descr: Type :=
| CdUnicodeProp (p: Property)
| CdNonUnicodeProp (p: Property)
| CdRange (l h: Character)
| CdUnion (cd1 cd2: char_descr).
*)

Inductive literal : Type :=
| Exact (s : string) (* the entire match is exactly `s` *)
| Prefix (s : string) (* the match starts with `s` *)
| None. (* this indicates the match cannot exist, as opposed to Prefix [] which means we do not know anything about the match *)

Definition literal_eq_dec: forall (l1 l2: literal), { l1 = l2 } + { l1 <> l2 }.
Proof. decide equality; apply string_eq_dec. Defined.
Instance literal_EqDec: EqDec literal := EqDec.make literal literal_eq_dec.

Definition prefix (l : literal) :=
	match l with
	| Exact s => s
	| Prefix s => s
	| None => []
	end.

Definition chain_literals (l1 l2 : literal) : literal :=
	match l1 with
	| Exact s1 => match l2 with
		| Exact s2 => Exact (s1 ++ s2)
		| Prefix s2 => Prefix (s1 ++ s2)
		| None => None
	end
	| Prefix s1 => Prefix s1
	| None => None
	end.

Lemma chain_literals_assoc:
	forall l1 l2 l3,
		chain_literals l1 (chain_literals l2 l3) = chain_literals (chain_literals l1 l2) l3.
Proof.
	intros l1 l2 l3.
	destruct l1; destruct l2; destruct l3; simpl; try reflexivity.
	all: f_equal; rewrite app_assoc; reflexivity.
Qed.

Lemma chain_literals_empty_exact_right:
	forall l1,
		chain_literals l1 (Exact []) = l1.
Proof.
	intros l1.
	destruct l1; simpl; try reflexivity.
	- f_equal. rewrite app_nil_r. reflexivity.
Qed.

Fixpoint common_prefix (s1 s2 : string) : string :=
	match s1, s2 with
	| h1 :: t1, h2 :: t2 => if h1 == h2 then h1 :: common_prefix t1 t2 else []
	| _, _ => []
	end.

Definition merge_literals (l1 l2 : literal) : literal :=
	if l1 == l2 then l1 else Prefix (common_prefix (prefix l1) (prefix l2)).

Fixpoint extract_literal (r: regex) : literal :=
	match r with
	| Epsilon => Exact []
	| Regex.Character cd => match cd with
		| CdEmpty => None
		| CdDot => Prefix []
		| CdAll => Prefix []
		| CdSingle c => Exact [c]
		| CdDigits => Prefix []
		| CdNonDigits => Prefix []
		| CdWhitespace => Prefix []
		| CdNonWhitespace => Prefix []
		| CdWordChar => Prefix []
		| CdNonWordChar => Prefix []
		| CdUnicodeProp p => Prefix [] (* FIXME: todo *)
		| CdNonUnicodeProp p => Prefix [] (* FIXME: todo *)
		| CdInv cd' => Prefix []
		| CdRange l h => if l == h then Exact [l] else Prefix []
		| CdUnion cd1 cd2 => Prefix [] (* FIXME: check if the union defines a single char *)
		end
	| Disjunction r1 r2 => merge_literals (extract_literal r1) (extract_literal r2)
	| Sequence r1 r2 => chain_literals (extract_literal r1) (extract_literal r2)
	| Quantified _ min _ r1 => Prefix [] (* FIXME: todo *)
	| Lookaround _ r1 => Prefix [] (* TODO: possible by merging the literals around but that requires a different way of computing literals. For instance /(?=abc)p/ => None, /(?<=abc)c/ => 'c' (but not exact nor prefix) *)
	| Group _ r1 => extract_literal r1
	| Anchor _ => Prefix [] (* TODO: can be used to detect impossible matches, like /\b\B/, but this requires restructuring this function *)
	| Backreference _ => Prefix [] (* TODO: possible to incorporate by having a group map from group id to `literal`. Then something like /(abc)\1/ can be extracted as `abcabc` *)
	end.

Definition extract_action_literal (a : action) : literal :=
	match a with
	| Areg r => extract_literal r
	| Acheck _ => Exact []
	| Aclose _ => Exact []
	end.

Fixpoint extract_actions_literal (acts : list action) : literal :=
	match acts with
	| [] => Exact []
	| a :: rest => chain_literals (extract_action_literal a) (extract_actions_literal rest)
	end.

Section LiteralExtraction.
Context (rer: RegExpRecord).
Context (no_i_flag : RegExpRecord.ignoreCase rer = false).

Lemma char_match_range_same: forall c l,
	char_match rer c (CdRange l l) = true -> c = l.
Proof.
	intros.
	unfold char_match in *. unfold char_match' in *.
	rewrite (canonicalize_casesenst rer _ no_i_flag) in H.
	admit.
Admitted.

Lemma extract_literal_prefix_general:
	forall acts tree inp gm result,
		is_tree rer acts inp Groups.GroupMap.empty forward tree ->
		tree_res tree gm inp forward = Some result ->
		starts_with (prefix (extract_actions_literal acts)) (next_str inp).
Proof.
	intros acts tree inp gm result Htree Hleaf.

	remember (forward) as dir.
	generalize dependent result.
	generalize dependent gm.
	induction Htree; intros; subst;
		(* the prefix is empty *)
		try reflexivity;
		(* the literal is that of the rest of the actions *)
		try solve[simpl in *;
		destruct (extract_actions_literal cont); eapply IHHtree; eauto];
		(* mismatch violating tree_res result *)
		try discriminate Hleaf.
	
	(* tree_char *)
	- destruct cd eqn:Heqcd; subst; try reflexivity;
			(* there is a character to read *)
			unfold read_char in READ; destruct inp eqn:Heqinp; destruct next eqn:Heqnext; try discriminate READ; subst;
			(* the character matches *)
			destruct (char_match rer t _) eqn:Heqmatch; try discriminate READ; injection READ; intros; subst.
		(* CdSingle *)
		+ assert (c = c0). {
				unfold char_match in Heqmatch. simpl in Heqmatch.
				do 2 rewrite (canonicalize_casesenst _ _ no_i_flag) in Heqmatch.
				apply EqDec.inversion_true. assumption.
			} subst.
			simpl. 
			destruct (extract_actions_literal cont); simpl; try reflexivity.
			all: simpl; rewrite starts_with_cons_iff; split; try reflexivity;
				eapply IHHtree; eauto.
		(* CdRange *)
		+	simpl. destruct (l ==? h)%wt eqn:Heq; try reflexivity.
			assert (l = h). apply EqDec.inversion_true; assumption. subst.
			assert (c = h). apply char_match_range_same. exact Heqmatch. subst. simpl.

			destruct (extract_actions_literal cont); simpl; try reflexivity.
			all: simpl; rewrite starts_with_cons_iff; split; try reflexivity;
				eapply IHHtree; eauto.
	(* tree_disj *)
	- simpl in Hleaf. unfold seqop in Hleaf.
		destruct (tree_res t1) eqn:Heqres.
		+ etransitivity.
			* eapply starts_with_chain_literals.
				eapply starts_with_merge_literals.
			* eapply IHHtree1; eauto.
		+ simpl. rewrite merge_literals_comm.
			etransitivity.
			* eapply starts_with_chain_literals.
				eapply starts_with_merge_literals.
			* eapply IHHtree2; eauto.
	(* tree_sequence *)
	- simpl. rewrite <-chain_literals_assoc.
		eapply IHHtree; eauto.
Qed.

Lemma extract_actions_literal_regex:
	forall r, extract_actions_literal [Areg r] = extract_literal r.
Proof. intros. apply chain_literals_empty_exact_right. Qed.

Theorem extract_literal_prefix:
	forall r tree inp result,
		is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree ->
		first_leaf tree inp = Some result ->
		starts_with (prefix (extract_literal r)) (next_str inp).
Proof.
	intros.
	rewrite <- (extract_actions_literal_regex r).
	eapply extract_literal_prefix_general; eassumption.
Qed.
End LiteralExtraction.
