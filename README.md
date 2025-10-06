# Artifact for ‘Formal Verification for JavaScript Regular Expressions: a Proven Mechanized Semantics and its Applications, in Rocq’ at POPL 2026

Welcome to our artifact!

The simplest way to evaluate this artifact is to download the VM (`linden.ova`) from Zenodo and follow the instructions below.

The VM username is `ubuntu`.  The password is also `ubuntu`.
The artifact directory is `~/Desktop/artifact`.
You may want to change the VM's display resolution after starting it (in Ubuntu's settings menu).

We are applying for the Available, Functional and Reusable badges.

Optionally, as an alternative if you prefer to recreate a fresh environment, we have an automated Packer script to rebuild and reprovision the VM from scratch, making the whole setup automatically reproducible.
Or you can run our code locally, without needing a VM. These last two options are described in section [Local setup](#optional-appendix-local-setup) at the bottom of this file.


## Description of artifact

The artifact consists of our Rocq development for the definitions, theorems, proofs and relevant examples contained in the paper.

The correspondence between each definition and theorem in the paper and their Rocq counterpart is described in [`correspondence_table.pdf`](correspondence_table.pdf) (TODO). A table of correspondences for theorems only can also be found [below](#factual-claim-1-mechanization).

Some of the correspondences in the correspondence table are not exact due to simplifications in the paper for legibility and understandability; the differences are documented in [`correspondence_notes.md`](correspondence_notes.md).

### Development structure

The Rocq files are split into five folders:
- `Semantics`: definition of regexes and their semantics (Sections 2 and 3 of the paper)
- `Engine`: formalizing and proving correct the PikeVM algorithm (Section 6 of the paper)
- `WarblreEquiv`: proving the equivalence between the Linden semantics and the [Warblre semantics](https://github.com/epfl-systemf/Warblre) (Section 4 of the paper)
- `Rewriting`: proving that a notion of regex equivalence allows rewrites under a context (Section 5 of the paper)
- `Utils`: canonical group maps

### Required hardware

We recommend running on an Ubuntu 24.04 LTS machine with at least 16GB of RAM.  The VM is configured to use:

- 8GB of RAM (to support the OS and build proofs)
- 32GB of free space on your hard drive

### Getting started guide

#### If you are using our VM image

Open a terminal, cd into the artifact directory at `~/Desktop/artifact`, then **run `eval $(opam env)`**. **If you need several terminal windows, repeat these instructions when opening each of them.**

The proofs are already pre-built. To build them again, run `dune clean` followed by `dune build` from the root directory of the artifact. `dune build` should take less than two minutes to run. Then, to step through any proofs you would like to, you can either use Visual Studio Code with VSCoq Legacy or Emacs with Proof General and company-coq, both of which are pre-installed in the VM.  
To use Visual Studio Code, run `code .` *in the terminal you opened* (from `~/Desktop/artifact`), click "Trust the authors", then open the Rocq file you are interested in and type `Alt+↓` to step forward or `Alt+↑` to step backwards.  
To use Emacs, run `emacs .` *in the terminal you opened* (from `~/Desktop/artifact`), then open the Rocq file you are interested in and type `Ctrl+C Ctrl+N` to step forward and `Ctrl+C Ctrl+U` to step backwards.

#### If you are running locally

After following the instructions in [section "[Optional appendix] Local setup", subsection "Without a VM"](#without-a-vm), you should have a local Opam switch in the artifact directory as well as the proofs built. Use the Opam switch, e.g. by opening a terminal, cd'ing into the artifact directory and running `eval $(opam env)`, to run any Coq IDE you would like to step through the proofs. TODO Mac OS, Windows?

## Summary of claims and experimental results

**Claims supported by the artifact:**

- Factual claim 1: mechanization. Our formal semantics, definitions and proofs are fully mechanized in the Rocq proof assistant.

- Factual claim 2: completeness and faithfulness of semantics. Our semantics is complete with respect to and faithful to the Warblre embedding of the ECMAScript 2023 specification of JavaScript regexes. (Section 4)

- Factual claim 3: regex equivalence. Our definition of regex equivalence permits proving and disproving regex rewrites. (Section 5)

- Factual claim 4: PikeVM correctness. The PikeVM algorithm is correct with respect to the Warblre mechanization of the ECMAScript 2023 specification of JavaScript regexes. (Section 6)

**Claims not supported by the artifact:** This artifact does not support the claim that the semantics is practical; this claim is supported by the two applications of the semantics presented in the paper, namely regex rewriting and the verification of the PikeVM.


## Step-by-step instructions

### Factual claim 1: mechanization

**Claim:** Our formal semantics, definitions and proofs are fully mechanized in the Rocq proof assistant.

**To verify this claim:**

The correspondence table ([`correspondence_table.pdf`](correspondence_table.pdf) (TODO)) provides an exhaustive matching between the definitions and theorems shown in the paper and their Rocq counterparts, in the order of appearance in the paper. The correspondences for theorems are listed below. You can read the paper and refer to the correspondence table (either the full one or the abridged one) and the Rocq development whenever you encounter a definition or a theorem.

The most important theorems are Theorems 4, 5, 6, 7 and 16. Feel free to review the other theorems below or other definitions in the full correspondence table if time permits.

| Paper definition | File | Rocq name |
|----------|----------------|------------|
| Section 3 | | |
| Theorem 1 | [Semantics/Semantics.v](Semantics/Semantics.v) | `is_tree_determ` |
| Theorem 2 | [Semantics/FunctionalSemantics.v](Semantics/FunctionalSemantics.v) | `functional_terminates` |
| Theorem 3 | [Semantics/ComputeIsTree.v](Semantics/ComputeIsTree.v) | `compute_is_tree` |
| Section 4 | | |
| Theorem 4 | [WarblreEquiv/EquivMain.v](WarblreEquiv/EquivMain.v) | `equiv_main_reconstruct` |
| Section 5 | | |
| Theorem 5 | [Rewriting/Equivalence.v](Rewriting/Equivalence.v) | `regex_equiv_ctx_samedir` |
| Theorem 6 | [Rewriting/Equivalence.v](Rewriting/Equivalence.v) | `regex_equiv_ctx_forward` |
| Theorem 7 | [Rewriting/Equivalence.v](Rewriting/Equivalence.v) | `regex_equiv_ctx_backward` |
| Theorem 8 | [Rewriting/Equivalence.v](Rewriting/Equivalence.v) | `observe_equivalence` |
| Section 6 | | |
| Theorem 9 | [Engine/BooleanSemantics.v](Engine/BooleanSemantics.v) | `encode_equal` |
| Theorem 10 | [Engine/BooleanSemantics.v](Engine/BooleanSemantics.v) | `boolean_correct` |
| Theorem 11 | [Engine/PikeTree.v](Engine/PikeTree.v) | `init_piketree_inv` |
| Theorem 12 | [Engine/PikeTree.v](Engine/PikeTree.v) | `pts_preservation` |
| Theorem 13 | [Engine/PikeEquiv.v](Engine/PikeEquiv.v) | `initial_pike_inv` |
| Theorem 14 | [Engine/PikeEquiv.v](Engine/PikeEquiv.v) | `invariant_preservation` |
| Theorem 15 | [Engine/Correctness.v](Engine/Correctness.v) | `pike_vm_to_pike_tree` |
| Theorem 16 | [Engine/Correctness.v](Engine/Correctness.v) | `pike_vm_warblre` |


To verify that a given theorem with Rocq name `thm` does not rely on unproven facts (other than axioms present in Rocq itself), use the command `Print Assumptions thm.` (replacing `thm` with the name of the theorem) after stepping through the proof of the theorem and the following `Qed.` command.  
This command should yield only the section variable `params : LindenParameters`, sometimes the section variable `rer : RegExpRecord`, sometimes the section variable `TS : TSeen params`, sometimes the section variable `VMS : VMSeen`, and sometimes the Rocq axiom `Eqdep.Eq_rect_eq.eq_rect_eq`.  
The `LindenParameters` typeclass is defined in `Semantics/Parameters.v`: it contains the parameters that the Linden development relies on, namely three typeclasses that Warblre relies on (character, Unicode property, character set) and a property of the canonicalization function. This typeclass is instantiated in `Semantics/Inst.v`.  
The `RegExpRecord` contains the values of the flags and the number of capturing groups in the regex being matched.  
The `TSeen` typeclass is defined in `Engine/SeenSets.v`, which also contains an instantiation of that typeclass. It specifies a type of set of seen trees.  
The `VMSeen` typeclass is also defined in `Engine/SeenSets.v`, which also contains an instantiation of that typeclass. It specifies a set of seen program counters.

### Factual claim 2: completeness and faithfulness of semantics

**Claim:** Our semantics supports all the features of JavaScript regexes described in the ECMAScript 2023 specification and is faithful to this specification.

**To verify this claim:**

This claim is supported by the faithfulness theorem `equiv_main_reconstruct` in [WarblreEquiv/EquivMain.v](WarblreEquiv/EquivMain.v). Read its statement, and check that it proof-checks, e.g. by running `dune build` from the project root and optionally stepping through the proof afterwards. The command `dune build` should take at most two minutes to run from a clean state.

Check that this theorem does not rely on unproven facts other than a Rocq axiom, by running `Print Assumptions equiv_main_reconstruct.` after the `Qed.` of the theorem (a discussion of the section variables can be found in section [Factual claim 1: mechanization](#factual-claim-1-mechanization)).

Check that the faithfulness theorem applies to all regexes: look at the regex translation function `warblre_to_linden` in [WarblreEquiv/RegexpTranslation.v](WarblreEquiv/RegexpTranslation.v) that is used in the statement of the faithfulness theorem.

### Factual claim 3: regex equivalence

**Claim:** Our definition of regex equivalence permits proving and disproving regex rewrites.

**To verify this claim:**

This claim is supported by several theorems proven in the Rocq development, namely `regex_equiv_ctx_samedir`, `regex_equiv_ctx_forward`, `regex_equiv_ctx_backward`, `observe_equivalence` in [Rewriting/Equivalence.v](Rewriting/Equivalence.v), and all the theorems relating to Figure 5 in the [correspondence table](path/to/correspondence_table.pdf). Read the theorem statements, then check that all these theorems proof-check by running `dune build` from the project root and optionally stepping through the proofs afterwards. The command `dune build` should take at most two minutes to run from a clean state.

Check that these theorems do not rely on unproven facts, by running `Print Assumptions thm.` after the `Qed.` of each theorem `thm` (a discussion of the section variables can be found in section [Factual claim 1: mechanization](#factual-claim-1-mechanization)).

### Factual claim 4: PikeVM correctness

**Claim:** The PikeVM algorithm is correct with respect to the Warblre mechanization of the ECMAScript 2023 specification of JavaScript regexes.

**To verify this claim:**

This claim is supported by the theorem `pike_vm_warblre` in [Engine/Correctness.v](Engine/Correctness.v). Read its statement, then check that it proof-checks by running `dune build` from the project root and optionally stepping through the proof afterwards. The command `dune build` should take at most two minutes to run from a clean state.

Check that this theorem does not rely on unproven facts other than a Rocq axiom, by running `Print Assumptions pike_vm_warblre.` after the `Qed.` of the theorem (a discussion of the section variables can be found in section [Factual claim 1: mechanization](#factual-claim-1-mechanization)).



## Ensuring reusability

We claim that our development can be reused to perform formal proofs about JavaScript regexes. To verify this claim, we have prepared a proof exercise that you can do in Rocq using our development.

This exercise is located in the file `Semantics/Exercise.v`. Follow the instructions in that file to solve the exercise.

## Thank you!

Thank you so much for reviewing our artifact!


## [Optional appendix] Local setup

Our VM is automatically generated from a textual description, using a [Packer](https://www.packer.io/) script (Packer is a tool for “images as code”, used to build reproducible VM images, containers, etc.).

### To rebuild the VM automatically

1. [Install VirtualBox](https://www.virtualbox.org/manual/ch02.html)
2. [Install Packer](https://developer.hashicorp.com/packer/install) ≥ v1.10.2, `yamllint` (from `apt` package `yamllint`) and `xorriso` (from `apt` package `xorriso`)
3. Unzip `linden.tar.gz` and navigate to `artifact-vm/`
4. Run `make vm`

The last command will download the Ubuntu 24.04 ISO image, automatically set it up in a fresh VM, provision the VM by copying our code into it, installing dependencies and code editors with extensions, and compiling our code, leaving you with a brand new VM ready for artifact evaluation. This is the process we used to create the VM on Zenodo.

### Without a VM

If you wish to run our development on your own machine without a VM, this is possible. To do so, use the following instructions; you will need [opam](https://opam.ocaml.org/). TODO Mac OS, Windows?

1. Create a local [opam](https://opam.ocaml.org/) switch:

   ```
   opam switch --no-install create .
   ```

2. Pin the version of Warblre:

   ```
   opam pin add warblre https://github.com/epfl-systemf/Warblre.git#a1ffc3f2e47d942ad9e1194dfb71f0783ead6d8a
   ```

3. Build all proofs with `dune build`.
