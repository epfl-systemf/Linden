Linden
======

# Repository structure

Folders:
- `Semantics`: definitions of regexes and tree semantics
- `Engine`: formalization and proofs of the PikeVM algorithm
- `WarblreEquiv`: proof of equivalence between the tree semantics and the Warblre semantics
- `Rewriting`: proofs of some regexp rewrites

For a description of the files inside the folders, see the README.md files in these folders.

# Install

Using OPAM:

```
opam pin add -y coq 8.18.0
opam pin add -y warblre.0.1.0 https://github.com/epfl-systemf/Warblre.git#coq-versions
opam install -y .
```
