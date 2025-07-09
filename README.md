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

Run the following:
```
opam switch create linden --empty
opam pin add warblre.0.1.0 https://github.com/epfl-systemf/Warblre.git#coq-versions
opam install .
```