#!/bin/bash
opam switch create linden --empty
opam pin add -y warblre.0.1.0 https://github.com/epfl-systemf/Warblre.git#coq-versions
opam install -y .