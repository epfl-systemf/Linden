(lang dune 3.14)

(name linden)

(generate_opam_files true)

(using coq 0.8)

(homepage "https://github.com/epfl-systemf/Linden")

(authors "Aurèle Barrière" "Victor Deng" "Clément Pit-Claudel")

(package
 (name linden)
 (synopsis "Formal Verification for JavaScript Regular Expressions")
 (depends
  (coq (= 8.18.0))
  (warblre (= 0.1.0))))
