(lang dune 3.14)

(name linden)

(generate_opam_files true)

(using coq 0.8)

(package
 (name linden)
 (synopsis "An inductive semantics for JavaScript regexes")
 (depends
  (coq (= 8.18.0))
  (warblre (= 0.1.0))))
