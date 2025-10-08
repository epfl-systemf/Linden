# Local installation

If you wish to run our development on your own machine without a VM, this is possible. To do so, use the following instructions; you will need [opam](https://opam.ocaml.org/) and git as well as a code editor supporting Coq 8.18.0-8.19.2.

## Instructions

1. Download the code archive (linden.tar.gz on Zenodo), then decompress it in a folder of your choice. For instance, assuming that `linden.tar.gz` is located in the current directory, run:
   
   ```
   mkdir Linden && cd Linden
   tar zxvf ../linden.tar.gz
   ```

2. Create a local [opam](https://opam.ocaml.org/) switch:

   ```
   opam switch --no-install create .
   ```

   This should take 2 to 5 minutes approximately.

3. Pin the version of Warblre:

   ```
   opam pin add warblre https://github.com/epfl-systemf/Warblre.git#a1ffc3f2e47d942ad9e1194dfb71f0783ead6d8a
   ```

   Answer `y` when asked whether to create package `warblre` as a new package.

   This should take 4 to 10 minutes approximately.

4. Run `eval $(opam env)`.

5. Build all proofs with `dune build`. This should take a minute or two.

You can then open your code editor to browse the proofs. Make sure to run your code editor in the environment set by the `eval $(opam env)` command above (step 4).
