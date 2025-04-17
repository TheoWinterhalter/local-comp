# Local computation rules in type theory

In this repository I develop a type theory which supports prenex quantification
over computation rules.
For the moment it contains a proof of conservativity of it over MLTT, and more
of the meta-theory.

More to come…

## Building

You need the Rocq prover 9.0, Equations and Autosubst 2 OCaml. You can install
them using
```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
```
