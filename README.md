# Encode the Cake and Eat it Too
## Controlling computation in type theory, *locally*

Repository containing the formalisation that goes with the POPL submission
entitled "Encode the Cake and Eat it Too".

[See the rendered Rocq code, with comments.](https://anonymous.4open.science/w/local-comp-popl-DE23/doc)

## Building

You need the Rocq prover 9.0, Equations and Autosubst 2 OCaml. You can install
them using
```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
```

Then to verify the proof, just use `make`:
```sh
make autosubst
make
```
