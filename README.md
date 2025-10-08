# Encode the Cake and Eat it Too
## Controlling computation in type theory, *locally*

Repository containing the formalisation that goes with our draft
entitled ["Encode the Cake and Eat it Too: Controlling computation in type theory, locally"](https://hal.science/view/index/docid/5160846).

[See the rendered Rocq code, with comments.](https://theowinterhalter.github.io/local-comp/)

## Building

You need the Rocq prover 9.0, Equations and Autosubst 2 OCaml (needs ocaml<5, recommended 4.14.2). You can install
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
