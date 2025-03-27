(** Environments

  We have three kinds of environments:
  - Σ the global signature, containing definitions.
  - Ξ the extension environment.
  - Γ the local environment.

**)

From Stdlib Require Import Utf8 String List Arith.
From LocalComp.autosubst Require Import AST.
From LocalComp Require Import BasicAST.

(** Local environment, a list of types **)
Definition ctx := list term.

(** Extension arguments **)
Definition eargs := list (list term).

(** Instance declaration

  It is given by a global reference (that should point to an extension)
  and by arguments for the corresponding extension.

**)
Definition idecl : Type := gref * eargs.

(** Extension environment **)
Definition ectx := list idecl.

(** Access in an extension environment

  This is special because we use de Bruijn levels so we need to perform some
  simple arithmetic. We also avoid returning [Some] for de Bruijn levels that go
  too far.

**)

Definition ectx_get (Ξ : ectx) (M : eref) :=
  if length Ξ <=? M then None
  else nth_error Ξ (length Ξ - (S M)).

(** Patterns and pattern arguments **)
Inductive parg :=
| pvar
| pforce (t : term)
| psymb (x : aref) (l : list parg).

Record pat := {
  pat_head : aref ;
  pat_args : list parg
}.

(** Custom computation rule **)
Record crule := {
  cr_env : ctx ;
  cr_pat : pat ;
  cr_rep : term ;
  cr_typ : term
}.

(** Global declaration **)
Inductive gdecl :=
| Ext (Ξ : ectx) (Δ : ctx) (R : list crule)
| Def (Ξ : ectx) (A : term) (t : term).

Definition gctx : Type := gref → option gdecl.

Definition gnil : gctx :=
  λ _, None.

Definition gcons (k : gref) (d : gdecl) (Σ : gctx) : gctx :=
  λ r, if (r =? k)%string then Some d else Σ r.

Definition extends (Σ Σ' : gctx) :=
  ∀ r d,
    Σ r = Some d →
    Σ' r = Some d.

Notation "a ⊑ b" := (extends a b) (at level 70, b at next level).

(** Notations **)

Notation "'∙'" :=
  (@nil term).

Notation "Γ ,, d" :=
  (@cons term d Γ) (at level 20, d at next level).

Notation "Γ ,,, Δ" :=
  (@List.app term Δ Γ) (at level 25, Δ at next level, left associativity).
