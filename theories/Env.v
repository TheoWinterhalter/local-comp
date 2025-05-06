(** Environments

  We have three kinds of environments:
  - Σ the global signature, containing definitions and interfaces.
  - Ξ the extension environment.
  - Γ the local environment.

**)

From Stdlib Require Import Utf8 String List Arith.
From LocalComp.autosubst Require Import AST.
From LocalComp Require Import BasicAST.

Import ListNotations.

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

(** Custom computation rule

  Fields are
  - [cr_env]: the environment of the rule [Θ]
  - [cr_pat]: the "pattern" for the left-hand side [p]
  - [cr_sub]: the "forcing" substitution [ρ] to go from [p] to the actual lhs
  - [cr_rep]: the replacing term [r]
  - [cr_typ]: the type for both sides [A]

  This represents the following (typed) definitional equality:
  [Θ ⊢ l <[ρ] ≡ r : A]

**)
Record crule := {
  cr_env : ctx ;
  cr_pat : term ;
  cr_sub : nat → term ;
  cr_rep : term ;
  cr_typ : term
}.

(** Global declaration **)
Inductive gdecl :=
| Ext (Ξ : ectx) (Δ : ctx) (R : list crule)
| Def (Ξ : ectx) (A : term) (t : term).

Definition gctx : Type := list (gref * gdecl).

Fixpoint gctx_get (Σ : gctx) (c : gref) : option gdecl :=
  match Σ with
  | [] => None
  | (k,d) :: Σ => if (c =? k)%string then Some d else gctx_get Σ c
  end.

Coercion gctx_get : gctx >-> Funclass.

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
