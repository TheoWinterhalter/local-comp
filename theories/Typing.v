(** Typing **)

From Coq Require Import Utf8 List.
From LocalComp.autosubst Require Import AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import BasicAST Env.

Open Scope subst_scope.

Section Typing.

Reserved Notation "Γ ⊢ t : A"
  (at level 80, t, A at next level).

Reserved Notation "Γ ⊢ u ≡ v"
  (at level 80, u, v at next level).

Context (Σ : gctx) (Ξ : ectx).

Inductive conversion (Γ : ctx) : term → term → Prop :=

(** Computation rules **)

| conv_beta :
    ∀ A t u,
      Γ ⊢ app (lam A t) u ≡ t <[ u .. ]

(** Congruence rules **)

| cong_Pi :
    ∀ A A' B B',
      Γ ⊢ A ≡ A' →
      Γ ,, A ⊢ B ≡ B' →
      Γ ⊢ Pi A B ≡ Pi A' B'

| cong_lam :
    ∀ A A' t t',
      Γ ⊢ A ≡ A' →
      Γ ,, A ⊢ t ≡ t' →
      Γ ⊢ lam A t ≡ lam A' t'

| cong_app :
    ∀ u u' v v',
      Γ ⊢ u ≡ u' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ app u v ≡ app u' v'

(** Structural rules **)

| conv_refl :
    ∀ u,
      Γ ⊢ u ≡ u

| conv_sym :
    ∀ u v,
      Γ ⊢ u ≡ v →
      Γ ⊢ v ≡ u

| conv_trans :
    ∀ u v w,
      Γ ⊢ u ≡ v →
      Γ ⊢ v ≡ w →
      Γ ⊢ u ≡ w

where "Γ ⊢ u ≡ v" := (conversion Γ u v).

Inductive typing (Γ : ctx) : term → term → Prop :=

| type_var :
    ∀ x A,
      nth_error Γ x = Some A →
      Γ ⊢ var x : (plus (S x)) ⋅ A

| type_sort :
    ∀ i,
      Γ ⊢ Sort i : Sort (S i)

| type_pi :
    ∀ i j A B,
      Γ ⊢ A : Sort i →
      Γ ,, A ⊢ B : Sort j →
      Γ ⊢ Pi A B : Sort (max i j)

| type_lam :
    ∀ i j A B t,
      Γ ⊢ A : Sort i →
      Γ ,, A ⊢ B : Sort j →
      Γ ,, A ⊢ t : B →
      Γ ⊢ lam A t : Pi A B

| type_app :
    ∀ i j A B t u,
      Γ ⊢ t : Pi A B →
      Γ ⊢ u : A →
      Γ ⊢ A : Sort i →
      Γ ,, A ⊢ B : Sort j →
      Γ ⊢ app t u : B <[ u .. ]

| type_conv :
    ∀ i A B t,
      Γ ⊢ t : A →
      Γ ⊢ A ≡ B →
      Γ ⊢ B : Sort i →
      Γ ⊢ t : B

where "Γ ⊢ t : A" := (typing Γ t A).

(** Context formation **)

Inductive wf : ctx → Prop :=
| wf_nil : wf ∙
| wf_cons :
    ∀ Γ i A,
      wf Γ →
      Γ ⊢ A : Sort i →
      wf (Γ ,, A).

End Typing.

Notation "Σ | Ξ | Γ ⊢ u ≡ v" :=
  (conversion Σ Ξ Γ u v)
  (at level 80, u, v at next level, format "Σ | Ξ | Γ  ⊢  u  ≡  v").

Notation "Σ | Ξ | Γ ⊢ t : A" :=
  (typing Σ Ξ Γ t A)
  (at level 80, t, A at next level, format "Σ | Ξ | Γ  ⊢  t  :  A").
