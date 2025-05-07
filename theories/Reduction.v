(** Reduction

  We define reduction for the language as a way to study decidability of
  conversion and type checking.
  Those will be achieved with some assumptions on the reduction relation,
  namely confluence and type preservation.

**)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing BasicMetaTheory
  GScope.
From Stdlib Require Import Setoid Morphisms Relation_Definitions Relation_Operators.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Section Red.

  Reserved Notation "Γ ⊢ u ↦ v"
    (at level 80, u, v at next level).

  Context (Σ : gctx) (Ξ : ectx).

  Inductive red1 (Γ : ctx) : term → term → Prop :=

  (** Computation rules **)

  | red_beta A t u : Γ ⊢ app (lam A t) u ↦ t <[ u .. ]

  | red_unfold c ξ Ξ' A t :
      Σ c = Some (Def Ξ' A t) →
      Γ ⊢ const c ξ ↦ einst ξ t

  | red_rule E Ξ' Δ R M ξ' n rule σ :
      Σ E = Some (Ext Ξ' Δ R) →
      ectx_get Ξ M = Some (E, ξ') →
      nth_error R n = Some rule →
      let δ := length Δ in
      let lhs := rlhs M ξ' δ rule in
      let rhs := rrhs M ξ' δ rule in
      Γ ⊢ lhs <[ σ ] ↦ rhs <[ σ ]

  (** Congruence rules **)

  | red_Pi_dom A B A' :
      Γ ⊢ A ↦ A' →
      Γ ⊢ Pi A B ↦ Pi A' B

  | red_Pi_cod A B B' :
      Γ ,, A ⊢ B ↦ B' →
      Γ ⊢ Pi A B ↦ Pi A B'

  | red_lam_dom A t A' :
      Γ ⊢ A ↦ A' →
      Γ ⊢ lam A t ↦ lam A' t

  | red_lam_body A t t' :
      Γ ,, A ⊢ t ↦ t' →
      Γ ⊢ lam A t ↦ lam A t'

  | red_app_fun u v u' :
      Γ ⊢ u ↦ u' →
      Γ ⊢ app u v ↦ app u' v

  | red_app_arg u v v' :
      Γ ⊢ v ↦ v' →
      Γ ⊢ app u v ↦ app u v'

  where "Γ ⊢ u ↦ v" := (red1 Γ u v).

End Red.

Notation "Σ ;; Ξ | Γ ⊢ u ↦ v" :=
  (red1 Σ Ξ Γ u v)
  (at level 80, u, v at next level).

(** Reflexive transitive closure **)

Definition red Σ Ξ Γ := clos_refl_trans _ (λ u v, Σ ;; Ξ | Γ ⊢ u ↦ v).

Notation "Σ ;; Ξ | Γ ⊢ u ↦* v" :=
  (red Σ Ξ Γ u v)
  (at level 80, u, v at next level).

(** Equivalence **)

Definition equiv Σ Ξ Γ := clos_refl_sym_trans _ (λ u v, Σ ;; Ξ | Γ ⊢ u ↦ v).

Notation "Σ ;; Ξ | Γ ⊢ u ↮ v" :=
  (equiv Σ Ξ Γ u v)
  (at level 80, u, v at next level).

#[export] Instance equiv_refl Σ Ξ Γ : Reflexive (equiv Σ Ξ Γ).
Proof.
  intros u.
  eapply rst_refl.
Qed.

#[export] Instance equiv_sym Σ Ξ Γ : Symmetric (equiv Σ Ξ Γ).
Proof.
  intros u v h.
  eapply rst_sym. eassumption.
Qed.

#[export] Instance equiv_trans Σ Ξ Γ : Transitive (equiv Σ Ξ Γ).
Proof.
  intros u v w h1 h2.
  eapply rst_trans. all: eassumption.
Qed.

Lemma rst_step_ind A B R R' f x y :
  (∀ x y, R x y → clos_refl_sym_trans B R' (f x) (f y)) →
  clos_refl_sym_trans A R x y →
  clos_refl_sym_trans B R' (f x) (f y).
Proof.
  intros hstep h.
  induction h.
  - eauto.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans. all: eassumption.
Qed.

Lemma equiv_red_ind Σ Ξ Γ Δ f x y :
  (∀ x y, Σ ;; Ξ | Δ ⊢ x ↦ y → Σ ;; Ξ | Γ ⊢ f x ↮ f y) →
  Σ ;; Ξ | Δ ⊢ x ↮ y →
  Σ ;; Ξ | Γ ⊢ f x ↮ f y.
Proof.
  intros hred h.
  eapply rst_step_ind. all: eauto.
Qed.

(** Reduction characterises conversion **)

Lemma red_Pi Σ Ξ Γ A A' B B' :
  Σ ;; Ξ | Γ ⊢ A ↮ A' →
  Σ ;; Ξ | Γ ,, A ⊢ B ↮ B' →
  Σ ;; Ξ | Γ ⊢ Pi A B ↮ Pi A' B'.
Proof.
  intros hA hB.
  transitivity (Pi A B').
  - eapply equiv_red_ind. 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
  - eapply equiv_red_ind with (f := λ x, Pi x B'). 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
Qed.

Lemma red_lam Σ Ξ Γ A A' t t' :
  Σ ;; Ξ | Γ ⊢ A ↮ A' →
  Σ ;; Ξ | Γ ,, A ⊢ t ↮ t' →
  Σ ;; Ξ | Γ ⊢ lam A t ↮ lam A' t'.
Proof.
  intros hA ht.
  transitivity (lam A t').
  - eapply equiv_red_ind. 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
  - eapply equiv_red_ind with (f := λ x, lam x t'). 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
Qed.

Lemma red_app Σ Ξ Γ u u' v v' :
  Σ ;; Ξ | Γ ⊢ u ↮ u' →
  Σ ;; Ξ | Γ ⊢ v ↮ v' →
  Σ ;; Ξ | Γ ⊢ app u v ↮ app u' v'.
Proof.
  intros hu hv.
  transitivity (app u v').
  - eapply equiv_red_ind. 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
  - eapply equiv_red_ind with (f := λ x, app x v'). 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
Qed.

Lemma conv_equiv Σ Ξ Γ u v :
  Σ ;; Ξ | Γ ⊢ u ≡ v →
  Σ ;; Ξ | Γ ⊢ u ↮ v.
Proof.
  intros h.
  induction h using conversion_ind.
  all: try solve [ econstructor ; econstructor ; eauto ].
  - eapply red_Pi. all: eassumption.
  - eapply red_lam. all: eassumption.
  - eapply red_app. all: eassumption.
  - admit.
Admitted.
