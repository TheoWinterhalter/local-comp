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

(* TODO MOVE *)

Inductive OnOne2 {A} (R : A → A → Prop) : list A → list A → Prop :=
| OnOne2_hd a a' l : R a a' → OnOne2 R (a :: l) (a' :: l)
| OnOne2_tl a l l' : OnOne2 R l l' → OnOne2 R (a :: l) (a :: l').

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

  | red_const c ξ ξ' :
      OnOne2 (OnOne2 (λ u v, Γ ⊢ u ↦ v)) ξ ξ' →
      Γ ⊢ const c ξ ↦ const c ξ'

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

(** Notion of confluence **)

Definition red_confluent Σ Ξ :=
  ∀ Γ t u v,
    Σ ;; Ξ | Γ ⊢ t ↦* u →
    Σ ;; Ξ | Γ ⊢ t ↦* v →
    ∃ w,
      Σ ;; Ξ | Γ ⊢ u ↦* w ∧
      Σ ;; Ξ | Γ ⊢ v ↦* w.

(** Joinability **)

Definition joinable Σ Ξ Γ u v :=
  ∃ w,
    Σ ;; Ξ | Γ ⊢ u ↦* w ∧
    Σ ;; Ξ | Γ ⊢ v ↦* w.

Notation "Σ ;; Ξ | Γ ⊢ u ⋈ v" :=
  (joinable Σ Ξ Γ u v)
  (at level 80, u, v at next level).

(** Assuming confluence, equivalence is the same as joinability **)

Lemma equiv_join Σ Ξ Γ u v :
  red_confluent Σ Ξ →
  Σ ;; Ξ | Γ ⊢ u ↮ v →
  Σ ;; Ξ | Γ ⊢ u ⋈ v.
Proof.
  intros hc h.
  induction h as [u v hr | u | u v h ih | u v w h1 ih1 h2 ih2 ].
  - exists v. split.
    + apply rt_step. assumption.
    + apply rt_refl.
  - exists u. split. all: apply rt_refl.
  - destruct ih as [w [h1 h2]]. exists w. intuition auto.
  - destruct ih1 as [w1 [? hv1]], ih2 as [w2 [hv2 ?]].
    eapply hc in hv1 as hw. specialize hw with (1 := hv2).
    destruct hw as [w3 []].
    exists w3. split.
    + eapply rt_trans. all: eassumption.
    + eapply rt_trans. all: eassumption.
Qed.

(** Conversion is included in the congruence closure of reduction **)

Lemma equiv_Pi Σ Ξ Γ A A' B B' :
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

Lemma equiv_lam Σ Ξ Γ A A' t t' :
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

Lemma equiv_app Σ Ξ Γ u u' v v' :
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

Lemma Forall2_rst_OnOne2 A (R : relation A) l l' :
  Forall2 R l l' →
  clos_refl_sym_trans _ (OnOne2 R) l l'.
Proof.
  intros h.
  induction h as [| x y l l' h hl ih].
  - apply rst_refl.
  - eapply rst_trans.
    + apply rst_step. constructor. eassumption.
    + eapply rst_step_ind. 2: eassumption.
      intros. eapply rst_step. constructor. assumption.
Qed.

Lemma OnOne2_rst_comm A R l l' :
  OnOne2 (clos_refl_sym_trans A R) l l' →
  clos_refl_sym_trans _ (OnOne2 R) l l'.
Proof.
  intros h.
  induction h as [| x l l' hl ih].
  - eapply rst_step_ind with (f := λ z, z :: l). 2: eassumption.
    intros. apply rst_step. constructor. assumption.
  - eapply rst_step_ind. 2: eassumption.
    intros. apply rst_step. constructor. assumption.
Qed.

Lemma clos_refl_sym_trans_incl A R R' :
  inclusion A R R' →
  inclusion A (clos_refl_sym_trans A R) (clos_refl_sym_trans A R').
Proof.
  intros hR x y h.
  eapply rst_step_ind with (f := λ x, x). 2: eassumption.
  intros. apply rst_step. eauto.
Qed.

Lemma equiv_const Σ Ξ Γ c ξ ξ' :
  Forall2 (Forall2 (λ u v, Σ ;; Ξ | Γ ⊢ u ↮ v)) ξ ξ' →
  Σ ;; Ξ | Γ ⊢ const c ξ ↮ const c ξ'.
Proof.
  intros hξ.
  eapply Forall2_impl in hξ. 2: eapply Forall2_rst_OnOne2.
  eapply Forall2_impl in hξ.
  2:{ eapply clos_refl_sym_trans_incl. intros ??. eapply OnOne2_rst_comm. }
  eapply Forall2_impl in hξ. 2: eapply Operators_Properties.clos_rst_idempotent.
  eapply Forall2_rst_OnOne2 in hξ.
  eapply clos_refl_sym_trans_incl in hξ.
  2:{ intros ??. eapply OnOne2_rst_comm. }
  eapply Operators_Properties.clos_rst_idempotent in hξ.
  eapply rst_step_ind. 2: eassumption.
  intros. apply rst_step.
  constructor. assumption.
Qed.

Lemma conv_equiv Σ Ξ Γ u v :
  Σ ;; Ξ | Γ ⊢ u ≡ v →
  Σ ;; Ξ | Γ ⊢ u ↮ v.
Proof.
  intros h.
  induction h using conversion_ind.
  all: try solve [ econstructor ; econstructor ; eauto ].
  - eapply equiv_Pi. all: eassumption.
  - eapply equiv_lam. all: eassumption.
  - eapply equiv_app. all: eassumption.
  - eapply equiv_const. assumption.
Qed.
