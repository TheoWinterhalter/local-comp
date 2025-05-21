(** Global scoping

  It tracks whether [c] in [const c ξ] always points to [Σ].
  It doesn't ensure anything about [assm].

  The definition is in [Typing] for dependency reasons.

*)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing BasicMetaTheory.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Lemma inst_typing_gscope_ih Σ Ξ Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ _ t _, gscope Σ t) Γ ξ Ξ' →
  gscope_instance Σ ξ.
Proof.
  intros h ih.
  rewrite Forall_forall. intros σ hσ.
  rewrite Forall_forall. intros u hu.
  eapply In_nth_error in hσ as [M hM].
  eapply In_nth_error in hu as [x hx].
  destruct ih as [_ [ih e]]. red in ih. specialize (ih M).
  destruct (ictx_get Ξ' M) as [[E ξ'] |] eqn:e'.
  2:{
    unfold ictx_get in e'. destruct (_ <=? _) eqn: e1.
    - rewrite Nat.leb_le in e1. rewrite <- e in e1.
      rewrite <- nth_error_None in e1. congruence.
    - rewrite nth_error_None in e'.
      rewrite Nat.leb_gt in e1. lia.
  }
  specialize ih with (1 := eq_refl).
  destruct ih as (hξ' & Ξ'' & Δ & R & hE & eM & ih).
  rewrite hM in eM. cbn in eM.
  destruct (nth_error Δ x) eqn: eΔ.
  2:{
    rewrite nth_error_None in eΔ. rewrite <- eM in eΔ.
    rewrite <- nth_error_None in eΔ. congruence.
  }
  specialize ih with (1 := eΔ).
  unfold iget in ih. rewrite hM, hx in ih.
  assumption.
Qed.

Lemma typing_gscope Σ Ξ Γ t A :
  Σ ;; Ξ | Γ ⊢ t : A →
  gscope Σ t.
Proof.
  intro h. induction h using typing_ind.
  all: try solve [ econstructor ; eauto ].
  - econstructor. 1: eassumption.
    eapply inst_typing_gscope_ih. all: eassumption.
  - assumption.
Qed.

Lemma inst_typing_gscope Σ Ξ Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  gscope_instance Σ ξ.
Proof.
  intros h.
  eapply inst_typing_gscope_ih. 1: eassumption.
  destruct h as (he & ht & e).
  split. 2: split.
  - assumption.
  - intros M E ξ' eM.
    specialize (ht _ _ _ eM). destruct ht as (? & Ξ'' & Δ & R & eE & ho & ht).
    split. 1: assumption.
    eexists _,_,_. split. 1 : eassumption.
    split. 1: assumption.
    intros x A hx. specialize ht with (1 := hx).
    unfold iget in *. destruct (nth_error ξ _) as [σ |] eqn:e1. 2: constructor.
    destruct (nth_error σ _) eqn:e2. 2: constructor.
    eapply typing_gscope. eassumption.
  - assumption.
Qed.

Lemma wf_gscope Σ Ξ Γ :
  wf Σ Ξ Γ →
  Forall (gscope Σ) Γ.
Proof.
  induction 1 as [| Γ i A hΓ ih hA]. 1: constructor.
  econstructor. 2: assumption.
  eapply typing_gscope. eassumption.
Qed.

Definition gscope_equation Σ ε :=
  Forall (gscope Σ) ε.(eq_env) ∧
  gscope Σ ε.(eq_lhs) ∧
  gscope Σ ε.(eq_rhs) ∧
  gscope Σ ε.(eq_typ).

Lemma gscope_apps_inv Σ f l :
  gscope Σ (apps f l) →
  gscope Σ f ∧ Forall (gscope Σ) l.
Proof.
  intros h.
  induction l as [| x l ih] in f, h |- *.
  - cbn in h. intuition constructor.
  - cbn in h. eapply ih in h as [happ hl].
    inversion happ. subst.
    split.
    + assumption.
    + constructor. all: assumption.
Qed.

Lemma equation_typing_gscope Σ Ξ Δ r :
  equation_typing Σ Ξ Δ r →
  gscope_equation Σ r.
Proof.
  intros (hctx & [i hty] & hl & hr).
  eapply typing_gscope in hl as gl, hr as gr, hty.
  eapply wf_gscope in hctx.
  rewrite Forall_app in hctx.
  unfold gscope_equation. intuition eauto.
Qed.

Lemma equations_typing_gscope Σ Ξ Δ R :
  Forall (equation_typing Σ Ξ Δ) R →
  Forall (gscope_equation Σ) R.
Proof.
  eauto using Forall_impl, equation_typing_gscope.
Qed.
