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

Lemma inst_typing_gscope_ih Σ conv ξ Ξ' :
  inst_typing_ conv (λ t _, gscope Σ t) ξ Ξ' →
  gscope_instance Σ ξ.
Proof.
  eauto using inst_typing_prop_ih.
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
  eapply inst_typing_gscope_ih.
  eapply inst_typing_impl; eauto.
  apply typing_gscope.
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

Lemma equation_typing_gscope Σ Ξ r :
  equation_typing Σ Ξ r →
  gscope_equation Σ r.
Proof.
  intros (hctx & [i hty] & hl & hr).
  eapply typing_gscope in hl as gl, hr as gr, hty.
  eapply wf_gscope in hctx.
  unfold gscope_equation. intuition eauto.
Qed.

Lemma equations_typing_gscope Σ Ξ R :
  Forall (equation_typing Σ Ξ) R →
  Forall (gscope_equation Σ) R.
Proof.
  eauto using Forall_impl, equation_typing_gscope.
Qed.
