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
  rewrite Forall_forall. intros o ho.
  eapply In_nth_error in ho as [x hx].
  destruct o as [u |]. 2: constructor.
  constructor.
  destruct ih as [heq [ih e]]. red in ih. specialize (ih x).
  destruct (ictx_get Ξ' x) as [[] |] eqn:e'.
  3:{
    unfold ictx_get in e'. destruct (_ <=? _) eqn: e1.
    - rewrite Nat.leb_le in e1. rewrite <- e in e1.
      rewrite <- nth_error_None in e1. congruence.
    - rewrite nth_error_None in e'.
      rewrite Nat.leb_gt in e1. lia.
    }
    2:{
      specialize (heq _ _ e'). cbn in heq. intuition congruence.
    }
    specialize ih with (1 := eq_refl).
    unfold iget in ih. rewrite hx in ih.
    apply ih.
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
  - intros x A hx. specialize (ht _ _ hx) as [].
    split. 1: assumption.
    unfold iget in *. 
    destruct (nth_error ξ _) as [[] |] eqn:e1. 2,3: constructor.
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
