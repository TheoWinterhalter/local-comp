(** Basic meta-theory **)

From Coq Require Import Utf8 List.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

(** Util **)

Lemma meta_conv :
  ∀ Σ Ξ Γ t A B,
    Σ ;; Ξ | Γ ⊢ t : A →
    A = B →
    Σ ;; Ξ | Γ ⊢ t : B.
Proof.
  intros Σ Ξ Γ t A B h ->. assumption.
Qed.

Lemma meta_conv_trans_l :
  ∀ Σ Ξ Γ u v w,
    u = v →
    Σ ;; Ξ | Γ ⊢ v ≡ w →
    Σ ;; Ξ | Γ ⊢ u ≡ w.
Proof.
  intros Σ Ξ Γ ??? <- h. assumption.
Qed.

Lemma meta_conv_trans_r :
  ∀ Σ Ξ Γ u v w,
    Σ ;; Ξ | Γ ⊢ u ≡ v →
    v = w →
    Σ ;; Ξ | Γ ⊢ u ≡ w.
Proof.
  intros Σ Ξ Γ u v ? h <-. assumption.
Qed.

Lemma meta_conv_refl :
  ∀ Σ Ξ Γ u v,
    u = v →
    Σ ;; Ξ | Γ ⊢ u ≡ v.
Proof.
  intros Σ Ξ Γ u ? <-. ttconv.
Qed.

(** Renaming preserves typing **)

Definition rtyping (Γ : ctx) (ρ : nat → nat) (Δ : ctx) : Prop :=
  ∀ x A,
    nth_error Δ x = Some A →
    ∃ B,
      nth_error Γ (ρ x) = Some B ∧
      (plus (S x) >> ρ) ⋅ A = (plus (S (ρ x))) ⋅ B.

#[export] Instance rtyping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) rtyping.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  intros n A en. rewrite <- e.
  eapply h in en as [B [en eB]].
  eexists. split. 1: eassumption.
  rasimpl. rasimpl in eB. rewrite <- eB.
  apply extRen_term. intro x. cbn. core.unfold_funcomp.
  rewrite <- e. reflexivity.
Qed.

Lemma autosubst_simpl_rtyping :
  ∀ Γ Δ r s,
    RenSimplification r s →
    rtyping Γ r Δ ↔ rtyping Γ s Δ.
Proof.
  intros Γ Δ r s H.
  apply rtyping_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_rtyping : rasimpl_outermost.

Lemma rtyping_shift :
  ∀ Γ Δ A ρ,
    rtyping Γ ρ Δ →
    rtyping (Γ ,, (ρ ⋅ A)) (0 .: ρ >> S) (Δ,, A).
Proof.
  intros Γ Δ A ρ hρ.
  intros y B hy.
  destruct y.
  - cbn in *. inversion hy. eexists.
    split. 1: reflexivity.
    rasimpl. reflexivity.
  - cbn in *. eapply hρ in hy. destruct hy as [C [en eC]].
    eexists. split. 1: eassumption.
    rasimpl.
    apply (f_equal (λ t, S ⋅ t)) in eC. rasimpl in eC.
    assumption.
Qed.

Lemma rtyping_S :
  ∀ Γ A,
    rtyping (Γ ,, A) S Γ.
Proof.
  intros Γ A. intros x B e.
  simpl. rasimpl.
  eexists. split. 1: eassumption.
  rasimpl. reflexivity.
Qed.

Lemma ren_inst :
  ∀ ρ ξ t,
    ρ ⋅ (einst ξ t) = einst (map (map (ren_term ρ)) ξ) (ρ ⋅ t).
Proof.
  intros ρ ξ t.
  induction t in ρ |- *. all: try solve [ eauto ].
  - cbn. f_equal. 1: eauto.
    rewrite IHt2. f_equal.
    (* This is wrong, need to figure out who lives where.
      It seems it doesn't make sense for an argument to einst to feature
      free variables.
    *)
Abort.

Lemma conv_ren :
  ∀ Σ Ξ Γ Δ ρ u v,
    rtyping Γ ρ Δ →
    Σ ;; Ξ | Δ ⊢ u ≡ v →
    Σ ;; Ξ | Γ ⊢ ρ ⋅ u ≡ ρ ⋅ v.
Proof.
  intros Σ Ξ Γ Δ ρ u v hρ h.
  induction h in Γ, ρ, hρ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto using rtyping_shift ].
  - rasimpl. eapply meta_conv_trans_r. 1: econstructor.
    rasimpl. reflexivity.
  - rasimpl. eapply conv_trans. 1: econstructor. 1: eassumption.
    admit. (* The corresponding rule is wrong *)
Admitted.

Lemma typing_ren :
  ∀ Σ Ξ Γ Δ ρ t A,
    rtyping Γ ρ Δ →
    Σ ;; Ξ | Δ ⊢ t : A →
    Σ ;; Ξ | Γ ⊢ ρ ⋅ t : ρ ⋅ A.
Proof.
  intros Σ Ξ Γ Δ ρ t A hρ ht.
  induction ht in Γ, ρ, hρ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto using rtyping_shift ].
  - rasimpl. eapply hρ in H as [B [? eB]].
    rasimpl in eB. rewrite eB.
    econstructor. eassumption.
  - rasimpl. rasimpl in IHht1. rasimpl in IHht4.
    eapply meta_conv. 1: econstructor. all: eauto.
    1:{ eauto using rtyping_shift. }
    rasimpl. reflexivity.
  - rasimpl. eapply meta_conv. 1: econstructor. 1: eassumption.
    (* TODO: Prove a stronger induction principle that also concludes on
      inst_typing *)
    all: admit.
  - rasimpl. eapply meta_conv.
    1:{ econstructor. all: eassumption. }
    admit.
  - rasimpl. rasimpl in IHht2.
    econstructor. all: eauto.
    eapply conv_ren. all: eassumption.
Admitted.
