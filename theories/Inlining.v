(** Inlining

  Here we prove one of the main results about our theory: that it is a
  conservative extension of MLTT.

**)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing BasicMetaTheory.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Section Inline.

  Context (Σ : gctx).
  Context (κ : gref → eargs → term).

  Reserved Notation "⟦ t ⟧⟨ e ⟩" (at level 0).

  Fixpoint inline (χ : eargs) (t : term) :=
    match t with
    | var n => var n
    | Sort i => Sort i
    | Pi A B => Pi ⟦ A ⟧⟨ χ ⟩ ⟦ B ⟧⟨ χ ⟩
    | lam A t => lam ⟦ A ⟧⟨ χ ⟩ ⟦ t ⟧⟨ χ ⟩
    | app u v => app ⟦ u ⟧⟨ χ ⟩ ⟦ v ⟧⟨ χ ⟩
    | const c ξ => κ c (map (map (inline χ)) ξ)
    | assm M x => eget χ M x
    end

  where "⟦ t ⟧⟨ e ⟩" := (inline e t).

  Notation "⟦ l ⟧*⟨ e ⟩" := (map (inline e) l).

  Notation "⟦ k ⟧⟪ e ⟫" := (map (map (inline e)) k).

  (* For now, wrong on purpose *)

  Definition econd Ξ χ :=
    ∀ M x E ξ Ξ' Δ R A Γ,
      ectx_get Ξ M = Some (E, ξ) →
      Σ E = Some (Ext Ξ' Δ R) →
      nth_error Δ x = Some A →
      [] ;; [] | ⟦ Γ ⟧*⟨ χ ⟩ ⊢ eget χ M x : ⟦ delocal M (einst ξ (plus (S x) ⋅ A)) ⟧⟨ χ ⟩.

  Definition gcond :=
    ∀ Ξ c Ξ' A t Γ ξ χ,
      econd Ξ χ →
      Σ c = Some (Def Ξ' A t) →
      [] ;; [] | ⟦ Γ ⟧*⟨ χ ⟩ ⊢ κ c ⟦ ξ ⟧⟪ χ ⟫ : ⟦ einst ξ A ⟧⟨ χ ⟩.

  Context (hκ : gcond).

  Lemma typing_inline Ξ Γ t A χ :
    econd Ξ χ →
    Σ ;; Ξ | Γ ⊢ t : A →
    [] ;; [] | ⟦ Γ ⟧*⟨ χ ⟩ ⊢ ⟦ t ⟧⟨ χ ⟩ : ⟦ A ⟧⟨ χ ⟩.
  Proof.
    intros hχ h.
    induction h in χ, hχ |- * using typing_ind.
    all: try solve [ cbn ; tttype ].
    - cbn. admit.
    - cbn. admit.
    - cbn. eapply hκ. all: eassumption.
    - cbn. eapply hχ. all: eassumption.
    - econstructor. 1,3: eauto.
      admit.
  Admitted.

End Inline.

Notation "⟦ t ⟧⟨ k | c ⟩" := (inline k c t) (at level 0).
Notation "⟦ l ⟧*⟨ k | e ⟩" := (map (inline k e) l).
Notation "⟦ t ⟧⟪ k | e ⟫" := (map (map (inline k e)) t).

Reserved Notation "⟦ s ⟧κ" (at level 0).

Definition gnil (c : gref) (χ : eargs) :=
  dummy.

Definition gcons r f κ (c : gref) (χ : eargs) : term :=
  if (c =? r)%string then f χ else κ c χ.

Fixpoint inline_gctx Σ :=
  match Σ with
  | (c, d) :: Σ =>
    let κ := ⟦ Σ ⟧κ in
    match d with
    | Def Ξ A t => gcons c (λ χ, ⟦ t ⟧⟨ κ | χ ⟩) κ
    | _ => κ
    end
  | [] => gnil
  end
where "⟦ s ⟧κ" := (inline_gctx s).

Lemma gwf_gcond Σ :
  gwf Σ →
  gcond Σ ⟦ Σ ⟧κ.
Proof.
  intro h. intros Ξ c Ξ' A t Γ ξ χ hχ e.
  induction h.
  1:{ cbn in e. discriminate. }
  - cbn in *. destruct (_ =? _)%string eqn:ec.
    1:{ apply eqb_eq in ec. subst. congruence. }
    apply IHh. 2: assumption.
    admit.
  - admit.
Abort.
