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

  Context (Σ : gctx) (Ξ : ectx).
  Context (κ : gref → eargs → term).
  Context (χ : eargs).

  Reserved Notation "⟦ t ⟧" (at level 0).

  Fixpoint inline (t : term) :=
    match t with
    | var n => var n
    | Sort i => Sort i
    | Pi A B => Pi ⟦ A ⟧ ⟦ B ⟧
    | lam A t => lam ⟦ A ⟧ ⟦ t ⟧
    | app u v => app ⟦ u ⟧ ⟦ v ⟧
    | const c ξ => κ c (map (map (inline)) ξ)
    | assm M x => eget χ M x
    end

  where "⟦ t ⟧" := (inline t).

  Notation "⟦ l ⟧*" := (map inline l).

  (* For now, wrong on purpose *)

  Definition gcond :=
    ∀ c Ξ' A t Γ ξ,
      Σ c = Some (Def Ξ' A t) →
      [] ;; [] | Γ ⊢ κ c (map (map inline) ξ) : ⟦ einst ξ A ⟧.

  Context (hκ : gcond).

  Definition econd :=
    ∀ M x E ξ Ξ' Δ R A Γ,
      ectx_get Ξ M = Some (E, ξ) →
      Σ E = Some (Ext Ξ' Δ R) →
      nth_error Δ x = Some A →
      [] ;; [] | Γ ⊢ eget χ M x : ⟦ delocal M (einst ξ (plus (S x) ⋅ A)) ⟧.

  Context (hχ : econd).

  Lemma typing_inline Γ t A :
    Σ ;; Ξ | Γ ⊢ t : A →
    [] ;; [] | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ : ⟦ A ⟧.
  Proof.
    intro h.
    induction h using typing_ind.
    all: try solve [ cbn ; tttype ].
    - cbn. admit.
    - cbn. admit.
    - cbn. eapply hκ. eassumption.
    - cbn. eapply hχ. all: eassumption.
    - econstructor. 1,3: eassumption.
      admit.
  Admitted.

End Inline.

Notation "⟦ t ⟧⟨ k | c ⟩" := (inline k c t) (at level 0).

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
