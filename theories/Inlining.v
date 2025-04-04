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
  Context (χ : eref → aref → term).

  Reserved Notation "⟦ t ⟧" (at level 0).

  Fixpoint inline (t : term) :=
    match t with
    | var n => var n
    | Sort i => Sort i
    | Pi A B => Pi ⟦ A ⟧ ⟦ B ⟧
    | lam A t => lam ⟦ A ⟧ ⟦ t ⟧
    | app u v => app ⟦ u ⟧ ⟦ v ⟧
    | const c ξ => κ c (map (map (inline)) ξ)
    | assm M x => χ M x
    end

  where "⟦ t ⟧" := (inline t).

  Notation "⟦ l ⟧*" := (map inline l).

  Definition ginst :=
    ∀ c Ξ' A t Γ ξ,
      Σ c = Some (Def Ξ' A t) →
      gnil ;; [] | Γ ⊢ κ c (map (map inline) ξ) : ⟦ einst ξ A ⟧.

  Context (hκ : ginst).

  Lemma typing_inline Γ t A :
    Σ ;; Ξ | Γ ⊢ t : A →
    gnil ;; [] | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ : ⟦ A ⟧.
  Proof.
    intro h.
    induction h using typing_ind.
    all: try solve [ cbn ; tttype ].
    - cbn. admit.
    - cbn. admit.
    - cbn. eapply hκ. eassumption.
    - cbn. admit.
    - econstructor. 1,3: eassumption.
      admit.
  Admitted.

End Inline.
