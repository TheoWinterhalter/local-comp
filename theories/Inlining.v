(** Inlining

  Here we prove one of the main results about our theory: that it is a
  conservative extension of MLTT.

  We do so by inlining global definitions inside a term.

  We represent MLTT by out type theory where both global (Σ) and extension (Ξ)
  environments are empty.

  By doing this, we get more than by going through ETT: typically we don't need
  any form of UIP or funext, or even of equality!

**)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing BasicMetaTheory.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

#[local] Notation ginst := (gref → eargs → term).

Section Inline.

  Context (Σ : gctx).
  Context (κ : ginst).

  Reserved Notation "⟦ t ⟧" (at level 0).

  Fixpoint inline (t : term) :=
    match t with
    | var n => var n
    | Sort i => Sort i
    | Pi A B => Pi ⟦ A ⟧ ⟦ B ⟧
    | lam A t => lam ⟦ A ⟧ ⟦ t ⟧
    | app u v => app ⟦ u ⟧ ⟦ v ⟧
    | const c ξ => κ c (map (map inline) ξ)
    | assm M x => assm M x
    end

  where "⟦ t ⟧" := (inline t).

  Notation "⟦ l ⟧*" := (map inline l).

  Notation "⟦ k ⟧×" := (map (map inline) k).

  Definition gren :=
    ∀ ρ c ξ, ρ ⋅ κ c ξ = κ c (ren_eargs ρ ξ).

  Context (hren : gren).

  Lemma inline_ren ρ t :
    ⟦ ρ ⋅ t ⟧ = ρ ⋅ ⟦ t ⟧.
  Proof.
    induction t in ρ |- * using term_rect.
    all: try solve [ cbn ; f_equal ; eauto ].
    cbn. rewrite hren. f_equal.
    rewrite !map_map. apply map_ext_All.
    eapply All_impl. 2: eassumption.
    intros σ h.
    rewrite !map_map. apply map_ext_All.
    eapply All_impl. 2: eassumption.
    cbn. auto.
  Qed.

  Lemma inline_einst ξ t :
    ⟦ einst ξ t ⟧ = einst ⟦ ξ ⟧× ⟦ t ⟧.
  Proof.
    induction t in ξ |- * using term_rect.
    all: try solve [ cbn ; f_equal ; eauto ].
    - cbn. f_equal. 1: eauto.
      rewrite IHt2. admit.
    - admit.
    - cbn. (* Would this be true? *)
  Abort.

  Definition gcond' :=
    ∀ c Ξ' A t Γ ξ,
      Σ c = Some (Def Ξ' A t) →
      [] ;; [] | ⟦ Γ ⟧* ⊢ κ c ⟦ ξ ⟧× : ⟦ einst ξ A ⟧.

  Context (hκ : gcond').

  Lemma typing_inline Γ t A :
    Σ ;; [] | Γ ⊢ t : A →
    [] ;; [] | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ : ⟦ A ⟧.
  Proof.
    intros h.
    induction h using typing_ind.
    all: try solve [ cbn ; tttype ].
    - cbn. admit.
    - cbn. admit.
    - cbn. eapply hκ. eassumption.
    - cbn. discriminate.
    - econstructor. 1,3: eassumption.
      admit.
  Admitted.

End Inline.

Notation "⟦ t ⟧⟨ k ⟩" := (inline k t) (at level 0).
Notation "⟦ l ⟧*⟨ k ⟩" := (map (inline k) l).
Notation "⟦ t ⟧×⟨ k ⟩" := (map (map (inline k)) t).

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
    | Def Ξ A t => gcons c (λ ξ, ⟦ einst ξ t ⟧⟨ κ ⟩) κ
    | _ => κ
    end
  | [] => gnil
  end
where "⟦ s ⟧κ" := (inline_gctx s).

Lemma gcons_eq c c' f κ :
  (c' =? c)%string = true →
  gcons c f κ c' = f.
Proof.
  intro h.
  unfold gcons. rewrite h. reflexivity.
Qed.

Lemma gcons_neq c c' f κ :
  (c' =? c)%string = false →
  gcons c f κ c' = κ c'.
Proof.
  intro h.
  unfold gcons. rewrite h. reflexivity.
Qed.

Lemma get_gren Σ :
  gren ⟦ Σ ⟧κ.
Proof.
  intros ρ c ξ.
  induction Σ as [| [r []] Σ ih] in ρ, c, ξ |- *.
  - reflexivity.
  - cbn. eauto.
  - cbn. unfold gcons. destruct (_ =? _)%string eqn:e.
    + rewrite <- inline_ren. 2: eauto.
      rewrite ren_inst. f_equal. f_equal.
      admit.
    + eauto.
Admitted.

Inductive gcond : gctx → ginst → Prop :=
| gcond_nil : gcond [] gnil

| gcond_ext c Σ κ Ξ Δ R :
    gcond Σ κ →
    gcond ((c, Ext Ξ Δ R) :: Σ) κ

| gcond_def c Σ κ Ξ A t :
    gcond Σ κ →
    (∀ ξ,
      inst_typing Σ [] ∙ ξ Ξ →
      [] ;; [] | ∙ ⊢ ⟦ einst ξ t ⟧⟨ κ ⟩ : ⟦ einst ξ A ⟧⟨ κ ⟩
    ) →
    gcond ((c, Def Ξ A t) :: Σ) (gcons c (λ ξ, ⟦ einst ξ t ⟧⟨ κ ⟩) κ).

Lemma gcond_gcond' Σ κ :
  gcond Σ κ →
  gcond' Σ κ.
Proof.
  intro h. intros c Ξ' A t Γ ξ e.
  induction h in c, Ξ', A, t, ξ, e |- *.
  1:{ cbn in e. discriminate. }
  - cbn in e |- *. destruct (_ =? _)%string eqn:ec.
    1:{ apply eqb_eq in ec. subst. congruence. }
    eapply IHh. eassumption.
  - cbn in e |- *. destruct (_ =? _)%string eqn:ec.
    + inversion e. subst. clear e.
      rewrite gcons_eq. 2: eassumption.
      eapply typing_lift_closed. 2: admit.
      eapply meta_conv.
      * eapply H. admit.
      * admit.
    + rewrite gcons_neq. 2: eassumption.
      admit.
Admitted.

Lemma gwf_gcond Σ :
  gwf Σ →
  gcond Σ ⟦ Σ ⟧κ.
Proof.
  intro h.
  induction h as [ | c' ?????? ih | c' ??????? ih ].
  - constructor.
  - cbn. constructor. assumption.
  - cbn. constructor. 1: assumption.
    intros ξ hξ.
    eapply typing_inline with (Γ := ∙).
    + eapply get_gren.
    + eapply gcond_gcond'. eassumption.
    + eapply typing_einst_closed. all: eassumption.
Qed.
