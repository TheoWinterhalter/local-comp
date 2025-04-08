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
    | const c ξ => κ c ξ (* (map (map inline) ξ) *)
    | assm M x => assm M x
    end

  where "⟦ t ⟧" := (inline t).

  Notation "⟦ l ⟧*" := (map inline l).

  (* Notation "⟦ k ⟧×" := (map (map inline) k). *)

  Definition gren :=
    ∀ ρ c ξ, ρ ⋅ κ c ξ = κ c (ren_eargs ρ ξ).

  Context (hren : gren).

  Lemma inline_ren ρ t :
    ⟦ ρ ⋅ t ⟧ = ρ ⋅ ⟦ t ⟧.
  Proof.
    induction t in ρ |- * using term_rect.
    all: solve [ cbn ; f_equal ; eauto ].
  Qed.

  Lemma up_term_inline σ n :
    (up_term_term (σ >> inline)) n = (up_term_term σ >> inline) n.
  Proof.
    rasimpl. destruct n.
    - reflexivity.
    - cbn. unfold core.funcomp. rewrite inline_ren. reflexivity.
  Qed.

  Definition gsubst :=
    ∀ σ c ξ, (κ c ξ) <[ σ >> inline ] = κ c (subst_eargs σ ξ).

  Context (hsubst : gsubst).

  Lemma inline_subst σ t :
    ⟦ t <[ σ ] ⟧ = ⟦ t ⟧ <[ σ >> inline ].
  Proof.
    induction t in σ |- * using term_rect.
    all: try solve [ cbn ; f_equal ; eauto ].
    - cbn. f_equal. 1: eauto.
      rewrite IHt2. eapply ext_term. intro.
      rewrite up_term_inline. reflexivity.
    - cbn. f_equal. 1: eauto.
      rewrite IHt2. eapply ext_term. intro.
      rewrite up_term_inline. reflexivity.
  Qed.

  (* Lemma inline_einst ξ t :
    ⟦ einst ξ t ⟧ = einst ⟦ ξ ⟧× ⟦ t ⟧.
  Proof.
    induction t in ξ |- * using term_rect.
    all: try solve [ cbn ; f_equal ; eauto ].
    - cbn. f_equal. 1: eauto.
      rewrite IHt2. admit.
    - admit.
    - cbn. (* Would this be true? *)
  Abort. *)

  Definition gcond' :=
    ∀ c Ξ' A t Γ ξ,
      Σ c = Some (Def Ξ' A t) →
      inst_typing Σ [] Γ ξ Ξ' →
      [] ;; [] | ⟦ Γ ⟧* ⊢ κ c ξ : ⟦ einst ξ A ⟧.

  Context (hκ : gcond').

  Lemma typing_inline Γ t A :
    Σ ;; [] | Γ ⊢ t : A →
    [] ;; [] | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ : ⟦ A ⟧.
  Proof.
    intros h.
    induction h using typing_ind.
    all: try solve [ cbn ; tttype ].
    - cbn. rewrite inline_ren. econstructor.
      rewrite nth_error_map. rewrite H. reflexivity.
    - cbn in *. eapply meta_conv.
      + tttype.
      + rewrite inline_subst. apply ext_term. intros []. all: reflexivity.
    - cbn. eapply hκ. all: eassumption.
    - cbn. discriminate.
    - econstructor. 1,3: eassumption.
      admit.
  Admitted.

End Inline.

Notation "⟦ t ⟧⟨ k ⟩" := (inline k t) (at level 0).
Notation "⟦ l ⟧*⟨ k ⟩" := (map (inline k) l).
(* Notation "⟦ t ⟧×⟨ k ⟩" := (map (map (inline k)) t). *)

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

Lemma gwf_gren Σ :
  gwf Σ →
  gren ⟦ Σ ⟧κ.
Proof.
  intros h ρ c ξ.
  induction h as [ | c' ?????? ih | c' ??????? ih ] in ρ, c, ξ |- *.
  - reflexivity.
  - cbn. eauto.
  - cbn. unfold gcons. destruct (_ =? _)%string eqn:e.
    + rewrite <- inline_ren. 2: eauto.
      rewrite ren_inst. rewrite closed_ren.
      2:{ eapply typing_scoped with (Γ := []). eassumption. }
      reflexivity.
    + eauto.
Qed.

Lemma gwf_gsubst Σ :
  gwf Σ →
  gsubst ⟦ Σ ⟧κ.
Proof.
  intros h σ c ξ.
  induction h as [ | c' ?????? ih | c' ??????? ih ] in σ, c, ξ |- *.
  - reflexivity.
  - cbn. eauto.
  - cbn. destruct (c =? c')%string eqn:e.
    + rewrite gcons_eq. 2: assumption.
      erewrite <- subst_inst_closed.
      2:{ eapply typing_scoped with (Γ := []). eassumption. }
      rewrite inline_subst. 3: eauto.
      2:{ eapply gwf_gren. eassumption. }
      apply ext_term. intro n.
      unfold core.funcomp.
      (* We need some form of irrelevance, but we need more info. *)
      admit.
    + rewrite gcons_neq. 2: assumption.
      rewrite <- ih.
      apply ext_term. intro n.
      unfold core.funcomp.
      (* Same here *)
      admit.
Abort.

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
  intro h. intros c Ξ' A t Γ ξ e hξ.
  induction h in c, Ξ', A, t, ξ, e, hξ |- *.
  1:{ cbn in e. discriminate. }
  - cbn in e |- *. destruct (_ =? _)%string eqn:ec.
    1:{ apply eqb_eq in ec. subst. congruence. }
    eapply IHh.
    + eassumption.
    + (* Global context mismatch here too! *)
      admit.
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
    + eapply gwf_gren. assumption.
    + admit.
    + eapply gcond_gcond'. eassumption.
    + eapply typing_einst_closed. all: eassumption.
Abort.
