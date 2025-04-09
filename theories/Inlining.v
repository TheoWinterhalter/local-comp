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

(** Notion of global scoping

  We ignore the fact that [assm] because we consider the case where [Ξ] is
  empty.

**)

Inductive gscope (Σ : gctx) : term → Prop :=
| gscope_var x : gscope Σ (var x)
| gscope_sort i : gscope Σ (Sort i)
| gscope_pi A B : gscope Σ A → gscope Σ B → gscope Σ (Pi A B)
| gscope_lam A t : gscope Σ A → gscope Σ t → gscope Σ (lam A t)
| gscope_app u v : gscope Σ u → gscope Σ v → gscope Σ (app u v)
| gscope_const c ξ Ξ' A t :
    Σ c = Some (Def Ξ' A t) →
    Forall (Forall (gscope Σ)) ξ →
    gscope Σ (const c ξ).

Lemma typing_gscope Σ Γ t A :
  Σ ;; [] | Γ ⊢ t : A →
  gscope Σ t.
Proof.
  intro h. induction h using typing_ind.
  all: try solve [ econstructor ; eauto ].
  - econstructor. 1: eassumption.
    rewrite Forall_forall. intros σ hσ.
    rewrite Forall_forall. intros u hu.
    eapply In_nth_error in hσ as [M hM].
    eapply In_nth_error in hu as [x hx].
    destruct H1 as [_ [ih e]]. red in ih. specialize (ih M).
    destruct (ectx_get Ξ' M) as [[E ξ'] |] eqn:e'.
    2:{
      unfold ectx_get in e'. destruct (_ <=? _) eqn: e1.
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
    unfold eget in ih. rewrite hM, hx in ih.
    assumption.
  - discriminate.
  - assumption.
Qed.

(** Inlining **)

#[local] Notation ginst := (gref → eargs → term).

Section Inline.

  Context (Σ : gctx).
  Context (κ : ginst).

  Reserved Notation "⟦ t ⟧" (at level 0).
  Reserved Notation "⟦ k ⟧×" (at level 0).

  Fixpoint inline (t : term) :=
    match t with
    | var n => var n
    | Sort i => Sort i
    | Pi A B => Pi ⟦ A ⟧ ⟦ B ⟧
    | lam A t => lam ⟦ A ⟧ ⟦ t ⟧
    | app u v => app ⟦ u ⟧ ⟦ v ⟧
    | const c ξ => κ c ⟦ ξ ⟧×
    | assm M x => assm M x
    end

  where "⟦ t ⟧" := (inline t)
  and "⟦ k ⟧×" := (map (map inline) k).

  Notation "⟦ l ⟧*" := (map inline l).

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

  Lemma up_term_inline σ n :
    (up_term_term (σ >> inline)) n = (up_term_term σ >> inline) n.
  Proof.
    rasimpl. destruct n.
    - reflexivity.
    - cbn. unfold core.funcomp. rewrite inline_ren. reflexivity.
  Qed.

  Definition gsubst :=
    ∀ σ c ξ, (κ c ξ) <[ σ ] = κ c (subst_eargs σ ξ).

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
    - cbn. rewrite hsubst. f_equal.
      rewrite !map_map. apply map_ext_All.
      eapply All_impl. 2: eassumption.
      intros ? h.
      rewrite !map_map. apply map_ext_All.
      eapply All_impl. 2: eassumption.
      cbn. auto.
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

  Definition g_unfold :=
    ∀ Γ c ξ Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      [] ;; [] | ⟦ Γ ⟧* ⊢ κ c ⟦ ξ ⟧× ≡ ⟦ einst ξ t ⟧.

  Context (hufd : g_unfold).

  Definition g_cong :=
    ∀ Γ c ξ ξ',
      Forall2 (Forall2 (conversion [] [] Γ)) ξ ξ' →
      [] ;; [] | Γ ⊢ κ c ξ ≡ κ c ξ'.

  Context (hcong : g_cong).

  Lemma conv_inline Γ u v :
    Σ ;; [] | Γ ⊢ u ≡ v →
    [] ;; [] | ⟦ Γ ⟧* ⊢ ⟦ u ⟧ ≡ ⟦ v ⟧.
  Proof.
    intros h.
    induction h using conversion_ind.
    all: try solve [ cbn ; ttconv ].
    - cbn. rewrite inline_subst. eapply meta_conv_trans_r. 1: econstructor.
      apply ext_term. intros []. all: reflexivity.
    - cbn. eapply hufd. eassumption.
    - discriminate.
    - cbn. apply hcong.
      apply Forall2_map_l, Forall2_map_r.
      eapply Forall2_impl. 2: eassumption.
      intros. apply Forall2_map_l, Forall2_map_r.
      eapply Forall2_impl. 2: eassumption.
      cbn. auto.
    - econstructor. assumption.
    - eapply conv_trans. all: eassumption.
  Qed.

  Definition gcond' :=
    ∀ c Ξ' A t Γ ξ,
      Σ c = Some (Def Ξ' A t) →
      inst_typing Σ [] Γ ξ Ξ' →
      [] ;; [] | ⟦ Γ ⟧* ⊢ κ c ⟦ ξ ⟧× : ⟦ einst ξ A ⟧.

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
      eapply conv_inline. assumption.
  Qed.

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
      (* We need to know σ has already been inlined I guess? *)
      admit.
    + rewrite gcons_neq. 2: assumption.
      rewrite <- ih. reflexivity.
Abort.

Lemma gwf_unfold Σ :
  gwf Σ →
  g_unfold Σ ⟦ Σ ⟧κ.
Proof.
  intros h Γ c ξ Ξ' A t hc.
  induction h as [ | c' ?????? ih | c' ??????? ih ] in Γ, c, ξ, Ξ', A, t, hc |- *.
  - discriminate.
  - cbn. admit.
  - cbn. admit.
Admitted.

Lemma gwf_cong Σ :
  gwf Σ →
  g_cong ⟦ Σ ⟧κ.
Proof.
  intros h Γ c ξ ξ' e.
  induction h as [ | c' ?????? ih | c' ??????? ih ] in Γ, c, ξ, ξ', e |- *.
  - cbn. constructor.
  - cbn. eapply ih.
    (* This is really problematic because this is strengthening we need! *)
    admit.
  - cbn. admit.
Admitted.

Inductive gcond : gctx → ginst → Prop :=
| gcond_nil : gcond [] gnil

| gcond_ext c Σ κ Ξ Δ R :
    gcond Σ κ →
    gcond ((c, Ext Ξ Δ R) :: Σ) κ

| gcond_def c Σ κ Ξ A t :
    gcond Σ κ →
    (∀ Γ Σ' ξ,
      Σ ⊑ Σ' →
      inst_typing Σ' [] Γ ξ Ξ →
      [] ;; [] | ⟦ Γ ⟧*⟨ κ ⟩ ⊢ ⟦ einst ξ t ⟧⟨ κ ⟩ : ⟦ einst ξ A ⟧⟨ κ ⟩
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
      eapply meta_conv.
      * admit.
      * admit.
    + rewrite gcons_neq. 2: eassumption.
      admit.
Admitted.

Lemma inline_ext_gscope Σ t κ κ' :
  gscope Σ t →
  (∀ c Ξ' A t ξ, Σ c = Some (Def Ξ' A t) → κ c ⟦ ξ ⟧×⟨ κ ⟩ = κ' c ⟦ ξ ⟧×⟨ κ' ⟩) →
  ⟦ t ⟧⟨ κ ⟩ = ⟦ t ⟧⟨ κ' ⟩.
Proof.
  intros ht he.
  induction ht in κ, κ', he |- *.
  all: try solve [ cbn ; eauto ].
  all: solve [ cbn ; f_equal ; eauto ].
Qed.

Lemma gwf_get Σ c ξ Ξ' A t :
  gwf Σ →
  Σ c = Some (Def Ξ' A t) →
  ⟦ Σ ⟧κ c ξ = ⟦ einst ξ t ⟧⟨ ⟦ Σ ⟧κ ⟩.
Proof.
  intros h hc.
  induction h as [ | c' ?????? ih | c' ??????? ih ] in c, Ξ', A, t, hc |- *.
  - discriminate.
  - cbn. cbn in hc. destruct (_ =? _)%string eqn:ec.
    1:{ apply eqb_eq in ec. subst. congruence. }
    eauto.
  - cbn in hc |- *. destruct (_ =? _)%string eqn:ec.
    + inversion hc. subst. clear hc.
      rewrite gcons_eq. 2: eassumption.
      eapply inline_ext_gscope.
      (* If we ask for ξ to be well typed, we get back the issue of it being in
        a future context.

        In fact, this is much more serious than that! The current definition of
        ⟦ Σ ⟧κ is wrong because it uses the wrong κ! It's enough for t but not
        for ξ.

        Because I'm tempted to go back to the weird situation where ξ gets
        inlined twice, with the second time being useless.

        Or we go a third way and parametrise the translation by a ξ.
        The problem is that I would like to avoid reimplementing (and proving)
        einst again.
      *)
      1:{ eapply typing_gscope. admit. }
      intros ????? e.
      admit.
    + admit.
Abort.

Lemma gwf_gcond' Σ :
  gwf Σ →
  gcond' Σ ⟦ Σ ⟧κ.
Proof.
  intro h. intros c Ξ' A t Γ ξ e hξ.
Abort.

Lemma gwf_gcond Σ :
  gwf Σ →
  gcond Σ ⟦ Σ ⟧κ.
Proof.
  intro h.
  induction h as [ | c' ?????? ih | c' ??????? ih ].
  - constructor.
  - cbn. constructor. assumption.
  - cbn. constructor. 1: assumption.
    intros Γ Σ' ξ hle hξ.
    eapply typing_inline.
    + eapply gwf_gren. assumption.
    + admit.
    + eapply gwf_unfold. assumption.
    + eapply gwf_cong. assumption.
    + eapply gcond_gcond'. eassumption.
    + eapply typing_einst_closed. all: admit.
Abort.

Theorem inlining Σ Γ t A :
  gwf Σ →
  let κ := ⟦ Σ ⟧κ in
  Σ ;; [] | Γ ⊢ t : A →
  [] ;; [] | ⟦ Γ ⟧*⟨ κ ⟩ ⊢ ⟦ t ⟧⟨ κ ⟩ : ⟦ A ⟧⟨ κ ⟩.
Proof.
  intros hΣ κ h.
  eapply typing_inline.
  - eapply gwf_gren. assumption.
  - admit.
  - eapply gwf_unfold. assumption.
  - eapply gwf_cong. assumption.
  - eapply gcond_gcond'. admit.
  - eassumption.
Admitted.

Theorem conservativity Σ t A i :
  gwf Σ →
  [] ;; [] | ∙ ⊢ A : Sort i →
  Σ ;; [] | ∙ ⊢ t : A →
  let κ := ⟦ Σ ⟧κ in
  [] ;; [] | ∙ ⊢ ⟦ t ⟧⟨ κ ⟩ : A.
Proof.
  intros hΣ hA ht κ.
  eapply inlining in ht. 2: assumption.
  cbn in ht.
  (* TODO: Show that inline is the identity on MLTT. *)
  (* Do we use a typing judgment or a global scoping one? *)
Admitted.
