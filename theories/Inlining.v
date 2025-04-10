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

Notation gscope_eargs Σ ξ := (Forall (Forall (gscope Σ)) ξ).

Lemma gscope_ind_alt :
  ∀ Σ (P : term → Prop),
  (∀ x, P (var x)) →
  (∀ i, P (Sort i)) →
  (∀ A B, gscope Σ A → P A → gscope Σ B → P B → P (Pi A B)) →
  (∀ A t, gscope Σ A → P A → gscope Σ t → P t → P (lam A t)) →
  (∀ u v, gscope Σ u → P u → gscope Σ v → P v → P (app u v)) →
  (∀ c ξ Ξ' A t,
    Σ c = Some (Def Ξ' A t) →
    gscope_eargs Σ ξ →
    Forall (Forall P) ξ →
    P (const c ξ)
  ) →
  ∀ t, gscope Σ t → P t.
Proof.
  intros Σ P hvar hsort hpi hlam happ hconst.
  fix aux 2. move aux at top.
  intros t h. destruct h as [| | | | | ????? hc h].
  6:{
    eapply hconst. 1,2: eassumption.
    revert ξ h.
    fix aux1 2.
    intros ξ h. destruct h as [| σ ξ hσ hξ].
    - constructor.
    - constructor. 2: eauto.
      revert σ hσ. fix aux2 2. intros σ hσ.
      destruct hσ as [| u σ h hσ]. 1: constructor.
      constructor. all: eauto.
  }
  all: match goal with h : _ |- _ => solve [ eapply h ; eauto ] end.
Qed.

(** Inlining **)

#[local] Notation ginst := (gref → term).

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
    | const c ξ => einst ⟦ ξ ⟧× (κ c)
    | assm M x => assm M x
    end

  where "⟦ t ⟧" := (inline t)
  and "⟦ k ⟧×" := (map (map inline) k).

  Notation "⟦ l ⟧*" := (map inline l).

  Definition gclosed :=
    ∀ c, closed (κ c) = true.

  Context (hclosed : gclosed).

  Lemma inline_ren ρ t :
    ⟦ ρ ⋅ t ⟧ = ρ ⋅ ⟦ t ⟧.
  Proof.
    induction t in ρ |- * using term_rect.
    all: try solve [ cbn ; f_equal ; eauto ].
    cbn. rewrite ren_inst. rewrite closed_ren. 2: auto.
    f_equal.
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
    - cbn. rewrite subst_inst_closed. 2: auto.
      f_equal.
      rewrite !map_map. apply map_ext_All.
      eapply All_impl. 2: eassumption.
      intros ? h.
      rewrite !map_map. apply map_ext_All.
      eapply All_impl. 2: eassumption.
      cbn. auto.
  Qed.

  Lemma inline_eget ξ M x :
    ⟦ eget ξ M x ⟧ = eget ⟦ ξ ⟧× M x.
  Proof.
    unfold eget. rewrite nth_error_map.
    destruct nth_error as [σ |] eqn: e1. 2: reflexivity.
    cbn. rewrite nth_error_map.
    destruct (nth_error σ _) as [t|] eqn:e2. 2: reflexivity.
    cbn. reflexivity.
  Qed.

  Lemma inline_ren_eargs ρ ξ :
    ⟦ ren_eargs ρ ξ ⟧× = ren_eargs ρ ⟦ ξ ⟧×.
  Proof.
    rewrite !map_map. apply map_ext. intro.
    rewrite !map_map. apply map_ext. intro.
    apply inline_ren.
  Qed.

  Lemma inline_einst ξ t :
    ⟦ einst ξ t ⟧ = einst ⟦ ξ ⟧× ⟦ t ⟧.
  Proof.
    induction t in ξ |- * using term_rect.
    all: try solve [ cbn ; f_equal ; eauto ].
    - cbn. f_equal. 1: eauto.
      rewrite IHt2. rewrite inline_ren_eargs. reflexivity.
    - cbn. f_equal. 1: eauto.
      rewrite IHt2. rewrite inline_ren_eargs. reflexivity.
    - cbn. rewrite einst_einst. f_equal.
      rewrite !map_map. apply map_ext_All.
      eapply All_impl. 2: eassumption.
      intros σ hσ. rewrite !map_map. apply map_ext_All.
      eapply All_impl. 2: eassumption.
      auto.
    - cbn. apply inline_eget.
  Qed.

  Definition g_unfold :=
    ∀ c Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      κ c = ⟦ t ⟧.

  Context (hκ : g_unfold).

  Definition g_conv_unfold :=
    ∀ c Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      Σ ;; Ξ' | ∙ ⊢ κ c ≡ t.

  Context (h_conv_unfold : g_conv_unfold).

  Lemma conv_ren_einst Ξ Γ Δ ρ ξ ξ' :
    Forall2 (Forall2 (conversion Σ Ξ Δ)) ξ ξ' →
    Forall2 (Forall2 (conversion Σ Ξ Γ)) (ren_eargs ρ ξ) (ren_eargs ρ ξ').
  Proof.
    intros h.
    apply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros. apply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros. eapply conv_ren. eassumption.
  Qed.

  Lemma conv_eargs_inline_self Ξ Ξ' Γ ξ :
    inst_typing_ Σ Ξ (λ Γ t _, Σ ;; Ξ | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ ≡ t) Γ ξ Ξ' →
    Forall2 (Forall2 (conversion Σ Ξ ⟦ Γ ⟧*)) ⟦ ξ ⟧× ξ.
  Proof.
    intros (h1 & h2 & e).
    apply Forall2_map_l. apply Forall2_diag.
    rewrite Forall_forall. intros σ hσ.
    apply Forall2_map_l. apply Forall2_diag.
    rewrite Forall_forall. intros u hu.
    eapply In_nth_error in hσ as [M hM].
    eapply In_nth_error in hu as [x hx].
    specialize (h2 M).
    destruct (ectx_get Ξ' M) as [[E ξ'] |] eqn:e'.
    2:{
      unfold ectx_get in e'. destruct (_ <=? _) eqn: e1.
      - rewrite Nat.leb_le in e1. rewrite <- e in e1.
        rewrite <- nth_error_None in e1. congruence.
      - rewrite nth_error_None in e'.
        rewrite Nat.leb_gt in e1. lia.
    }
    specialize h2 with (1 := eq_refl).
    destruct h2 as (hξ' & Ξ'' & Δ & R & hE & eM & ih).
    rewrite hM in eM. cbn in eM.
    destruct (nth_error Δ x) eqn: eΔ.
    2:{
      rewrite nth_error_None in eΔ. rewrite <- eM in eΔ.
      rewrite <- nth_error_None in eΔ. congruence.
    }
    specialize ih with (1 := eΔ).
    unfold eget in ih. rewrite hM, hx in ih.
    assumption.
  Qed.

  Lemma inst_equations_inline Ξ Ξ' Γ ξ :
    inst_typing_ Σ Ξ (λ Γ t _, Σ ;; Ξ | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ ≡ t) Γ ξ Ξ' →
    inst_equations Σ Ξ ⟦ Γ ⟧* ⟦ ξ ⟧× Ξ'.
  Proof.
    intros h.
    eapply conv_eargs_inline_self in h as hξ.
    destruct h as (h1 & h2 & e).
    intros E M ξ' eM.
    specialize (h1 _ _ _ eM) as (Ξ'' & Δ & R & eE & h1).
    eexists _,_,_. split. 1: eassumption.
    intros n rule hr m δ Θ lhs0 rhs0 hlhs hrhs lhs rhs.
    subst lhs rhs.
    eapply conv_trans.
    1:{ eapply conv_einsts. eapply conv_ren_einst. eassumption. }
    eapply conv_trans.
    2:{
      apply conv_sym.
      eapply conv_einsts. eapply conv_ren_einst. eassumption.
    }
    eapply conv_ctx_irr.
    eapply h1. all: eauto.
  Qed.

  Lemma conv_inline_self Ξ Γ t A :
    gwf Σ →
    Σ ;; Ξ | Γ ⊢ t : A →
    Σ ;; Ξ | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ ≡ t.
  Proof.
    intros hΣ h.
    induction h using typing_ind.
    all: try solve [ cbn ; ttconv ].
    cbn. apply conv_sym.
    eapply conv_trans.
    - eapply conv_unfold. 1: eassumption.
      eapply valid_def in hΣ as h. 2: eassumption.
      destruct h as (_ & _ & h).
      eapply typing_closed. eassumption.
    - apply conv_sym. eapply cong_einst.
      + eapply inst_equations_inline. eassumption.
      + eapply h_conv_unfold. eassumption.
      + eapply conv_eargs_inline_self. eassumption.
  Qed.

  Lemma conv_inline Ξ Γ u v A B :
    gwf Σ →
    Σ ;; Ξ | Γ ⊢ u : A →
    Σ ;; Ξ | Γ ⊢ v : B →
    Σ ;; Ξ | Γ ⊢ u ≡ v →
    Σ ;; Ξ | ⟦ Γ ⟧* ⊢ ⟦ u ⟧ ≡ ⟦ v ⟧.
  Proof.
    intros hΣ hu hv h.
    eapply conv_trans.
    1:{ eapply conv_inline_self. all: eassumption. }
    eapply conv_trans.
    2:{ apply conv_sym. eapply conv_inline_self. all: eassumption. }
    eapply conv_ctx_irr.
    eassumption.
  Qed.

  (* Lemma conv_inline Γ u v :
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
  Qed. *)

  (* Definition gcond' :=
    ∀ c Ξ' A t Γ ξ,
      Σ c = Some (Def Ξ' A t) →
      inst_typing Σ [] Γ ξ Ξ' →
      (* inst_typing [] [] Γ ⟦ ξ ⟧× Ξ' → *)
      [] ;; [] | ⟦ Γ ⟧* ⊢ κ c ⟦ ξ ⟧× : ⟦ einst ξ A ⟧.

  Context (hκ : gcond'). *)

  Lemma inst_typing_inline Γ ξ Ξ Ξ' :
    gwf Σ →
    wf Σ Ξ Γ →
    inst_typing Σ Ξ Γ ξ Ξ' →
    inst_typing_ Σ Ξ (λ Γ t A, wf Σ Ξ Γ → Σ ;; Ξ | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ : ⟦ A ⟧) Γ ξ Ξ' →
    inst_typing Σ Ξ ⟦ Γ ⟧* ⟦ ξ ⟧× Ξ'.
  Proof.
    intros hΣ hΓ hξ (he & hg & e).
    assert (he' : inst_equations Σ Ξ ⟦ Γ ⟧* ⟦ ξ ⟧× Ξ').
    { eapply inst_equations_inline.
      split. 2: split. 1,3: eassumption.
      intros E M ξ' hE.
      specialize (hg _ _ _ hE).
      destruct hg as (hξ' & Ξ'' & Δ & R & hM & ho & h).
      split. 1: assumption.
      eexists _,_,_. split. 1: eassumption.
      split. 1: eassumption.
      intros x A hx.
      eapply conv_inline_self. 1: assumption.
      eapply type_eget. 2-4: eassumption.
      apply hξ.
    }
    split. 2: split.
    - assumption.
    - intros M E ξ' hE.
      specialize (hg _ _ _ hE).
      destruct hg as (hξ' & Ξ'' & Δ & R & hM & ho & h).
      split. 1: assumption.
      eexists _,_,_. split. 1: eassumption.
      split.
      + rewrite nth_error_map. destruct (nth_error ξ M) eqn:eξ. 2: auto.
        cbn in ho |- *. rewrite length_map. assumption.
      + intros x A hx.
        rewrite <- inline_eget.
        eapply type_conv.
        * eapply h. all: eassumption.
        * rewrite inline_einst. eapply conv_einst_closed. 1: eassumption.
          eapply conv_inline_self with (Γ := ∙). 1: assumption.
          admit.
        * admit. (* Would be better if it could be avoided *)
    - rewrite length_map. assumption.
  Admitted.

  Lemma typing_inline Ξ Γ t A :
    gwf Σ →
    ewf Σ Ξ →
    wf Σ Ξ Γ →
    Σ ;; Ξ | Γ ⊢ t : A →
    Σ ;; Ξ | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ : ⟦ A ⟧.
  Proof.
    intros hΣ hΞ hΓ h.
    revert Γ t A hΓ h.
    refine (typing_ind_wf _ _ _ _ _ _ _ _ _ _ _).
    (* induction h using typing_ind_wf. *)
    all: try solve [ intros ; cbn ; tttype ].
    - intros Γ x A hΓ e.
      cbn. rewrite inline_ren. econstructor.
      rewrite nth_error_map. rewrite e. reflexivity.
    - intros Γ i j A B t u hΓ ht iht hu ihu hA ihA hB ihB.
      cbn in *. eapply meta_conv.
      + tttype.
      + rewrite inline_subst. apply ext_term. intros []. all: reflexivity.
    - intros Γ c ξ Ξ' A t hΓ hc hξ ihξ hA.
      cbn. rewrite inline_einst. eapply typing_einst_closed.
      + eapply inst_typing_inline. all: eassumption.
      + (* erewrite hκ. 2: eassumption. *)
        (* Instead I need an assumption about κ c : ⟦ A ⟧ *)
        admit.
    - intros Γ M x E ξ Ξ' Δ R A hΓ hM hE hx hcξ.
      cbn. admit.
    - intros Γ i A B t hΓ ht iht hconv hB ihB.
      econstructor. 1,3: eassumption.
      eapply validity in ht as hA. 2-4: assumption.
      destruct hA.
      eapply conv_inline. all: eassumption.
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

(* Fixpoint inline_gctx Σ :=
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
      2:{ eapply typing_closed. eassumption. }
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
      2:{ eapply typing_closed. eassumption. }
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
  apply meta_conv_refl. clear Γ.
  induction h as [ | c' ?????? ih | c' ??????? ih ] in c, ξ, Ξ', A, t, hc |- *.
  - discriminate.
  - cbn in hc |- *. destruct (c =? c')%string eqn:e. 1: discriminate.
    eapply ih. eassumption.
  - cbn in hc |- *. destruct (c =? c')%string eqn:e.
    + inversion hc. subst. clear hc.
      rewrite gcons_eq. 2: assumption.
      (* If we want to stay on that route, we need this probably *)
      admit.
    + rewrite gcons_neq. 2: assumption.
      (* Why would this hold? *)
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
    (∀ Γ ξ,
      inst_typing [] [] Γ ξ Ξ →
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
  (∀ c Ξ' A t ξ,
    Σ c = Some (Def Ξ' A t) →
    κ c ξ = κ' c ξ
  ) →
  ⟦ t ⟧⟨ κ ⟩ = ⟦ t ⟧⟨ κ' ⟩.
Proof.
  intros ht he.
  induction ht in κ, κ', he |- * using gscope_ind_alt.
  all: try solve [ cbn ; eauto ].
  all: try solve [ cbn ; f_equal ; eauto ].
  cbn.
  assert (e : ⟦ ξ ⟧×⟨ κ ⟩ = ⟦ ξ ⟧×⟨ κ' ⟩).
  { apply map_ext_Forall. eapply Forall_impl. 2: eassumption.
    intros σ hσ.
    apply map_ext_Forall. eapply Forall_impl. 2: eassumption.
    cbn. auto.
  }
  rewrite <- e.
  eapply he. eassumption.
Qed.

(* TODO MOVE *)
Lemma extends_nil Σ :
  [] ⊑ Σ.
Proof.
  intros ?? e. discriminate.
Qed.

Lemma gwf_get Σ Γ c ξ Ξ' A t :
  gwf Σ →
  Σ c = Some (Def Ξ' A t) →
  inst_typing [] [] Γ ξ Ξ' →
  ⟦ Σ ⟧κ c ξ = ⟦ einst ξ t ⟧⟨ ⟦ Σ ⟧κ ⟩.
Proof.
  intros h hc hξ.
  induction h as [ | c' ?????? ih | c' ??????? ih ] in ξ, hξ, c, Ξ', A, t, hc |- *.
  - discriminate.
  - cbn. cbn in hc. destruct (_ =? _)%string eqn:ec.
    1:{ apply eqb_eq in ec. subst. congruence. }
    eauto.
  - cbn in hc |- *. destruct (_ =? _)%string eqn:ec.
    + inversion hc. subst. clear hc.
      rewrite gcons_eq. 2: eassumption.
      eapply inline_ext_gscope.
      1:{
        eapply typing_gscope. eapply typing_einst_closed. 2: eassumption.
        eapply inst_typing_gweak. 1: eassumption.
        apply extends_nil.
      }
      intros c0 ???? e.
      destruct (c0 =? c')%string eqn:e0.
      1:{ rewrite String.eqb_eq in e0. congruence. }
      rewrite gcons_neq. 2: assumption.
      reflexivity.
    + rewrite gcons_neq. 2: assumption.
      erewrite ih. 2,3: eassumption.
      eapply valid_def in hc as hd. 2: assumption.
      eapply inline_ext_gscope.
      1:{
        eapply typing_gscope. eapply typing_einst_closed. 2: eapply hd.
        eapply inst_typing_gweak. 1: eassumption.
        apply extends_nil.
      }
      intros c0 ???? e.
      destruct (c0 =? c')%string eqn:e0.
      1:{ rewrite String.eqb_eq in e0. congruence. }
      rewrite gcons_neq. 2: assumption.
      reflexivity.
Qed.

Lemma gwf_gcond' Σ :
  gwf Σ →
  gcond' Σ ⟦ Σ ⟧κ.
Proof.
  intro h. intros c Ξ' A t Γ ξ e hξ.
  erewrite gwf_get. 2,3: eassumption. 2: admit.
  eapply typing_inline.
  - eapply gwf_gren. assumption.
  - admit.
  - eapply gwf_unfold. assumption.
  - eapply gwf_cong. assumption.
  - (* Not great, a loop *)
    admit.
  - (* Not true anyway *)
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
    intros Γ ξ hξ.
    eapply typing_inline.
    + eapply gwf_gren. assumption.
    + admit.
    + eapply gwf_unfold. assumption.
    + eapply gwf_cong. assumption.
    + eapply gcond_gcond'. eassumption.
    + eapply typing_einst_closed. 2: eassumption.
      eapply inst_typing_gweak. 1: eassumption.
      apply extends_nil.
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
 *)
