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
From LocalComp Require Import Util BasicAST Env Inst Typing BasicMetaTheory
  GScope.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

#[local] Notation ginst := (gref → term).

Section Inline.

  Context (Σ : gctx).
  Context (κ : ginst). (** A map from references to their translated def. **)
  Context (Σᵗ : gctx). (** The translation of [Σ] **)

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

  Notation "⟦ X ⟧e" := (map (λ '(E, ξ), (E, ⟦ ξ ⟧×)) X).

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

  Definition g_conv_unfold :=
    ∀ c Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      Σᵗ ;; ⟦ Ξ' ⟧e | ∙ ⊢ κ c ≡ ⟦ t ⟧.

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

  Definition inline_crule rule := {|
    cr_env := ⟦ rule.(cr_env) ⟧* ;
    cr_pat := ⟦ rule.(cr_pat) ⟧ ;
    cr_sub x := ⟦ rule.(cr_sub) x ⟧ ;
    cr_rep := ⟦ rule.(cr_rep) ⟧ ;
    cr_typ := ⟦ rule.(cr_typ) ⟧
  |}.

  Notation "⟦ r ⟧r" := (inline_crule r).

  Definition inline_equation ε := {|
    eq_env := ⟦ ε.(eq_env) ⟧* ;
    eq_lhs := ⟦ ε.(eq_lhs) ⟧ ;
    eq_rhs := ⟦ ε.(eq_rhs) ⟧ ;
    eq_typ := ⟦ ε.(eq_typ) ⟧
  |}.

  Notation "⟦ e ⟧ε" := (inline_equation e).

  Lemma inline_crule_eq r :
    ⟦ crule_eq r ⟧ε = crule_eq ⟦ r ⟧r.
  Proof.
    unfold inline_crule, inline_equation, crule_eq. cbn. f_equal.
    apply inline_subst.
  Qed.

  Definition map_fst [A B C] (f : A → C) (p : A * B) :=
    let '(a,b) := p in (f a, b).

  Notation "⟦ E ⟧𝔼" := (map inline_equation E).

  Definition trans_gctx_ext :=
    ∀ E Ξ' Δ R,
      Σ E = Some (Ext Ξ' Δ R) →
      ∃ R',
        Σᵗ E = Some (Ext ⟦ Ξ' ⟧e ⟦ Δ ⟧* R') ∧
        ⟦ map crule_eq R ⟧𝔼 = map crule_eq R'.

  Context (hext : trans_gctx_ext).

  Lemma ectx_get_inline Ξ M E ξ' :
    ectx_get Ξ M = Some (E, ξ') →
    ectx_get ⟦ Ξ ⟧e M = Some (E, ⟦ ξ' ⟧×).
  Proof.
    unfold ectx_get. intro h.
    rewrite length_map. destruct (_ <=? _) eqn:e. 1: discriminate.
    rewrite nth_error_map.
    destruct nth_error eqn:e'. 2: discriminate.
    inversion h. subst.
    cbn. reflexivity.
  Qed.

  Lemma ectx_get_map Ξ M f :
    ectx_get (map (λ '(E, ξ), (E, f ξ)) Ξ) M =
    option_map (λ '(E, ξ), (E, f ξ)) (ectx_get Ξ M).
  Proof.
    unfold ectx_get. rewrite length_map.
    rewrite nth_error_map.
    destruct (_ <=? _). all: reflexivity.
  Qed.

  Lemma inline_rule_tm M ξ δ k t :
    ⟦ rule_tm M ξ δ k t ⟧ = rule_tm M ⟦ ξ ⟧× δ k ⟦ t ⟧.
  Proof.
    unfold rule_tm. unfold delocal_lift.
    rewrite inline_subst. rewrite inline_einst.
    rewrite inline_ren_eargs. apply ext_term.
    intros n. unfold core.funcomp.
    destruct (lt_dec n k).
    - rewrite ups_below. 2: assumption.
      reflexivity.
    - pose (m := n - k). replace n with (k + m) by lia.
      rewrite ups_above. reflexivity.
  Qed.

  Lemma inline_rule_lhs M ξ δ rule :
    ⟦ rule_lhs M ξ δ rule ⟧ = rule_lhs M ⟦ ξ ⟧× δ ⟦ rule ⟧ε.
  Proof.
    unfold rule_lhs. rewrite inline_rule_tm. cbn - [rule_tm].
    rewrite length_map. reflexivity.
  Qed.

  Lemma inline_rule_rhs M ξ δ rule :
    ⟦ rule_rhs M ξ δ rule ⟧ = rule_rhs M ⟦ ξ ⟧× δ ⟦ rule ⟧ε.
  Proof.
    unfold rule_rhs. rewrite inline_rule_tm. cbn - [rule_tm].
    rewrite length_map. reflexivity.
  Qed.

  Lemma scoped_eargs_inline_ih k ξ :
    All (All (λ t, ∀ k, scoped k t = true → scoped k ⟦ t ⟧ = true)) ξ →
    scoped_eargs k ξ = true →
    scoped_eargs k ⟦ ξ ⟧× = true.
  Proof.
    intros ih h.
    apply forallb_All in h. move h at top.
    eapply All_prod in h. 2: eassumption.
    apply All_forallb. apply All_map. eapply All_impl. 2: eassumption.
    cbn. intros σ [h1 h2].
    apply All_forallb. apply All_map.
    apply forallb_All in h2.
    eapply All_prod in h1. 2: eassumption.
    eapply All_impl. 2: eassumption.
    cbn. intros t []. eauto.
  Qed.

  Lemma scoped_inline k t :
    scoped k t = true →
    scoped k ⟦ t ⟧ = true.
  Proof.
    intros h.
    induction t using term_rect in k, h |- *.
    all: try solve [ cbn ; eauto ].
    all: try solve [
      cbn in * ; rewrite Bool.andb_true_iff in * ;
      intuition eauto
    ].
    cbn in h |- *. eapply scoped_einst_closed.
    - eapply scoped_eargs_inline_ih. all: assumption.
    - apply hclosed.
  Qed.

  Lemma scoped_eargs_inline k ξ :
    scoped_eargs k ξ = true →
    scoped_eargs k ⟦ ξ ⟧× = true.
  Proof.
    intros h.
    eapply scoped_eargs_inline_ih. 2: assumption.
    eapply forall_All. intros.
    eapply forall_All. intros.
    eapply scoped_inline. assumption.
  Qed.

  Lemma inline_ctx_einst ξ Γ :
    ⟦ ctx_einst ξ Γ ⟧* = ctx_einst ⟦ ξ ⟧× ⟦ Γ ⟧*.
  Proof.
    induction Γ as [| A Γ ih] in ξ |- *.
    - reflexivity.
    - cbn. rewrite ih. rewrite inline_einst.
      rewrite inline_ren_eargs. rewrite length_map. reflexivity.
  Qed.

  Lemma inst_equations_inline_ih Ξ Ξ' Γ ξ :
    inst_equations_ Σ (λ Γ u v, Σᵗ ;; ⟦ Ξ ⟧e | ⟦ Γ ⟧* ⊢ ⟦ u ⟧ ≡ ⟦ v ⟧) Γ ξ Ξ' →
    inst_equations Σᵗ ⟦ Ξ ⟧e ⟦ Γ ⟧* ⟦ ξ ⟧× ⟦ Ξ' ⟧e.
  Proof.
    intros ih.
    intros E M ξ' hM.
    rewrite ectx_get_map in hM.
    destruct ectx_get as [[E' ξ'']|] eqn:hM'. 2: discriminate.
    cbn in hM. inversion hM. subst. clear hM.
    specialize (ih _ _ _ hM') as (Ξ'' & Δ' & R & e & ih).
    eapply hext in e as e'. destruct e' as (R' & ? & eR).
    eexists _,_,_. split. 1: eauto.
    intros n ε hn m δ Θ lhs0 rhs0. cbn.
    rewrite <- eR in hn.
    rewrite nth_error_map in hn.
    destruct (nth_error _ n) as [ε' |] eqn:hn'. 2: discriminate.
    cbn in hn. inversion hn. subst. clear hn.
    specialize ih with (1 := hn'). cbn in ih.
    destruct ih as (hl & hr & ih).
    subst m lhs0 rhs0 δ.
    cbn - [ rule_lhs rule_rhs]. rewrite !length_map.
    rewrite <- inline_rule_rhs, <- inline_rule_lhs.
    rewrite map_app in ih. rewrite !inline_ctx_einst in ih.
    rewrite !inline_einst in ih. rewrite !inline_ren_eargs in ih.
    intuition eauto using scoped_inline.
  Qed.

  Lemma conv_inline Ξ Γ u v :
    Σ ;; Ξ | Γ ⊢ u ≡ v →
    Σᵗ ;; ⟦ Ξ ⟧e | ⟦ Γ ⟧* ⊢ ⟦ u ⟧ ≡ ⟦ v ⟧.
  Proof.
    intros h.
    induction h using conversion_ind.
    all: try solve [ cbn ; ttconv ].
    - cbn. rewrite inline_subst. eapply meta_conv_trans_r. 1: econstructor.
      apply ext_term. intros []. all: reflexivity.
    - cbn. rewrite inline_einst. eapply conv_einst_closed.
      + eapply inst_equations_inline_ih. eassumption.
      + eapply h_conv_unfold. eassumption.
    - cbn. eapply conv_einsts.
      apply Forall2_map_l, Forall2_map_r.
      eapply Forall2_impl. 2: eassumption.
      intros. apply Forall2_map_l, Forall2_map_r.
      eapply Forall2_impl. 2: eassumption.
      cbn. auto.
    - econstructor. assumption.
    - eapply conv_trans. all: eassumption.
  Qed.

  Definition g_type :=
    ∀ c Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      Σᵗ ;; ⟦ Ξ' ⟧e | ∙ ⊢ κ c : ⟦ A ⟧.

  Context (h_type : g_type).

  Lemma inline_delocal M t :
    ⟦ delocal M t ⟧ = delocal M ⟦ t ⟧.
  Proof.
    unfold delocal.
    rewrite inline_subst. reflexivity.
  Qed.

  Lemma inst_typing_inline Ξ Γ ξ Ξ' :
    inst_typing_ Σ Ξ (λ Γ t A, Σᵗ ;; ⟦ Ξ ⟧e | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ : ⟦ A ⟧) Γ ξ Ξ' →
    inst_typing Σᵗ ⟦ Ξ ⟧e ⟦ Γ ⟧* ⟦ ξ ⟧× ⟦ Ξ' ⟧e.
  Proof.
    intros (he & ih & e).
    split. 2: split.
    - eauto using inst_equations_inline_ih, inst_equations_prop, conv_inline.
    - intros M E ξ' eM.
      rewrite ectx_get_map in eM.
      destruct ectx_get as [[E' ξ'']|] eqn:eM'. 2: discriminate.
      cbn in eM. inversion eM. subst. clear eM.
      specialize (ih _ _ _ eM') as (? & Ξ'' & Δ & R & eE & ho & ih).
      split. 1:{ apply scoped_eargs_inline. assumption. }
      eapply hext in eE as e'. destruct e' as (R' & ? & eR).
      eexists _,_,_. split. 1: eauto.
      split.
      1:{
        rewrite nth_error_map, onSome_map. setoid_rewrite length_map.
        assumption.
      }
      intros x A hx.
      rewrite nth_error_map in hx.
      destruct (nth_error Δ x) as [B|] eqn: eB. 2: discriminate.
      cbn in hx. inversion hx. subst. clear hx.
      specialize ih with (1 := eB).
      rewrite inline_eget, inline_einst, inline_delocal in ih.
      rewrite inline_einst, inline_ren in ih.
      assumption.
    - rewrite 2!length_map. assumption.
  Qed.

  Lemma typing_inline Ξ Γ t A :
    gwf Σ →
    Σ ;; Ξ | Γ ⊢ t : A →
    Σᵗ ;; ⟦ Ξ ⟧e | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ : ⟦ A ⟧.
  Proof.
    intros hΣ h.
    induction h using typing_ind.
    all: try solve [ intros ; cbn ; tttype ].
    - cbn. rewrite inline_ren. econstructor.
      rewrite nth_error_map. rewrite H. reflexivity.
    - cbn in *. eapply meta_conv.
      + tttype.
      + rewrite inline_subst. apply ext_term. intros []. all: reflexivity.
    - cbn. rewrite inline_einst. eapply typing_einst_closed.
      + eapply inst_typing_inline. eassumption.
      + eapply h_type. all: eassumption.
    - cbn. rewrite inline_delocal. rewrite inline_einst. rewrite inline_ren.
      eapply hext in H0 as e'. destruct e' as (R' & ? & eR).
      econstructor.
      + eapply ectx_get_inline. eassumption.
      + eauto.
      + rewrite nth_error_map. rewrite H1. reflexivity.
      + eapply scoped_eargs_inline. assumption.
    - econstructor. 1,3: eassumption.
      apply conv_inline. assumption.
  Qed.

End Inline.

Notation "⟦ t ⟧⟨ k ⟩" := (inline k t) (at level 0).
Notation "⟦ l ⟧*⟨ k ⟩" := (map (inline k) l).
Notation "⟦ t ⟧×⟨ k ⟩" := (map (map (inline k)) t).
Notation "⟦ X ⟧e⟨ k ⟩" := (map (λ '(E, ξ), (E, ⟦ ξ ⟧×⟨ k ⟩)) X).
Notation "⟦ e ⟧ε⟨ k ⟩" := (inline_equation k e).
Notation "⟦ R ⟧R⟨ k ⟩" := (map (inline_crule k) R).
Notation "⟦ E ⟧𝔼⟨ k ⟩" := (map (inline_equation k) E).

Reserved Notation "⟦ s ⟧κ" (at level 0).

(* TODO Probably can just use [list (greg * term)] *)

Definition gnil (c : gref) :=
  dummy.

Definition gcons r t κ (c : gref) : term :=
  if (c =? r)%string then t else κ c.

Fixpoint inline_gctx_ufd Σ :=
  match Σ with
  | (c, d) :: Σ =>
    let κ := ⟦ Σ ⟧κ in
    match d with
    | Def Ξ A t => gcons c ⟦ t ⟧⟨ κ ⟩ κ
    | _ => κ
    end
  | [] => gnil
  end
where "⟦ s ⟧κ" := (inline_gctx_ufd s).

Lemma gcons_eq c c' t κ :
  (c' =? c)%string = true →
  gcons c t κ c' = t.
Proof.
  intro h.
  unfold gcons. rewrite h. reflexivity.
Qed.

Lemma gcons_neq c c' t κ :
  (c' =? c)%string = false →
  gcons c t κ c' = κ c'.
Proof.
  intro h.
  unfold gcons. rewrite h. reflexivity.
Qed.

Definition eq_gscope (Σ : gctx) (κ κ' : ginst) :=
  ∀ c Ξ' A t,
    Σ c = Some (Def Ξ' A t) →
    κ c = κ' c.

Lemma inline_ext Σ t κ κ' :
  gscope Σ t →
  eq_gscope Σ κ κ' →
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
  rewrite <- e. f_equal.
  eapply he. eassumption.
Qed.

Lemma inline_eargs_ext Σ (ξ : eargs) κ κ' :
  gscope_eargs Σ ξ →
  eq_gscope Σ κ κ' →
  ⟦ ξ ⟧×⟨ κ ⟩ = ⟦ ξ ⟧×⟨ κ' ⟩.
Proof.
  intros hξ he.
  eapply map_ext_Forall. eapply Forall_impl. 2: eassumption.
  intros. eapply map_ext_Forall. eapply Forall_impl. 2: eassumption.
  intros. eapply inline_ext. all: eassumption.
Qed.

Lemma inline_ectx_ext Σ Ξ κ κ' :
  ewf Σ Ξ →
  eq_gscope Σ κ κ' →
  ⟦ Ξ ⟧e⟨ κ ⟩ = ⟦ Ξ ⟧e⟨ κ' ⟩.
Proof.
  intros hΞ he.
  eapply map_ext_Forall.
  induction hΞ as [| Ξ E ξ' Ξ' Δ R hΞ ih e hξ' ]. 1: constructor.
  econstructor. 2: eauto.
  f_equal.
  eapply inline_eargs_ext. 2: eassumption.
  eapply inst_typing_gscope. eassumption.
Qed.

Lemma inline_list_ext Σ l κ κ' :
  Forall (gscope Σ) l →
  eq_gscope Σ κ κ' →
  ⟦ l ⟧*⟨ κ ⟩ = ⟦ l ⟧*⟨ κ' ⟩.
Proof.
  intros hl he.
  eapply map_ext_Forall. eapply Forall_impl. 2: eassumption.
  intros. eapply inline_ext. all: eassumption.
Qed.

Lemma inline_ctx_ext Σ Ξ Γ κ κ' :
  wf Σ Ξ Γ →
  eq_gscope Σ κ κ' →
  ⟦ Γ ⟧*⟨ κ ⟩ = ⟦ Γ ⟧*⟨ κ' ⟩.
Proof.
  intros hΓ he.
  eapply inline_list_ext. 2: eassumption.
  eapply wf_gscope. eassumption.
Qed.

Lemma inline_equation_ext Σ ε κ κ' :
  gscope_equation Σ ε →
  eq_gscope Σ κ κ' →
  ⟦ ε ⟧ε⟨ κ ⟩ = ⟦ ε ⟧ε⟨ κ' ⟩.
Proof.
  intros [? [? []]] he.
  destruct ε as [Θ l r A].
  unfold inline_equation. cbn in *. f_equal.
  - eapply inline_list_ext. all: eassumption.
  - eapply inline_ext. all: eassumption.
  - eapply inline_ext. all: eassumption.
  - eapply inline_ext. all: eassumption.
Qed.

Lemma inline_equations_ext Σ R κ κ' :
  Forall (gscope_equation Σ) R →
  eq_gscope Σ κ κ' →
  ⟦ R ⟧𝔼⟨ κ ⟩ = ⟦ R ⟧𝔼⟨ κ' ⟩.
Proof.
  intros hR he.
  eapply map_ext_Forall. eapply Forall_impl. 2: eassumption.
  intros. eapply inline_equation_ext. all: eassumption.
Qed.

Reserved Notation "⟦ s ⟧g".

Fixpoint inline_gctx (Σ : gctx) : gctx :=
  match Σ with
  | [] => []
  | (c, Def Ξ A t) :: Σ => ⟦ Σ ⟧g
  | (c, Ext Ξ Δ R) :: Σ =>
    let κ := ⟦ Σ ⟧κ in
    (c, Ext ⟦ Ξ ⟧e⟨ κ ⟩ ⟦ Δ ⟧*⟨ κ ⟩ ⟦ R ⟧R⟨ κ ⟩) :: ⟦ Σ ⟧g
  end

where "⟦ s ⟧g" := (inline_gctx s).

Lemma inline_gctx_None (Σ : gctx) c :
  Σ c = None →
  ⟦ Σ ⟧g c = None.
Proof.
  intros e.
  induction Σ as [| [c' []] Σ ih].
  - reflexivity.
  - cbn in *. destruct (c =? c')%string eqn:ec. 1: discriminate.
    eauto.
  - cbn in *. destruct (c =? c')%string eqn:ec. 1: discriminate.
    eauto.
Qed.

Lemma eq_gscope_gcons (Σ : gctx) κ c u :
  Σ c = None →
  eq_gscope Σ κ (gcons c u κ).
Proof.
  intros h c' Ξ A t e.
  destruct (c' =? c)%string eqn:ec.
  1:{ rewrite String.eqb_eq in ec. congruence. }
  rewrite gcons_neq. 2: assumption.
  reflexivity.
Qed.

Lemma gwf_gclosed Σ :
  gwf Σ →
  gclosed ⟦ Σ ⟧κ.
Proof.
  intros h.
  induction h as [ | c' ?????? ih | c' ??????? ih ].
  all: intros c.
  - cbn. reflexivity.
  - cbn. eauto.
  - cbn. destruct (c =? c')%string eqn:ec.
    + rewrite gcons_eq. 2: assumption.
      eapply scoped_inline. 1: assumption.
      eapply typing_closed. eassumption.
    + rewrite gcons_neq. 2: assumption.
      eauto.
Qed.

Lemma gwf_conv_unfold Σ :
  gwf Σ →
  g_conv_unfold Σ ⟦ Σ ⟧κ ⟦ Σ ⟧g.
Proof.
  intros h c Ξ' A t ec.
  induction h as [ | c' ?????? ih | c' ??????? ih ].
  - discriminate.
  - cbn in *. destruct (c =? c')%string eqn:e. 1: discriminate.
    eapply conv_gweak. 1: eauto.
    eapply extends_gcons.
    apply inline_gctx_None. assumption.
  - cbn in *. destruct (c =? c')%string eqn:e.
    + inversion ec. subst. clear ec.
      rewrite gcons_eq. 2: assumption.
      erewrite <- inline_ectx_ext. 2,3: eauto using eq_gscope_gcons.
      apply meta_conv_refl.
      eapply inline_ext.
      all: eauto using eq_gscope_gcons, typing_gscope.
    + rewrite gcons_neq. 2: assumption.
      eapply valid_def in ec as h'. 2: assumption.
      destruct h' as (hΞ' & [j hB] & ht).
      erewrite <- inline_ectx_ext. 2,3: eauto using eq_gscope_gcons.
      erewrite <- inline_ext with (t := t).
      2,3: eauto using eq_gscope_gcons, typing_gscope.
      eauto.
Qed.

Lemma gwf_trans_gctx_ext Σ :
  gwf Σ →
  trans_gctx_ext Σ ⟦ Σ ⟧κ ⟦ Σ ⟧g.
Proof.
  intros h E Ξ' Δ R eE.
  induction h as [ | c ?????? ih | c ??????? ih ].
  - discriminate.
  - cbn in *. destruct (E =? c)%string eqn:e.
    + inversion eE. subst. eexists. split.
      * reflexivity.
      * rewrite !map_map. eapply map_ext.
        intros. apply inline_crule_eq.
        eapply gwf_gclosed. assumption.
    + eauto.
  - cbn in *. destruct (E =? c)%string eqn:e. 1: discriminate.
    eapply ih in eE as h'. destruct h' as (R' & eE' & eR).
    exists R'. rewrite <- eR.
    assert (eg : eq_gscope Σ ⟦ Σ ⟧κ (gcons c ⟦ t ⟧⟨ ⟦ Σ ⟧κ ⟩ ⟦ Σ ⟧κ)).
    { eapply eq_gscope_gcons. assumption. }
    eapply valid_ext in eE as h'. 2: assumption.
    destruct h' as (hΞ' & hΔ & hR).
    split.
    + rewrite eE'. f_equal. f_equal.
      * eapply inline_ectx_ext. all: eassumption.
      * eapply inline_ctx_ext. all: eassumption.
    + symmetry. eapply inline_equations_ext. 2: eassumption.
      eapply equations_typing_gscope. eassumption.
Qed.

Lemma gwf_type Σ :
  gwf Σ →
  g_type Σ ⟦ Σ ⟧κ ⟦ Σ ⟧g.
Proof.
  intros h.
  induction h as [ | c' ?????? ih | c' ??????? ih ].
  all: intros c Ξ' B u ec.
  - discriminate.
  - cbn in *. destruct (c =? c')%string eqn:e. 1: discriminate.
    eapply typing_gweak. 1: eauto.
    eapply extends_gcons.
    apply inline_gctx_None. assumption.
  - cbn in *. destruct (c =? c')%string eqn:e.
    + inversion ec. subst. clear ec.
      rewrite gcons_eq. 2: assumption.
      erewrite <- inline_ectx_ext. 2,3: eauto using eq_gscope_gcons.
      erewrite <- inline_ext with (t := B).
      2,3: eauto using eq_gscope_gcons, typing_gscope.
      eapply typing_inline with (Γ := ∙).
      * eapply gwf_gclosed. assumption.
      * eapply gwf_conv_unfold. assumption.
      * eapply gwf_trans_gctx_ext. assumption.
      * assumption.
      * assumption.
      * assumption.
    + rewrite gcons_neq. 2: assumption.
      eapply valid_def in ec as h'. 2: assumption.
      destruct h' as (hΞ' & [j hB] & ht).
      erewrite <- inline_ectx_ext. 2,3: eauto using eq_gscope_gcons.
      erewrite <- inline_ext with (t := B).
      2,3: eauto using eq_gscope_gcons, typing_gscope.
      eauto.
Qed.

Theorem inlining Ξ Σ Γ t A :
  gwf Σ →
  let κ := ⟦ Σ ⟧κ in
  Σ ;; Ξ | Γ ⊢ t : A →
  ⟦ Σ ⟧g ;; ⟦ Ξ ⟧e⟨ κ ⟩ | ⟦ Γ ⟧*⟨ κ ⟩ ⊢ ⟦ t ⟧⟨ κ ⟩ : ⟦ A ⟧⟨ κ ⟩.
Proof.
  intros hΣ κ h.
  eapply typing_inline.
  - eapply gwf_gclosed. assumption.
  - eapply gwf_conv_unfold. assumption.
  - eapply gwf_trans_gctx_ext. assumption.
  - eapply gwf_type. assumption.
  - eassumption.
  - assumption.
Qed.

(** Conservativity **)

Lemma inline_nil_id t κ :
  gscope [] t →
  ⟦ t ⟧⟨ κ ⟩ = t.
Proof.
  intros h. induction h using gscope_ind_alt.
  all: try solve [ cbn ; f_equal ; eauto ].
  discriminate.
Qed.

Fixpoint only_exts (Σ : gctx) : bool :=
  match Σ with
  | [] => true
  | (c, Def Ξ A t) :: Σ => false
  | (c, Ext Ξ Δ R) :: Σ => only_exts Σ
  end.

Lemma only_exts_no_def Σ c Ξ A t :
  only_exts Σ = true →
  Σ c = Some (Def Ξ A t) →
  False.
Proof.
  intros h hc.
  induction Σ as [| [c' []] Σ ih] in Ξ, A, t, h, hc |- *. 1,3: discriminate.
  cbn in *. destruct (c =? c')%string eqn:ec. 1: discriminate.
  eauto.
Qed.

Lemma conv_noext Σ Γ u v :
  only_exts Σ = true →
  Σ ;; [] | Γ ⊢ u ≡ v →
  [] ;; [] | Γ ⊢ u ≡ v.
Proof.
  intros hΣ h.
  induction h using conversion_ind.
  all: try solve [ ttconv ].
  all: try solve [ econstructor ; eauto ].
  exfalso. eauto using only_exts_no_def.
Qed.

Lemma typing_noext Σ Γ t A :
  only_exts Σ = true →
  Σ ;; [] | Γ ⊢ t : A →
  [] ;; [] | Γ ⊢ t : A.
Proof.
  intros hΣ h.
  induction h using typing_ind.
  all: try solve [ tttype ].
  - exfalso. eauto using only_exts_no_def.
  - discriminate.
  - econstructor. 1,3: eauto.
    eauto using conv_noext.
Qed.

Lemma only_exts_inline Σ :
  only_exts ⟦ Σ ⟧g = true.
Proof.
  induction Σ as [| [c' []] Σ ih]. all: cbn ; auto.
Qed.

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
  eapply typing_gscope in hA as gA. eapply inline_nil_id in gA.
  rewrite gA in ht.
  eapply typing_noext. 2: eassumption.
  eapply only_exts_inline.
Qed.
