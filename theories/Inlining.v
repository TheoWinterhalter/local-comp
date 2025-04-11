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
      Σᵗ ;; Ξ' | ∙ ⊢ κ c ≡ ⟦ t ⟧.

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

  (* Lemma conv_eargs_inline_self Ξ Ξ' Γ ξ :
    inst_typing_ Σ Ξ (λ Γ t _, Σ ;; Ξ | ⟦ Γ ⟧* ⊢ ⟦ t ⟧ ≡ t) Γ ξ Ξ' →
    Forall2 (Forall2 (conversion Σ Ξ ⟦ Γ ⟧) ⟦ ξ ⟧× ξ.
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
  Qed. *)

  (* Lemma inst_equations_inline Ξ Ξ' Γ ξ :
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
  Qed. *)

  Fixpoint inline_parg p :=
    match p with
    | pvar => pvar
    | pforce t => pforce ⟦ t ⟧
    | psymb x l => psymb x (map inline_parg l)
    end.

  Definition inline_pat p := {|
    pat_head := p.(pat_head) ;
    pat_args := map inline_parg p.(pat_args)
  |}.

  Notation "⟦ p ⟧p" := (inline_pat p).

  Definition inline_crule rule := {|
    cr_env := ⟦ rule.(cr_env) ⟧* ;
    cr_pat := ⟦ rule.(cr_pat) ⟧p ;
    cr_rep := ⟦ rule.(cr_rep) ⟧ ;
    cr_typ := ⟦ rule.(cr_typ) ⟧
  |}.

  Notation "⟦ r ⟧r" := (inline_crule r).

  Definition map_fst [A B C] (f : A → C) (p : A * B) :=
    let '(a,b) := p in (f a, b).

  Notation "⟦ R ⟧R" := (map inline_crule R).

  Definition trans_gctx_ext :=
    ∀ E Ξ' Δ R,
      Σ E = Some (Ext Ξ' Δ R) →
      Σᵗ E = Some (Ext ⟦ Ξ' ⟧e ⟦ Δ ⟧* ⟦ R ⟧R).

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

  Lemma inst_equations_inline Ξ Ξ' Γ ξ :
    inst_equations Σ Ξ Γ ξ Ξ' →
    inst_equations Σᵗ ⟦ Ξ ⟧e ⟦ Γ ⟧* ⟦ ξ ⟧× ⟦ Ξ' ⟧e.
  Proof.
    intros h.
    intros E M ξ' eM.
    rewrite ectx_get_map in eM.
    destruct ectx_get as [[E' ξ'']|] eqn:eM'. 2: discriminate.
    cbn in eM. inversion eM. subst. clear eM.
    specialize (h _ _ _ eM') as (Ξ'' & Δ & R & eE & h1).
    eapply hext in eE as eE'.
    eexists _,_,_. split. 1: eassumption.
    intros n rule hr m δ Θ lhs0 rhs0 hlhs hrhs lhs rhs.
    rewrite nth_error_map in hr.
    destruct (nth_error R n) as [rule'|] eqn: hrn. 2: discriminate.
    cbn in hr. inversion hr. subst. clear hr.
    specialize h1 with (1 := hrn).
    (* subst lhs rhs. *)
    (* This is currently not enough, but might work with a proper ih. *)
    (* This will probably mean adding this to conversion, but all typed
      instances will verify this so maybe it's ok. *)
  Abort.

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

  Lemma inline_plinst_args f l n :
    Forall (λ p, ∀ k, f (inline_parg p) k = map_fst inline (f p k)) l →
    plinst_args f (map inline_parg l) n =
    map_fst (map inline) (plinst_args f l n).
  Proof.
    intros h.
    unfold plinst_args. change (∙, n) with (map_fst (map inline) (∙, n)) at 1.
    generalize (∙, n) as p. intros p.
    induction h as [| x l hx hl ih] in p |- *.
    - reflexivity.
    - cbn. rewrite <- ih. f_equal.
      destruct p as [acc k]. cbn.
      rewrite hx.
      destruct (f x k). reflexivity.
  Qed.

  Lemma inline_apps u l :
    ⟦ apps u l ⟧ = apps ⟦ u ⟧ ⟦ l ⟧*.
  Proof.
    induction l in u |- *.
    - reflexivity.
    - eauto.
  Qed.

  Lemma inline_plinst_arg p k :
    plinst_arg (inline_parg p) k = map_fst inline (plinst_arg p k).
  Proof.
    induction p using parg_ind in k |- *.
    - cbn. reflexivity.
    - cbn. reflexivity.
    - cbn. rewrite inline_plinst_args.
      + destruct plinst_args. cbn.
        rewrite inline_apps. rewrite map_rev. reflexivity.
      + assumption.
  Qed.

  Lemma inline_plinst k p :
    ⟦ plinst k p ⟧ = plinst k ⟦ p ⟧p.
  Proof.
    unfold plinst. cbn - [ plinst_args ].
    rewrite inline_plinst_args.
    - destruct plinst_args. rewrite inline_apps. rewrite map_rev. reflexivity.
    - apply Forall_forall. intros. apply inline_plinst_arg.
  Qed.

  Lemma inline_rule_lhs M ξ δ rule :
    ⟦ rule_lhs M ξ δ rule ⟧ = rule_lhs M ⟦ ξ ⟧× δ ⟦ rule ⟧r.
  Proof.
    unfold rule_lhs. rewrite inline_rule_tm. cbn.
    rewrite length_map. rewrite inline_plinst. reflexivity.
  Qed.

  Lemma inline_rule_rhs M ξ δ rule :
    ⟦ rule_rhs M ξ δ rule ⟧ = rule_rhs M ⟦ ξ ⟧× δ ⟦ rule ⟧r.
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

  (* TODO MOVE *)
  Lemma forall_All A (P : A → Type) l :
    (forall x, In x l → P x) →
    All P l.
  Proof.
    intros h.
    induction l as [| x l ih].
    - constructor.
    - econstructor.
      + eapply h. cbn. auto.
      + eapply ih. intros y hy.
        eapply h. cbn. auto.
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
      + (* eapply inst_equations_inline. eassumption. *) admit.
      + eapply h_conv_unfold. eassumption.
    - rewrite !inline_subst. subst lhs rhs.
      rewrite inline_rule_lhs, inline_rule_rhs.
      replace δ with (length ⟦ Δ ⟧*). 2:{ apply length_map. }
      eapply conv_red.
      + eapply hext. eassumption.
      + apply ectx_get_inline. assumption.
      + rewrite nth_error_map. rewrite H1. reflexivity.
      + rewrite <- inline_rule_lhs. eapply scoped_inline.
        cbn. rewrite 2!length_map. assumption.
      + rewrite <- inline_rule_rhs. eapply scoped_inline.
        cbn. rewrite 2!length_map. assumption.
    - cbn. eapply conv_einsts.
      apply Forall2_map_l, Forall2_map_r.
      eapply Forall2_impl. 2: eassumption.
      intros. apply Forall2_map_l, Forall2_map_r.
      eapply Forall2_impl. 2: eassumption.
      cbn. auto.
    - econstructor. assumption.
    - eapply conv_trans. all: eassumption.
  Admitted.

  (* Definition gcond' :=
    ∀ c Ξ' A t Γ ξ,
      Σ c = Some (Def Ξ' A t) →
      inst_typing Σ [] Γ ξ Ξ' →
      (* inst_typing [] [] Γ ⟦ ξ ⟧× Ξ' → *)
      [] ;; [] | ⟦ Γ ⟧* ⊢ κ c ⟦ ξ ⟧× : ⟦ einst ξ A ⟧.

  Context (hκ : gcond'). *)

  (* Lemma inst_typing_inline Γ ξ Ξ Ξ' :
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
  Admitted. *)

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
      + (* eapply inst_typing_inline. all: eassumption. *) admit.
      + eapply h_type. all: eassumption.
    - cbn. rewrite inline_delocal. rewrite inline_einst. rewrite inline_ren.
      econstructor.
      + eapply ectx_get_inline. eassumption.
      + eapply hext. eassumption.
      + rewrite nth_error_map. rewrite H1. reflexivity.
      + eapply scoped_eargs_inline. assumption.
    - econstructor. 1,3: eassumption.
      apply conv_inline. assumption.
  Admitted.

End Inline.

Notation "⟦ t ⟧⟨ k ⟩" := (inline k t) (at level 0).
Notation "⟦ l ⟧*⟨ k ⟩" := (map (inline k) l).
Notation "⟦ t ⟧×⟨ k ⟩" := (map (map (inline k)) t).
Notation "⟦ X ⟧e⟨ k ⟩" := (map (λ '(E, ξ), (E, ⟦ ξ ⟧×⟨ k ⟩)) X).
Notation "⟦ R ⟧R⟨ k ⟩" := (map (inline_crule k) R).

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

(* Lemma gwf_gren Σ :
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
Qed. *)

(* Lemma gwf_gsubst Σ :
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
Abort. *)

(* Lemma gwf_unfold Σ :
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
Admitted. *)

(* Lemma gwf_cong Σ :
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
Admitted. *)

(* Inductive gcond : gctx → ginst → Prop :=
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
    gcond ((c, Def Ξ A t) :: Σ) (gcons c (λ ξ, ⟦ einst ξ t ⟧⟨ κ ⟩) κ). *)

(* Lemma gcond_gcond' Σ κ :
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
Admitted. *)

(* Lemma inline_ext_gscope Σ t κ κ' :
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
Qed. *)

(* TODO MOVE *)
Lemma extends_nil Σ :
  [] ⊑ Σ.
Proof.
  intros ?? e. discriminate.
Qed.

(* Lemma gwf_get Σ Γ c ξ Ξ' A t :
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
Qed. *)

(* Lemma gwf_gcond' Σ :
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
Abort. *)

(* Lemma gwf_gcond Σ :
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
Abort. *)

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

Lemma gwf_gclosed Σ :
  gwf Σ →
  gclosed ⟦ Σ ⟧κ.
Proof.
  intros h c.
Admitted.

Lemma gwf_conv_unfold Σ :
  gwf Σ →
  g_conv_unfold Σ ⟦ Σ ⟧κ ⟦ Σ ⟧g.
Proof.
  intros h c Ξ' A t ec.
Admitted.

Lemma gwf_trans_gctx_ext Σ :
  gwf Σ →
  trans_gctx_ext Σ ⟦ Σ ⟧κ ⟦ Σ ⟧g.
Proof.
  intros h E Ξ' Δ R eE.
Admitted.

Lemma gwf_type Σ :
  gwf Σ →
  g_type Σ ⟦ Σ ⟧κ ⟦ Σ ⟧g.
Proof.
  intros h c Ξ' A t ec.
Admitted.

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
