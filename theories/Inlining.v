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

  For [assm], we assume it is always globally scoped.
  Indeed, we focus on whether [const] is properly pointing to [Σ].

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
    gscope Σ (const c ξ)
| gscope_assm M x : gscope Σ (assm M x).

Notation gscope_eargs Σ ξ := (Forall (Forall (gscope Σ)) ξ).

Lemma inst_typing_gscope_ih Σ Ξ Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ _ t _, gscope Σ t) Γ ξ Ξ' →
  gscope_eargs Σ ξ.
Proof.
  intros h ih.
  rewrite Forall_forall. intros σ hσ.
  rewrite Forall_forall. intros u hu.
  eapply In_nth_error in hσ as [M hM].
  eapply In_nth_error in hu as [x hx].
  destruct ih as [_ [ih e]]. red in ih. specialize (ih M).
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
Qed.

Lemma typing_gscope Σ Ξ Γ t A :
  Σ ;; Ξ | Γ ⊢ t : A →
  gscope Σ t.
Proof.
  intro h. induction h using typing_ind.
  all: try solve [ econstructor ; eauto ].
  - econstructor. 1: eassumption.
    eapply inst_typing_gscope_ih. all: eassumption.
  - assumption.
Qed.

Lemma inst_typing_gscope Σ Ξ Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  gscope_eargs Σ ξ.
Proof.
  intros h.
  eapply inst_typing_gscope_ih. 1: eassumption.
  destruct h as (he & ht & e).
  split. 2: split.
  - assumption.
  - intros M E ξ' eM.
    specialize (ht _ _ _ eM). destruct ht as (? & Ξ'' & Δ & R & eE & ho & ht).
    split. 1: assumption.
    eexists _,_,_. split. 1 : eassumption.
    split. 1: assumption.
    intros x A hx. specialize ht with (1 := hx).
    unfold eget in *. destruct (nth_error ξ _) as [σ |] eqn:e1. 2: constructor.
    destruct (nth_error σ _) eqn:e2. 2: constructor.
    eapply typing_gscope. eassumption.
  - assumption.
Qed.

Lemma wf_gscope Σ Ξ Γ :
  wf Σ Ξ Γ →
  Forall (gscope Σ) Γ.
Proof.
  induction 1 as [| Γ i A hΓ ih hA]. 1: constructor.
  econstructor. 2: assumption.
  eapply typing_gscope. eassumption.
Qed.

Inductive gscope_parg Σ : parg → Prop :=
| gscope_pvar : gscope_parg Σ pvar
| gscope_pforce t : gscope Σ t → gscope_parg Σ (pforce t)
| gscope_psymb x l : Forall (gscope_parg Σ) l → gscope_parg Σ (psymb x l).

Definition gscope_pat Σ p :=
  Forall (gscope_parg Σ) p.(pat_args).

Definition gscope_rule Σ rule :=
  Forall (gscope Σ) rule.(cr_env) ∧
  gscope_pat Σ rule.(cr_pat) ∧
  gscope Σ rule.(cr_rep) ∧
  gscope Σ rule.(cr_typ).

Lemma rule_typing_gscope Σ Ξ Δ r :
  rule_typing Σ Ξ Δ r →
  gscope_rule Σ r.
Proof.
  intros (hctx & [i hty] & hl & hr).
  eapply typing_gscope in hl as gl, hr as gr, hty.
  eapply wf_gscope in hctx.
  unfold gscope_rule. intuition eauto.
  (* We need inversions now *)
Admitted.

Lemma rules_typing_gscope Σ Ξ Δ R :
  Forall (rule_typing Σ Ξ Δ) R →
  Forall (gscope_rule Σ) R.
Proof.
  eauto using Forall_impl, rule_typing_gscope.
Qed.

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
  (∀ M x, P (assm M x)) →
  ∀ t, gscope Σ t → P t.
Proof.
  intros Σ P hvar hsort hpi hlam happ hconst hassm.
  fix aux 2. move aux at top.
  intros t h. destruct h as [| | | | | ????? hc h |].
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

  (* TODO MOVE *)
  (* Lemma scoped_rule_tm M ξ δ k t :
    scoped k (rule_tm M ξ δ k t) = true.
  Proof.
    unfold rule_tm.
    unfold delocal_lift.
    Search scoped subst_term. *)

  (* TODO MOVE *)
  (* Lemma rule_typing_scoped_lhs Ξ' Δ rule M ξ :
    rule_typing Σ Ξ' Δ rule →
    scoped (length rule.(cr_env)) (rule_lhs M ξ (length Δ) rule) = true.
  Proof.
    intros (henv & [i hty] & hl & hr).
    eapply typing_scoped in hl.
    rewrite length_app in hl.
    unfold rule_lhs. *)

  (* Maybe let's just type things *)

  Lemma inst_equations_inline_ih Ξ Ξ' Γ ξ :
    (* inst_equations Σ Ξ Γ ξ Ξ' → *)
    inst_equations_ Σ (λ Γ u v, Σᵗ ;; ⟦ Ξ ⟧e | ⟦ Γ ⟧* ⊢ ⟦ u ⟧ ≡ ⟦ v ⟧) Γ ξ Ξ' →
    inst_equations Σᵗ ⟦ Ξ ⟧e ⟦ Γ ⟧* ⟦ ξ ⟧× ⟦ Ξ' ⟧e.
  Proof.
    intros ih.
    intros E M ξ' hM.
    rewrite ectx_get_map in hM.
    destruct ectx_get as [[E' ξ'']|] eqn:hM'. 2: discriminate.
    cbn in hM. inversion hM. subst. clear hM.
    specialize (ih _ _ _ hM') as (Ξ'' & Δ' & R & e & ih).
    eexists _,_,_. split. 1: eauto.
    intros n rule hn m δ Θ lhs0 rhs0 hl hr. cbn.
    rewrite nth_error_map in hn.
    destruct (nth_error R n) as [rule' |] eqn:hn'. 2: discriminate.
    cbn in hn. inversion hn. subst. clear hn.
    eapply valid_ext in e as h. 2: admit.
    destruct h as (? & ? & hR).
    eapply nth_error_In in hn' as hrule.
    rewrite Forall_forall in hR. specialize hR with (1 := hrule).
    (* subst lhs0 rhs0. *)
    (* rewrite <- inline_rule_lhs in hl. rewrite <- inline_rule_rhs in hr. *)
    (* eapply scoped_inline in hl, hr. *)
    (* We would need the reverse!
      But this is not true because we can't invert scoping for einst.
      Instead we could require gwf and then get the scoping conditions this way.
    *)
    (* specialize ih with (1 := hn') (2 := hl) (3 := hr). cbn in ih. *)
  Admitted.

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
      econstructor.
      + eapply ectx_get_inline. eassumption.
      + eapply hext. eassumption.
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
Notation "⟦ r ⟧r⟨ k ⟩" := (inline_crule k r).
Notation "⟦ R ⟧R⟨ k ⟩" := (map (inline_crule k) R).
Notation "⟦ p ⟧p⟨ k ⟩" := (inline_pat k p).

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

Lemma inline_parg_ext Σ p κ κ' :
  gscope_parg Σ p →
  eq_gscope Σ κ κ' →
  inline_parg κ p = inline_parg κ' p.
Proof.
  intros hp he.
  induction hp.
  - reflexivity.
  - cbn. f_equal. eapply inline_ext. all: eauto.
  - cbn. f_equal. eapply map_ext_Forall. eapply Forall_impl. 2: eassumption.
    (* Need stronger ih *)
    admit.
Admitted.

Lemma inline_pat_ext Σ p κ κ' :
  gscope_pat Σ p →
  eq_gscope Σ κ κ' →
  ⟦ p ⟧p⟨ κ ⟩ = ⟦ p ⟧p⟨ κ' ⟩.
Proof.
  intros hp he.
  unfold gscope_pat in hp.
  destruct p as [a l].
  unfold inline_pat. cbn in *. f_equal.
  eapply map_ext_Forall. eapply Forall_impl. 2: eassumption.
  intros. eapply inline_parg_ext. all: eassumption.
Qed.

Lemma inline_crule_ext Σ rule κ κ' :
  gscope_rule Σ rule →
  eq_gscope Σ κ κ' →
  ⟦ rule ⟧r⟨ κ ⟩ = ⟦ rule ⟧r⟨ κ' ⟩.
Proof.
  intros [? [? []]] he.
  destruct rule as [Θ p r A].
  unfold inline_crule. cbn in *. f_equal.
  - eapply inline_list_ext. all: eassumption.
  - eapply inline_pat_ext. all: eassumption.
  - eapply inline_ext. all: eassumption.
  - eapply inline_ext. all: eassumption.
Qed.

Lemma inline_rules_ext Σ R κ κ' :
  Forall (gscope_rule Σ) R →
  eq_gscope Σ κ κ' →
  ⟦ R ⟧R⟨ κ ⟩ = ⟦ R ⟧R⟨ κ' ⟩.
Proof.
  intros hR he.
  eapply map_ext_Forall. eapply Forall_impl. 2: eassumption.
  intros. eapply inline_crule_ext. all: eassumption.
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
    + inversion eE. subst. reflexivity.
    + eauto.
  - cbn in *. destruct (E =? c)%string eqn:e. 1: discriminate.
    rewrite ih. 2: assumption.
    assert (eg : eq_gscope Σ ⟦ Σ ⟧κ (gcons c ⟦ t ⟧⟨ ⟦ Σ ⟧κ ⟩ ⟦ Σ ⟧κ)).
    { eapply eq_gscope_gcons. assumption. }
    eapply valid_ext in eE as h'. 2: assumption.
    destruct h' as (hΞ' & hΔ & hR).
    f_equal. f_equal.
    + eapply inline_ectx_ext. all: eassumption.
    + eapply inline_ctx_ext. all: eassumption.
    + eapply inline_rules_ext. 2: eassumption.
      eapply rules_typing_gscope. eassumption.
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
