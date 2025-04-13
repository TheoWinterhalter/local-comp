(** Global scoping

  It tracks whether [c] in [const c ξ] always points to [Σ].
  It doesn't ensure anything about [assm].

**)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing BasicMetaTheory.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

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

Lemma gscope_apps_inv Σ f l :
  gscope Σ (apps f l) →
  gscope Σ f ∧ Forall (gscope Σ) l.
Proof.
  intros h.
  induction l as [| x l ih] in f, h |- *.
  - cbn in h. intuition constructor.
  - cbn in h. eapply ih in h as [happ hl].
    inversion happ. subst.
    split.
    + assumption.
    + constructor. all: assumption.
Qed.

Lemma gscope_plinst_args_inv (f : parg → nat → term * nat) Σ pl l n r :
  Forall (λ p, ∀ k t m, f p k = (t, m) → gscope Σ t → gscope_parg Σ p) pl →
  fold_left (λ '(acc, k) p, let '(t, m) := f p k in (t :: acc, m)) pl r = (l, n) →
  Forall (gscope Σ) l →
  Forall (gscope Σ) (fst r) ∧ Forall (gscope_parg Σ) pl.
Proof.
  intros hl e h.
  induction hl as [| p pl hp hl ih] in r, l, n, e, h |- *.
  - cbn in e. subst. cbn. intuition constructor.
  - cbn in e. eapply ih in e as h'. 2: assumption.
    destruct r as [acc k]. cbn.
    destruct f as [t m] eqn:e'. cbn in h'.
    rewrite Forall_cons_iff in h' |- *.
    intuition eauto.
Qed.

Lemma gscope_plinst_arg_inv Σ p k t m :
  plinst_arg p k = (t, m) →
  gscope Σ t →
  gscope_parg Σ p.
Proof.
  intros e ht.
  induction p using parg_ind in k, t, m, ht, e |- *.
  - constructor.
  - constructor. cbn in e. inversion e. assumption.
  - cbn in e. destruct plinst_args eqn: es.
    inversion e. subst. clear e.
    constructor.
    apply gscope_apps_inv in ht as [_ ht].
    eapply Forall_rev in ht. rewrite rev_involutive in ht.
    eapply gscope_plinst_args_inv in es. all: intuition eauto.
Qed.

Lemma gscope_plinst_inv Σ k p :
  gscope Σ (plinst k p) →
  gscope_pat Σ p.
Proof.
  intros h.
  unfold plinst in h.
  destruct plinst_args eqn:e.
  apply gscope_apps_inv in h as [_ h].
  eapply Forall_rev in h. rewrite rev_involutive in h.
  unfold gscope_pat.
  eapply gscope_plinst_args_inv in e. 1,3: intuition eauto.
  rewrite Forall_forall. intros. eauto using gscope_plinst_arg_inv.
Qed.

Lemma rule_typing_gscope Σ Ξ Δ r :
  rule_typing Σ Ξ Δ r →
  gscope_rule Σ r.
Proof.
  intros (hctx & [i hty] & hl & hr).
  eapply typing_gscope in hl as gl, hr as gr, hty.
  eapply wf_gscope in hctx.
  eapply gscope_plinst_inv in gl.
  rewrite Forall_app in hctx.
  unfold gscope_rule. intuition eauto.
Qed.

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

Lemma gscope_parg_ind_alt :
  ∀ (Σ : gctx) (P : parg → Prop),
    P pvar →
    (∀ t, gscope Σ t → P (pforce t)) →
    (∀ x l, Forall (gscope_parg Σ) l → Forall P l → P (psymb x l)) →
    ∀ p, gscope_parg Σ p → P p.
Proof.
  intros Σ P hvar hforce hsymb.
  fix aux 2. move aux at top.
  intros p h. destruct h as [| | x l h ].
  3:{
    eapply hsymb. 1: assumption.
    revert l h.
    fix aux1 2.
    intros l h. destruct h as [| p l hp hl].
    - constructor.
    - constructor. all: eauto.
  }
  all: match goal with h : _ |- _ => solve [ eapply h ; eauto ] end.
Qed.
