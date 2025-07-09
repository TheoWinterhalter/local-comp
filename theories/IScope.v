(** * Interface scoping

  It tracks whether [x] in [assm x] always points to [Ξ].

*)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing BasicMetaTheory.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

(** Better induction principle for [iscope] *)

Lemma iscope_ind_alt :
  ∀ Ξ (P : term → Prop),
  (∀ x, P (var x)) →
  (∀ i, P (Sort i)) →
  (∀ A B, iscope Ξ A → P A → iscope Ξ B → P B → P (Pi A B)) →
  (∀ A t, iscope Ξ A → P A → iscope Ξ t → P t → P (lam A t)) →
  (∀ u v, iscope Ξ u → P u → iscope Ξ v → P v → P (app u v)) →
  (∀ c ξ,
    iscope_instance Ξ ξ →
    Forall (OnSome P) ξ →
    P (const c ξ)
  ) →
  (∀ x A,
    ictx_get Ξ x = Some (Assm A) →
    P (assm x)
  ) →
  ∀ t, iscope Ξ t → P t.
Proof.
  intros Ξ P hvar hsort hpi hlam happ hconst hassm.
  fix aux 2. move aux at top.
  intros t h. destruct h as [| | | | | c ξ h |].
  6:{
    eapply hconst. 1: assumption.
    revert ξ h.
    fix aux1 2.
    intros ξ h. destruct h as [| u ξ hu hξ].
    - constructor.
    - constructor. 2: eauto.
      destruct hu.
      + constructor.
      + constructor. eauto.
  }
  all: match goal with h : _ |- _ => solve [ eapply h ; eauto ] end.
Qed.

Lemma inst_typing_iscope_ih conv Ξ ξ Ξ' :
  inst_typing_ conv (λ t _, iscope Ξ t) ξ Ξ' →
  iscope_instance Ξ ξ.
Proof.
  eauto using inst_typing_prop_ih.
Qed.

Lemma typing_iscope Σ Ξ Γ t A :
  Σ ;; Ξ | Γ ⊢ t : A →
  iscope Ξ t.
Proof.
  intro h. induction h using typing_ind.
  all: try solve [ econstructor ; eauto ].
  - econstructor.
    eauto using inst_typing_iscope_ih.
  - assumption.
Qed.

Definition eq_inst_on Ξ (ξ ξ' : instance) :=
  ∀ x A,
    ictx_get Ξ x = Some (Assm A) →
    iget ξ x = iget ξ' x.

Lemma eq_inst_on_lift Ξ ξ ξ' :
  eq_inst_on Ξ ξ ξ' →
  eq_inst_on Ξ (lift_instance ξ) (lift_instance ξ').
Proof.
  intros h. intros x A e.
  rewrite 2!iget_ren. f_equal.
  eauto.
Qed.

Lemma inst_ext_iscope Ξ ξ ξ' t :
  eq_inst_on Ξ ξ ξ' →
  iscope Ξ t →
  inst ξ t = inst ξ' t.
Proof.
  intros he h.
  induction h in ξ, ξ', he |- * using iscope_ind_alt.
  all: try solve [ cbn ; eauto ].
  all: try solve [ cbn ; f_equal ; eauto using eq_inst_on_lift ].
  cbn. f_equal.
  apply map_ext_Forall. eapply Forall_impl. 2: eassumption.
  intros o ho.
  rewrite OnSome_onSome in ho. apply onSome_onSomeT in ho.
  apply option_map_ext_onSomeT. eapply onSomeT_impl. 2: eassumption.
  cbn. auto.
Qed.

Lemma iscope_ren Ξ ρ t :
  iscope Ξ t →
  iscope Ξ (ρ ⋅ t).
Proof.
  intros h.
  induction h in ρ |- * using iscope_ind_alt.
  all: try solve [ cbn ; econstructor ; eauto ].
  cbn. econstructor.
  change @core.option_map with option_map.
  apply Forall_map. eapply Forall_impl. 2: eassumption.
  setoid_rewrite OnSome_onSome.
  intros ??. apply onSome_map.
  eapply onSome_impl. 2: eassumption.
  auto.
Qed.

Lemma iscope_instance_lift Ξ ξ :
  iscope_instance Ξ ξ →
  iscope_instance Ξ (lift_instance ξ).
Proof.
  intros h.
  apply Forall_map.
  eapply Forall_impl. 2: exact h.
  intros ??. rewrite OnSome_onSome in *.
  apply onSome_map.
  eapply onSome_impl. 2: eassumption.
  auto using iscope_ren.
Qed.

Lemma iscope_instance_inst_ih Ξ ξ ξ' :
  All (onSomeT (λ t, ∀ ξ, iscope_instance Ξ ξ → iscope Ξ (inst ξ t))) ξ' →
  iscope_instance Ξ ξ →
  iscope_instance Ξ (inst_instance ξ ξ').
Proof.
  intros h hξ.
  apply Forall_map. apply All_Forall.
  eapply All_impl. 2: eassumption.
  intros ??. rewrite OnSome_onSome. apply onSomeT_onSome.
  apply onSomeT_map. eapply onSomeT_impl. 2: eassumption.
  cbn. auto.
Qed.

Lemma iscope_inst Ξ t ξ :
  iscope_instance Ξ ξ →
  iscope Ξ (inst ξ t).
Proof.
  intros h.
  induction t in ξ, h |- * using term_rect.
  all: try solve [ cbn ; econstructor ; eauto using iscope_instance_lift ].
  - cbn. econstructor.
    eauto using iscope_instance_inst_ih.
  - cbn. unfold iget.
    destruct nth_error as [[]|] eqn:e. 2,3: econstructor.
    apply nth_error_In in e.
    rewrite Forall_forall in h.
    specialize h with (1 := e). rewrite OnSome_onSome in h. cbn in h.
    assumption.
Qed.
