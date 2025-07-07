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

Section iscope.

  Context (Ξ : ictx).

  Inductive iscope : term → Prop :=
  | iscope_var x : iscope (var x)
  | iscope_sort i : iscope (Sort i)
  | iscope_pi A B : iscope A → iscope B → iscope (Pi A B)
  | iscope_lam A t : iscope A → iscope t → iscope (lam A t)
  | iscope_app u v : iscope u → iscope v → iscope (app u v)
  | iscope_const c ξ :
      Forall (OnSome (iscope)) ξ →
      iscope (const c ξ)
  | iscope_assm x A :
      ictx_get Ξ x = Some (Assm A) →
      iscope (assm x).

End iscope.

Notation iscope_instance Ξ ξ := (Forall (OnSome (iscope Ξ)) ξ).

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

Lemma inst_typing_iscope_ih Σ Ξ Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ _ t _, iscope Ξ t) Γ ξ Ξ' →
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
