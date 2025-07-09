(** Reduction

  We define reduction for the language as a way to study decidability of
  conversion and type checking.
  Those will be achieved with some assumptions on the reduction relation,
  namely confluence and type preservation.

*)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing BasicMetaTheory
  GScope Inversion Confluence IScope.
From Stdlib Require Import Setoid Morphisms Relation_Definitions
  Relation_Operators.
From Equations Require Import Equations.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Require Import Equations.Prop.DepElim.

Section Red.

  Reserved Notation "u ↦ v"
    (at level 80).

  Context (Σ : gctx) (Ξ : ictx).

  Inductive red1 : term → term → Prop :=

  (** Computation rules *)

  | red_beta A t u : app (lam A t) u ↦ t <[ u .. ]

  | red_unfold c ξ Ξ' A t :
      Σ c = Some (Def Ξ' A t) →
      closed t = true →
      const c ξ ↦ inst ξ t

  | red_rule n rl σ :
      ictx_get Ξ n = Some (Comp rl) →
      let Θ := rl.(cr_env) in
      let k := length Θ in
      let lhs := rl.(cr_pat) in
      let rhs := rl.(cr_rep) in
      scoped k lhs = true →
      scoped k rhs = true →
      lhs <[ σ ] ↦ rhs <[ σ ]

  (** Congruence rules *)

  | red_Pi_dom A B A' :
      A ↦ A' →
      Pi A B ↦ Pi A' B

  | red_Pi_cod A B B' :
      B ↦ B' →
      Pi A B ↦ Pi A B'

  | red_lam_dom A t A' :
      A ↦ A' →
      lam A t ↦ lam A' t

  | red_lam_body A t t' :
      t ↦ t' →
      lam A t ↦ lam A t'

  | red_app_fun u v u' :
      u ↦ u' →
      app u v ↦ app u' v

  | red_app_arg u v v' :
      v ↦ v' →
      app u v ↦ app u v'

  | red_const c ξ ξ' :
      OnOne2 (some_rel (λ u v, u ↦ v)) ξ ξ' →
      const c ξ ↦ const c ξ'

  where "u ↦ v" := (red1 u v).

  Lemma red1_ind_alt :
    ∀ (P : term → term → Prop),
      (∀ A t u, P (app (lam A t) u) (t <[ u..])) →
      (∀ c ξ Ξ' A t,
        Σ c = Some (Def Ξ' A t) →
        closed t = true →
        P (const c ξ) (inst ξ t)
      ) →
      (∀ n rl σ,
        ictx_get Ξ n = Some (Comp rl) →
        let Θ := rl.(cr_env) in
        let k := length Θ in
        let lhs := rl.(cr_pat) in
        let rhs := rl.(cr_rep) in
        scoped k lhs = true →
        scoped k rhs = true →
        P (lhs <[ σ]) (rhs <[ σ])
      ) →
      (∀ A B A',
        A ↦ A' →
        P A A' →
        P (Pi A B) (Pi A' B)
      ) →
      (∀ A B B', B ↦ B' → P B B' → P (Pi A B) (Pi A B')) →
      (∀ A t A', A ↦ A' → P A A' → P (lam A t) (lam A' t)) →
      (∀ A t t', t ↦ t' → P t t' → P (lam A t) (lam A t')) →
      (∀ u v u', u ↦ u' → P u u' → P (app u v) (app u' v)) →
      (∀ u v v', v ↦ v' → P v v' → P (app u v) (app u v')) →
      (∀ c ξ ξ',
        OnOne2 (some_rel (λ u v : term, u ↦ v)) ξ ξ' →
        OnOne2 (some_rel P) ξ ξ' →
        P (const c ξ) (const c ξ')
      ) →
      ∀ u v, u ↦ v → P u v.
  Proof.
    intros P hbeta hunf hrl hpid hpic hlamd hlamb happf happa hconst.
    fix aux 3. move aux at top.
    intros u v h. destruct h.
    10:{
      eapply hconst. 1: assumption.
      revert ξ ξ' H. fix aux1 3.
      intros ξ ξ' h. destruct h as [ o o' ξ h | o ξ ξ' h ].
      - constructor. destruct h. constructor. auto.
      - constructor. auto.
    }
    all: match goal with h : _ |- _ => eapply h end.
    all: eauto.
  Qed.

End Red.

Notation "Σ ;; Ξ ⊢ u ↦ v" :=
  (red1 Σ Ξ u v)
  (at level 80, u, v at next level).

(** Reflexive transitive closure *)

Definition red Σ Ξ := clos_refl_trans (λ u v, Σ ;; Ξ ⊢ u ↦ v).

Notation "Σ ;; Ξ ⊢ u ↦* v" :=
  (red Σ Ξ u v)
  (at level 80, u, v at next level).

(** Equivalence *)

Definition equiv Σ Ξ := clos_refl_sym_trans _ (λ u v, Σ ;; Ξ ⊢ u ↦ v).

Notation "Σ ;; Ξ ⊢ u ↮ v" :=
  (equiv Σ Ξ u v)
  (at level 80, u, v at next level).

#[export] Instance equiv_refl Σ Ξ : Reflexive (equiv Σ Ξ).
Proof.
  intros u.
  eapply rst_refl.
Qed.

#[export] Instance equiv_sym Σ Ξ : Symmetric (equiv Σ Ξ).
Proof.
  intros u v h.
  eapply rst_sym. eassumption.
Qed.

#[export] Instance equiv_trans Σ Ξ : Transitive (equiv Σ Ξ).
Proof.
  intros u v w h1 h2.
  eapply rst_trans. all: eassumption.
Qed.

Lemma red_ind Σ Ξ f x y :
  (∀ x y, Σ ;; Ξ ⊢ x ↦ y → Σ ;; Ξ ⊢ f x ↦* f y) →
  Σ ;; Ξ ⊢ x ↦* y →
  Σ ;; Ξ ⊢ f x ↦* f y.
Proof.
  intros hred h.
  eapply rt_step_ind. all: eauto.
Qed.

Lemma equiv_red_ind Σ Ξ f x y :
  (∀ x y, Σ ;; Ξ ⊢ x ↦ y → Σ ;; Ξ ⊢ f x ↮ f y) →
  Σ ;; Ξ ⊢ x ↮ y →
  Σ ;; Ξ ⊢ f x ↮ f y.
Proof.
  intros hred h.
  eapply rst_step_ind. all: eauto.
Qed.

(** Notion of confluence *)

Definition red_confluent Σ Ξ :=
  confluent (red1 Σ Ξ).

(** Joinability *)

Definition red_joinable Σ Ξ :=
  joinable (red Σ Ξ).

Notation "Σ ;; Ξ ⊢ u ⋈ v" :=
  (red_joinable Σ Ξ u v)
  (at level 80, u, v at next level).

(** Assuming confluence, equivalence is the same as joinability *)

Lemma equiv_join Σ Ξ u v :
  red_confluent Σ Ξ →
  Σ ;; Ξ ⊢ u ↮ v →
  Σ ;; Ξ ⊢ u ⋈ v.
Proof.
  intros hc h.
  induction h as [u v hr | u | u v h ih | u v w h1 ih1 h2 ih2 ].
  - exists v. split.
    + apply rt_step. assumption.
    + apply rt_refl.
  - exists u. split. all: apply rt_refl.
  - destruct ih as [w [h1 h2]]. exists w. intuition auto.
  - destruct ih1 as [w1 [? hv1]], ih2 as [w2 [hv2 ?]].
    eapply hc in hv1 as hw. specialize hw with (1 := hv2).
    destruct hw as [w3 []].
    exists w3. split.
    + eapply rt_trans. all: eassumption.
    + eapply rt_trans. all: eassumption.
Qed.

(** Conversion is included in the congruence closure of reduction *)

Lemma equiv_Pi Σ Ξ A A' B B' :
  Σ ;; Ξ ⊢ A ↮ A' →
  Σ ;; Ξ ⊢ B ↮ B' →
  Σ ;; Ξ ⊢ Pi A B ↮ Pi A' B'.
Proof.
  intros hA hB.
  transitivity (Pi A B').
  - eapply equiv_red_ind. 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
  - eapply equiv_red_ind with (f := λ x, Pi x B'). 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
Qed.

Lemma equiv_lam Σ Ξ A A' t t' :
  Σ ;; Ξ ⊢ A ↮ A' →
  Σ ;; Ξ ⊢ t ↮ t' →
  Σ ;; Ξ ⊢ lam A t ↮ lam A' t'.
Proof.
  intros hA ht.
  transitivity (lam A t').
  - eapply equiv_red_ind. 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
  - eapply equiv_red_ind with (f := λ x, lam x t'). 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
Qed.

Lemma equiv_app Σ Ξ u u' v v' :
  Σ ;; Ξ ⊢ u ↮ u' →
  Σ ;; Ξ ⊢ v ↮ v' →
  Σ ;; Ξ ⊢ app u v ↮ app u' v'.
Proof.
  intros hu hv.
  transitivity (app u v').
  - eapply equiv_red_ind. 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
  - eapply equiv_red_ind with (f := λ x, app x v'). 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
Qed.

Lemma equiv_const Σ Ξ c ξ ξ' :
  Forall2 (option_rel (λ u v, Σ ;; Ξ ⊢ u ↮ v)) ξ ξ' →
  Σ ;; Ξ ⊢ const c ξ ↮ const c ξ'.
Proof.
  intros hξ.
  eapply Forall2_impl in hξ. 2: eapply option_rel_rst_some_rel.
  eapply Forall2_impl in hξ.
  2:{ eapply clos_refl_sym_trans_incl. intros ??. eapply some_rel_rst_comm. }
  eapply Forall2_impl in hξ. 2: eapply Operators_Properties.clos_rst_idempotent.
  eapply Forall2_rst_OnOne2 in hξ.
  eapply clos_refl_sym_trans_incl in hξ.
  2:{ intros ??. eapply OnOne2_rst_comm. }
  eapply Operators_Properties.clos_rst_idempotent in hξ.
  eapply rst_step_ind. 2: eassumption.
  intros. apply rst_step.
  constructor. assumption.
Qed.

Lemma conv_equiv Σ Ξ u v :
  Σ ;; Ξ ⊢ u ≡ v →
  Σ ;; Ξ ⊢ u ↮ v.
Proof.
  intros h.
  induction h using conversion_ind.
  all: try solve [ econstructor ; econstructor ; eauto ].
  - eapply equiv_Pi. all: eassumption.
  - eapply equiv_lam. all: eassumption.
  - eapply equiv_app. all: eassumption.
  - eapply equiv_const. assumption.
Qed.

(** One-step reduction embeds in conversion *)

#[export] Instance Reflexive_conversion Σ Ξ :
  Reflexive (conversion Σ Ξ).
Proof.
  intros u. ttconv.
Qed.

Lemma inst_typing_Forall_typed Σ Ξ Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  Forall (onSome (λ t, ∃ A, Σ ;; Ξ | Γ ⊢ t : A)) ξ.
Proof.
  induction 1; try constructor.
  all: apply Forall_app; split; auto.
  all: repeat constructor.
  cbn.
  eexists; eassumption.
Qed.

(* Definition factor_rules (Σ : gctx) Ξ :=
  ∀ M E ξ' Ξ' Δ R n rule σ Γ A,
    ictx_get Ξ M = Some (E, ξ') →
    Σ E = Some (Ext Ξ' Δ R) →
    nth_error R n = Some rule →
    let δ := length Δ in
    let lhs := rlhs M ξ' δ rule in
    let lhs' := elhs M ξ' δ (crule_eq rule) in
    Σ ;; Ξ | Γ ⊢ lhs <[ σ ] : A →
    ∃ θ, lhs <[ σ ] = lhs' <[ θ ]. *)

Section const_eqs.

  Context (Σ : gctx) (Ξ : ictx).

  Fixpoint const_eqs t {struct t} :=
    match t with
    | var x => True
    | Sort s => True
    | Pi A B => const_eqs A ∧ const_eqs B
    | lam A b => const_eqs A ∧ const_eqs b
    | app u v => const_eqs u ∧ const_eqs v
    | const c ξ =>
        rForall (onSome const_eqs) ξ ∧
        (∃ Ξ' A t, Σ c = Some (Def Ξ' A t) ∧ inst_equations Σ Ξ ξ Ξ')
    | assm x => True
    end.

End const_eqs.

(** Typing implies const_eqs *)

Lemma typing_const_eqs Σ Ξ Γ t A :
  Σ ;; Ξ | Γ ⊢ t : A →
  const_eqs Σ Ξ t.
Proof.
  intros h.
  induction h using typing_ind.
  all: try solve [ cbn in * ; intuition eauto ].
  cbn. split.
  - rewrite rForall_Forall.
    eapply Forall_impl. 1:{ intros ??. rewrite <- OnSome_onSome. eauto. }
    eapply inst_typing_prop_ih. all: eassumption.
  - eexists _,_,_. split. 1: eassumption.
    eapply inst_typing_equations; eassumption.
Qed.

Lemma red1_conv_inst_ih Σ Ξ ξ ξ' :
  Forall (onSome (const_eqs Σ Ξ)) ξ →
  OnOne2 (some_rel (red1 Σ Ξ)) ξ ξ' →
  OnOne2 (some_rel (λ u v, const_eqs Σ Ξ u → Σ ;; Ξ ⊢ u ≡ v)) ξ ξ' →
  Forall2 (option_rel (conversion Σ Ξ)) ξ ξ'.
Proof.
  intros hξ ? ?.
  eapply OnOne2_and_Forall_l in hξ. 2: eassumption.
  apply OnOne2_refl_Forall2. 1: exact _.
  eapply OnOne2_impl. 2: eassumption.
  intros ?? [h1 h2]. apply some_rel_option_rel.
  destruct h2. cbn in h1. constructor.
  eauto.
Qed.

Lemma red1_conv Σ Ξ u v :
  const_eqs Σ Ξ u →
  Σ ;; Ξ ⊢ u ↦ v →
  Σ ;; Ξ ⊢ u ≡ v.
Proof.
  intros hu h.
  induction h using red1_ind_alt.
  all: try solve [ cbn in hu ; intuition ttconv ].
  - cbn in hu. destruct hu as (? & ? & ? & ? & ? & ?).
    eqtwice. subst.
    econstructor. all: eassumption.
  - econstructor. all: eassumption.
  - cbn in hu. destruct hu as (hξ & _).
    rewrite rForall_Forall in hξ.
    constructor.
    eauto using red1_conv_inst_ih.
Qed.

Lemma Forall_funct A (P Q : A → Prop) l :
  Forall P l →
  Forall (λ x, P x → Q x) l →
  Forall Q l.
Proof.
  intros h hi.
  rewrite Forall_forall in *.
  eauto.
Qed.

Lemma const_eqs_ren Σ Ξ t ρ :
  const_eqs Σ Ξ t →
  const_eqs Σ Ξ (ρ ⋅ t).
Proof.
  intros h.
  induction t in ρ, h |- * using term_rect.
  all: try solve [ cbn in * ; intuition eauto ].
  cbn in *. destruct h as (h & Ξ' & A & t & e & h').
  rewrite rForall_Forall in *.
  change @core.option_map with option_map.
  split.
  - apply Forall_map. eapply Forall_funct. 1: eassumption.
    apply All_Forall. eapply All_impl. 2: eassumption.
    intros o ho ho'.
    apply onSome_onSomeT in ho'. apply onSomeT_onSome.
    eapply onSomeT_prod in ho. 2: eassumption.
    apply onSomeT_map.
    eapply onSomeT_impl. 2: eassumption.
    cbn. intuition eauto.
  - eexists _,_,_. split. 1: eassumption.
    eauto using inst_equations_ren_ih, inst_equations_prop, conv_ren.
Qed.

Lemma const_eqs_shift Σ Ξ σ :
  (∀ n, const_eqs Σ Ξ (σ n)) →
  ∀ n, const_eqs Σ Ξ (up_term σ n).
Proof.
  intros h n.
  destruct n.
  - cbn. constructor.
  - cbn. unfold core.funcomp.
    apply const_eqs_ren. auto.
Qed.

Lemma const_eqs_subst Σ Ξ t σ :
  (∀ n, const_eqs Σ Ξ (σ n)) →
  const_eqs Σ Ξ t →
  const_eqs Σ Ξ (t <[ σ ]).
Proof.
  intros hσ h.
  induction t in σ, hσ, h |- * using term_rect.
  all: try solve [ cbn in * ; intuition eauto using const_eqs_shift ].
  cbn in *. destruct h as (h & Ξ' & A & t & e & h').
  rewrite rForall_Forall in *.
  change @core.option_map with option_map.
  split.
  - apply Forall_map. eapply Forall_funct. 1: eassumption.
    apply All_Forall. eapply All_impl. 2: eassumption.
    intros o ho ho'.
    apply onSome_onSomeT in ho'. apply onSomeT_onSome.
    eapply onSomeT_prod in ho. 2: eassumption.
    apply onSomeT_map.
    eapply onSomeT_impl. 2: eassumption.
    cbn. intuition eauto.
  - eexists _,_,_. split. 1: eassumption.
    eauto using inst_equations_subst_ih, inst_equations_prop, conv_subst.
Qed.

Lemma const_eqs_inst Σ Ξ Ξ' ξ t k :
  inst_equations Σ Ξ ξ Ξ' →
  Forall (onSome (const_eqs Σ Ξ)) ξ →
  const_eqs Σ Ξ' t →
  let rξ := liftn k ξ in
  const_eqs Σ Ξ (inst rξ t).
Proof.
  intros heξ hξ h. cbn.
  induction t in Ξ', ξ, heξ, hξ, h, k |- * using term_rect.
  all: try solve [ cbn in * ; intuition eauto ].
  - cbn in *. intuition eauto.
    rewrite lift_liftn. eauto.
  - cbn in *. intuition eauto.
    rewrite lift_liftn. eauto.
  - cbn in *. rewrite rForall_Forall in *.
    destruct h as (h' & ? & ? & ? & e & h).
    split.
    + apply Forall_map. eapply Forall_funct. 1: eassumption.
      apply All_Forall. eapply All_impl. 2: eassumption.
      intros o ho ho'.
      apply onSome_onSomeT in ho'. apply onSomeT_onSome.
      eapply onSomeT_prod in ho. 2: eassumption.
      apply onSomeT_map.
      eapply onSomeT_impl. 2: eassumption.
      cbn. intuition eauto.
    + eexists _,_,_. split. 1: eassumption.
      eauto using inst_equations_inst_ih, inst_equations_prop, conv_inst.
  - cbn. rewrite iget_ren. apply const_eqs_ren.
    unfold iget. destruct (nth_error ξ _) as [[?|] |] eqn:e1. 2,3: constructor.
    rewrite Forall_forall in hξ.
    apply nth_error_In in e1. specialize hξ with (1 := e1).
    cbn in hξ. assumption.
Qed.

Lemma const_eqs_inst_closed Σ Ξ Ξ' ξ t :
  inst_equations Σ Ξ ξ Ξ' →
  Forall (onSome (const_eqs Σ Ξ)) ξ →
  const_eqs Σ Ξ' t →
  const_eqs Σ Ξ (inst ξ t).
Proof.
  intros heξ hξ h.
  eapply const_eqs_inst with (k := 0) in h. 2,3: eassumption.
  cbn in h.
  rewrite ren_instance_id_ext in h. 2: auto.
  assumption.
Qed.

Definition preserves_const_eqs Σ Ξ :=
  ∀ n rl σ,
    ictx_get Ξ n = Some (Comp rl) →
    let lhs := rl.(cr_pat) in
    let rhs := rl.(cr_rep) in
    const_eqs Σ Ξ (lhs <[ σ ]) →
    const_eqs Σ Ξ (rhs <[ σ ]).

Definition const_const_eqs (Σ : gctx) :=
  ∀ c Ξ A t,
    Σ c = Some (Def Ξ A t) →
    const_eqs Σ Ξ t.

(* TODO MOVE *)
Lemma inst_equations_conv Σ Ξ ξ ξ' Ξ' :
  inst_equations Σ Ξ ξ Ξ' →
  Forall2 (option_rel (conversion Σ Ξ)) ξ ξ' →
  inst_equations Σ Ξ ξ' Ξ'.
Proof.
  intros h he.
  intros x rl hx. specialize (h _ _ hx).
  cbn in *. destruct h as (e & ? & ? & h).
  split.
  - eapply Forall2_nth_error_l in he. 2: eassumption.
    destruct he as (o & eo & ho). inversion ho.
    subst. assumption.
  - intuition eauto.
    assert (hc :
      Forall2 (option_rel (conversion Σ Ξ))
        (liftn (length (cr_env rl)) ξ)
        (liftn (length (cr_env rl)) ξ')
    ).
    { apply Forall2_map_l, Forall2_map_r.
      eapply Forall2_impl. 2: eassumption.
      intros ?? ho. apply option_rel_map_l, option_rel_map_r.
      eapply option_rel_impl. 2: eassumption.
      eauto using conv_ren.
    }
    eapply conv_trans. 2: eapply conv_trans. 2: eassumption.
    + apply conv_sym. eapply conv_insts. assumption.
    + eapply conv_insts. assumption.
Qed.

Lemma inst_equations_red1 Σ Ξ Ξ' ξ ξ' :
  inst_equations Σ Ξ ξ Ξ' →
  Forall (onSome (const_eqs Σ Ξ)) ξ →
  OnOne2 (some_rel (red1 Σ Ξ)) ξ ξ' →
  inst_equations Σ Ξ ξ' Ξ'.
Proof.
  intros hi hξ h.
  eapply inst_equations_conv. 1: eassumption.
  eapply OnOne2_and_Forall_l in hξ. 2: exact h.
  apply OnOne2_refl_Forall2. 1: exact _.
  eapply OnOne2_impl. 2: eassumption.
  intros o o' [h1 h2]. destruct h2 as [? ? h2].
  cbn in h1. constructor.
  eauto using red1_conv.
Qed.

Lemma red1_const_eqs Σ Ξ u v :
  preserves_const_eqs Σ Ξ →
  const_const_eqs Σ →
  const_eqs Σ Ξ u →
  Σ ;; Ξ ⊢ u ↦ v →
  const_eqs Σ Ξ v.
Proof.
  intros hΣ hk hu h.
  induction h using red1_ind_alt.
  all: try solve [ cbn in * ; intuition eauto ].
  - cbn in hu. apply const_eqs_subst. 2: intuition eauto.
    intros []. all: cbn. all: intuition eauto.
  - cbn in hu. destruct hu as (hξ & ? & ? & ? & e & hξ').
    rewrite rForall_Forall in hξ.
    eqtwice. subst.
    eapply const_eqs_inst_closed. all: intuition eauto.
  - cbn in *. destruct hu as (hξ & Ξ' & A & t & e & hi).
    rewrite rForall_Forall in hξ |- *.
    split.
    + eapply OnOne2_and_Forall_l in hξ as h. 2: eassumption.
      eapply OnOne2_impl with (R' := λ x y, onSome (const_eqs Σ Ξ) y) in h.
      2:{
        intros ?? [h1 h2]. destruct h2 as [? ? h2]. cbn in h1.
        specialize (h2 h1). cbn. assumption.
      }
      eapply Forall_OnOne2_r. all: eauto.
    + eexists _,_,_. split. 1: eassumption.
      eauto using inst_equations_red1.
Qed.

Lemma red_const_eqs Σ Ξ u v :
  preserves_const_eqs Σ Ξ →
  const_const_eqs Σ →
  const_eqs Σ Ξ u →
  Σ ;; Ξ ⊢ u ↦* v →
  const_eqs Σ Ξ v.
Proof.
  intros hΣ hk hu h.
  induction h.
  - eapply red1_const_eqs. all: eassumption.
  - assumption.
  - eauto.
Qed.

Lemma red_conv Σ Ξ u v :
  preserves_const_eqs Σ Ξ →
  const_const_eqs Σ →
  const_eqs Σ Ξ u →
  Σ ;; Ξ ⊢ u ↦* v →
  Σ ;; Ξ ⊢ u ≡ v.
Proof.
  intros hΣ hk hu h.
  induction h.
  - apply red1_conv. all: assumption.
  - reflexivity.
  - eapply conv_trans. all: eauto using red_const_eqs.
Qed.

Lemma join_conv Σ Ξ u v :
  preserves_const_eqs Σ Ξ →
  const_const_eqs Σ →
  const_eqs Σ Ξ u →
  const_eqs Σ Ξ v →
  Σ ;; Ξ ⊢ u ⋈ v →
  Σ ;; Ξ ⊢ u ≡ v.
Proof.
  intros hΣ hk hcu hcv (w & hu & hv).
  eapply conv_trans.
  - eapply red_conv. all: eassumption.
  - apply conv_sym. eapply red_conv. all: eassumption.
Qed.

Definition type_preserving Σ Ξ :=
  ∀ n rl σ Γ A,
    ictx_get Ξ n = Some (Comp rl) →
    let lhs := rl.(cr_pat) in
    let rhs := rl.(cr_rep) in
    Σ ;; Ξ | Γ ⊢ lhs <[ σ ] : A →
    Σ ;; Ξ | Γ ⊢ rhs <[ σ ] : A.

Lemma gwf_const_const_eqs Σ :
  gwf Σ →
  const_const_eqs Σ.
Proof.
  intros h. intros c Ξ A t e.
  eapply valid_def in e. 2: eassumption.
  intuition eauto using typing_const_eqs.
Qed.

Lemma typed_join_conv Σ Ξ Γ Δ u v A B :
  gwf Σ →
  preserves_const_eqs Σ Ξ →
  Σ ;; Ξ | Γ ⊢ u : A →
  Σ ;; Ξ | Δ ⊢ v : B →
  Σ ;; Ξ ⊢ u ⋈ v →
  Σ ;; Ξ ⊢ u ≡ v.
Proof.
  intros hΣ hΞ hu hv h.
  eapply join_conv.
  all: eauto using typing_const_eqs, gwf_const_const_eqs.
Qed.

(** * Injectivity of Π

  The key component to subject reduction.
  To prove it, we need more constraints about computation rules.
  If they can have a Π on the left-hand side we lose.

*)

Definition no_pi_lhs (Σ : gctx) Ξ :=
  ∀ x rl A B σ,
    ictx_get Ξ x = Some (Comp rl) →
    let lhs := rl.(cr_pat) in
    Pi A B ≠ lhs <[ σ ].

#[export] Instance Reflexive_red Σ Ξ :
  Reflexive (red Σ Ξ).
Proof.
  intros u. apply rt_refl.
Qed.

Derive Signature for red1.
Derive Signature for clos_refl_trans.

#[export] Instance Transitive_red Σ Ξ :
  Transitive (red Σ Ξ).
Proof.
  intros u v w. eapply rt_trans.
Qed.

Section Injectivity.

  Context Σ Ξ (hnopi : no_pi_lhs Σ Ξ).

  Lemma red1_pi_inv A B T :
    Σ ;; Ξ ⊢ Pi A B ↦ T →
    ∃ A' B',
      T = Pi A' B' ∧
      Σ ;; Ξ ⊢ A ↦* A' ∧
      Σ ;; Ξ ⊢ B ↦* B'.
  Proof.
    intros h.
    depelim h.
    - exfalso. eapply hnopi. all: eassumption.
    - eexists _, _. intuition eauto.
      + apply rt_step. assumption.
      + reflexivity.
    - eexists _, _. intuition eauto.
      + reflexivity.
      + apply rt_step. assumption.
  Qed.

  Lemma red_pi_inv A B T :
    Σ ;; Ξ ⊢ Pi A B ↦* T →
    ∃ A' B',
      T = Pi A' B' ∧
      Σ ;; Ξ ⊢ A ↦* A' ∧
      Σ ;; Ξ ⊢ B ↦* B'.
  Proof.
    intros h.
    dependent induction h.
    - cbn in *. eapply red1_pi_inv. all: assumption.
    - eexists _,_. intuition eauto. all: reflexivity.
    - destruct IHh1 as (A' & B' & -> & hA & hB).
      specialize IHh2 with (1 := eq_refl).
      destruct IHh2 as (A'' & B'' & -> & hA' & hB').
      eexists _,_. intuition eauto.
      + etransitivity. all: eassumption.
      + etransitivity. all: eassumption.
  Qed.

  Lemma join_pi_inv A B A' B' :
    Σ ;; Ξ ⊢ Pi A B ⋈ Pi A' B' →
    Σ ;; Ξ ⊢ A ⋈ A' ∧
    Σ ;; Ξ ⊢ B ⋈ B'.
  Proof.
    intros (T & h & h').
    eapply red_pi_inv in h as (A1 & B1 & -> & hA1 & hB1), h' as (?&?&e&hA2&hB2).
    noconf e.
    split.
    - exists A1. intuition assumption.
    - exists B1. intuition auto.
  Qed.

  Lemma pi_inv Γ A B A' B' i j i' j' :
    gwf Σ →
    red_confluent Σ Ξ →
    preserves_const_eqs Σ Ξ →
    Σ ;; Ξ | Γ ⊢ A : Sort i →
    Σ ;; Ξ | Γ ⊢ A' : Sort i' →
    Σ ;; Ξ | Γ ,, A ⊢ B : Sort j →
    Σ ;; Ξ | Γ ,, A' ⊢ B' : Sort j' →
    Σ ;; Ξ ⊢ Pi A B ≡ Pi A' B' →
    Σ ;; Ξ ⊢ A ≡ A' ∧
    Σ ;; Ξ ⊢ B ≡ B'.
  Proof.
    intros hΣ hc hce hA hA' hB hB' h.
    eapply conv_equiv in h. eapply equiv_join in h. 2: assumption.
    eapply join_pi_inv in h.
    intuition eauto using typed_join_conv.
  Qed.

  Context (hΣ : gwf Σ).
  Context (hΞ : iwf Σ Ξ).
  Context (hc : red_confluent Σ Ξ).
  Context (hpc : preserves_const_eqs Σ Ξ).
  Context (hpt : type_preserving Σ Ξ).

  Lemma inst_typing_red_ih_gen Ξ' Γ ξ ξ' :
    wf Σ Ξ Γ →
    iwf Σ Ξ' ->
    inst_typing Σ Ξ Γ ξ Ξ' →
    Forall (onSome (const_eqs Σ Ξ)) ξ →
    Forall2 (option_rel (conversion Σ Ξ)) ξ ξ' →
    Forall2 (option_rel (λ u v, ∀ Γ A,
      wf Σ Ξ Γ →
      Σ ;; Ξ | Γ ⊢ u : A →
      Σ ;; Ξ | Γ ⊢ v : A
    )) ξ ξ' →
    inst_typing Σ Ξ Γ ξ' Ξ'.
  Proof.
    intros hΓ hΞ' h.
    induction h in ξ', hΞ' |- *; intros hξ hr hξ'.
    - depelim hξ'. constructor.
    - depelim hΞ'.
      apply Forall_app in hξ as [hξ _].
      apply Forall2_app_inv_l in hξ' as (ξ'1 & ξ'2 & hξ' & hξ'' & e). subst ξ'.
      depelim hξ''. depelim hξ''. depelim H7.
      apply Forall2_app_inv_l in hr as (ξ''1 & ξ''2 & hr & hξ'' & e).
      depelim hξ''. depelim hξ''. depelim H7.
      apply app_inj_tail in e as [e [= ]]. subst ξ''1.
      constructor; auto.

      rename ξ'1 into ξ'.
      assert (hc' :
        Forall2 (option_rel (conversion Σ Ξ))
          (liftn (length (cr_env rl)) ξ)
          (liftn (length (cr_env rl)) ξ')
      ).
      { apply Forall2_map_l, Forall2_map_r.
        eapply Forall2_impl. 2: apply hr.
        intros ?? ho. apply option_rel_map_l, option_rel_map_r.
        eapply option_rel_impl. 2: eassumption.
        eauto using conv_ren.
      }
      eapply conv_trans. 2: eapply conv_trans. 2: eassumption.
      + apply conv_sym. eapply conv_insts. assumption.
      + eapply conv_insts. assumption.


    - depelim hΞ'.
      apply Forall_app in hξ as [hξ _].
      apply Forall2_app_inv_l in hξ' as (ξ'1 & ξ'2 & hξ' & hξ'' & e). subst ξ'.
      depelim hξ''. depelim hξ''. depelim H3.
      apply Forall2_app_inv_l in hr as (ξ''1 & ξ''2 & hr & hξ'' & e).
      depelim hξ''. depelim hξ''. depelim H3.
      apply app_inj_tail in e as [e [= e']]. subst ξ''1 y1.
      constructor; auto.
      specialize (IHh _ hΞ' hξ hr hξ').

      apply H4; auto.
      eapply type_conv; eauto.
      1: now eapply conv_insts.
      eapply typing_inst_closed with (A := Sort _); eauto.
  Qed.


  Lemma inst_typing_red_ih Ξ' Γ ξ ξ' :
    wf Σ Ξ Γ →
    iwf Σ Ξ' ->
    inst_typing Σ Ξ Γ ξ Ξ' →
    Forall (onSome (const_eqs Σ Ξ)) ξ →
    OnOne2 (some_rel (red1 Σ Ξ)) ξ ξ' →
    OnOne2 (some_rel (λ u v, ∀ Γ A,
      wf Σ Ξ Γ →
      Σ ;; Ξ | Γ ⊢ u : A →
      Σ ;; Ξ | Γ ⊢ v : A
    )) ξ ξ' →
    inst_typing Σ Ξ Γ ξ' Ξ'.
  Proof.
    intros.
    eapply inst_typing_red_ih_gen; eauto.
    - eapply OnOne2_and_Forall_l in H3; eauto.
      eapply OnOne2_refl_Forall2, OnOne2_impl; eauto.
      { intros []; reflexivity. }
      intros to to' (h & h'). destruct h'. constructor.
      apply red1_conv; auto.
    - eapply OnOne2_refl_Forall2, OnOne2_impl; eauto.
      { intros []; constructor. auto. }
      intros to to' h. destruct h. constructor. auto.
  Qed.

  Lemma subject_reduction Γ u v A :
    wf Σ Ξ Γ →
    Σ ;; Ξ ⊢ u ↦ v →
    Σ ;; Ξ | Γ ⊢ u : A →
    Σ ;; Ξ | Γ ⊢ v : A.
  Proof.
    intros hΓ h hu.
    induction h in Γ, hΓ, A, hu |- * using red1_ind_alt.
    all: try solve [
      let h' := fresh in
      ttinv hu h' ; destruct_exists h' ;
      eapply validity in hu as hA ; try eassumption ;
      destruct hA ;
      econstructor ; [ econstructor | .. ] ;
      intuition eauto using typing_ctx_conv, wf_cons, ctx_conv_cons_same_ctx,
        ctx_conv_cons_same, red1_conv, typing_const_eqs
    ].
    - ttinv hu h. destruct h as (i & j & U & V & hlam & hu' & hU & hV & he).
      ttinv hlam h'. destruct h' as (? & ? & ? & ? & ? & ht & hepi).
      eapply pi_inv in hepi. 2-8: eassumption.
      destruct hepi as [h1 h2].
      eapply validity in hu as hA. 2-4: eauto.
      destruct hA.
      econstructor. 2,3: eassumption.
      eapply typing_subst.
      1:{ apply styping_one. eassumption. }
      econstructor. 2,3: eassumption.
      eauto using typing_ctx_conv, wf_cons, ctx_conv_cons_same_ctx.
    - ttinv hu h. destruct h as (? & ? & ? & e & hξ & hcA & he).
      eapply validity in hu as hA. 2-4: eassumption.
      destruct hA.
      econstructor. 2,3: eassumption.
      eapply typing_inst_closed. 1: eassumption.
      eapply valid_def in e as h'. 2: assumption.
      eqtwice. subst. intuition eauto.
    - eauto.
    - ttinv hu h'. destruct_exists h'.
      eapply validity in hu as hA. 2-4: eassumption.
      destruct hA.
      econstructor. 1: econstructor. all: intuition eauto.
      eapply typing_ctx_conv.
      all:
      intuition eauto using typing_ctx_conv, wf_cons, ctx_conv_cons_same_ctx,
        ctx_conv_cons_same, red1_conv, typing_const_eqs.
    - ttinv hu h'. destruct_exists h'.
      eapply validity in hu as hA. 2-4: eassumption.
      destruct hA.
      econstructor. 3: eassumption.
      2:{
        eapply conv_trans. 2: intuition eauto.
        apply cong_Pi. 2: apply conv_refl.
        apply conv_sym. intuition eauto using red1_conv, typing_const_eqs.
      }
      econstructor.
      + intuition eauto.
      + eapply typing_ctx_conv. 1,2: intuition eauto using wf_cons.
        apply ctx_conv_cons_same_ctx.
        intuition eauto using red1_conv, typing_const_eqs.
      + eapply typing_ctx_conv. 1,2: intuition eauto using wf_cons.
        apply ctx_conv_cons_same_ctx.
        intuition eauto using red1_conv, typing_const_eqs.
    - ttinv hu h'. destruct_exists h'.
      eapply validity in hu as hA. 2-4: eassumption.
      destruct hA.
      econstructor. 1: econstructor. all: intuition eauto.
      eapply conv_trans. 2: eassumption.
      eapply conv_substs. intros [].
      + cbn. apply conv_sym.
        intuition eauto using red1_conv, typing_const_eqs.
      + cbn. ttconv.
    - ttinv hu h'. destruct_exists h'.
      destruct h' as (hin & h').
      apply valid_def in hin as hΞ'; auto. destruct hΞ' as (hΞ' & _).
      eapply validity in hu as hA. 2-4: eassumption.
      destruct hA.
      econstructor. 1: econstructor. all: intuition eauto.
      + eapply typing_const_eqs in hu as hce.
        cbn in hce. destruct hce as (hξ & _).
        rewrite rForall_Forall in hξ.
        eauto using inst_typing_red_ih.
      + eapply conv_trans. 2: eassumption.
        apply conv_sym. apply conv_insts.
        eapply red1_conv_inst_ih.
        * eapply typing_const_eqs in hu. cbn in hu.
          rewrite rForall_Forall in hu. intuition auto.
        * assumption.
        * eapply OnOne2_impl. 2: exact H.
          intros ?? h. destruct h. constructor.
          eauto using red1_conv.
  Qed.

End Injectivity.
