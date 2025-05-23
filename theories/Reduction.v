(** Reduction

  We define reduction for the language as a way to study decidability of
  conversion and type checking.
  Those will be achieved with some assumptions on the reduction relation,
  namely confluence and type preservation.

  TODO:
  - Check that reduction as defined below is suitable for the usual proofs of
    confluence.

*)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing BasicMetaTheory
  GScope Inversion Confluence.
From Stdlib Require Import Setoid Morphisms Relation_Definitions
  Relation_Operators.
From Equations Require Import Equations.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Require Import Equations.Prop.DepElim.

Section Red.

  Reserved Notation "Γ ⊢ u ↦ v"
    (at level 80, u, v at next level).

  Context (Σ : gctx) (Ξ : ictx).

  Inductive red1 (Γ : ctx) : term → term → Prop :=

  (** Computation rules *)

  | red_beta A t u : Γ ⊢ app (lam A t) u ↦ t <[ u .. ]

  | red_unfold c ξ Ξ' A t :
      Σ c = Some (Def Ξ' A t) →
      inst_equations Σ Ξ Γ ξ Ξ' →
      closed t = true →
      Γ ⊢ const c ξ ↦ inst ξ t

  | red_rule n rl σ :
      ictx_get Ξ n = Some (Comp rl) →
      let Θ := rl.(cr_env) in
      let k := length Θ in
      let lhs := rl.(cr_pat) in
      let rhs := rl.(cr_rep) in
      scoped k lhs = true →
      scoped k rhs = true →
      Γ ⊢ lhs <[ σ ] ↦ rhs <[ σ ]

  (** Congruence rules *)

  | red_Pi_dom A B A' :
      Γ ⊢ A ↦ A' →
      Γ ⊢ Pi A B ↦ Pi A' B

  | red_Pi_cod A B B' :
      Γ ,, A ⊢ B ↦ B' →
      Γ ⊢ Pi A B ↦ Pi A B'

  | red_lam_dom A t A' :
      Γ ⊢ A ↦ A' →
      Γ ⊢ lam A t ↦ lam A' t

  | red_lam_body A t t' :
      Γ ,, A ⊢ t ↦ t' →
      Γ ⊢ lam A t ↦ lam A t'

  | red_app_fun u v u' :
      Γ ⊢ u ↦ u' →
      Γ ⊢ app u v ↦ app u' v

  | red_app_arg u v v' :
      Γ ⊢ v ↦ v' →
      Γ ⊢ app u v ↦ app u v'

  | red_const c ξ ξ' :
      OnOne2 (some_rel (λ u v, Γ ⊢ u ↦ v)) ξ ξ' →
      Γ ⊢ const c ξ ↦ const c ξ'

  where "Γ ⊢ u ↦ v" := (red1 Γ u v).

  Lemma red1_ind_alt :
    ∀ (P : ctx → term → term → Prop),
      (∀ Γ A t u, P Γ (app (lam A t) u) (t <[ u..])) →
      (∀ Γ c ξ Ξ' A t,
        Σ c = Some (Def Ξ' A t) →
        inst_equations Σ Ξ Γ ξ Ξ' →
        closed t = true →
        P Γ (const c ξ) (inst ξ t)
      ) →
      (∀ Γ n rl σ,
        ictx_get Ξ n = Some (Comp rl) →
        let Θ := rl.(cr_env) in
        let k := length Θ in
        let lhs := rl.(cr_pat) in
        let rhs := rl.(cr_rep) in
        scoped k lhs = true →
        scoped k rhs = true →
        P Γ (lhs <[ σ]) (rhs <[ σ])
      ) →
      (∀ Γ A B A',
        Γ ⊢ A ↦ A' →
        P Γ A A' →
        P Γ (Pi A B) (Pi A' B)
      ) →
      (∀ Γ A B B', Γ,, A ⊢ B ↦ B' → P (Γ,, A) B B' → P Γ (Pi A B) (Pi A B')) →
      (∀ Γ A t A', Γ ⊢ A ↦ A' → P Γ A A' → P Γ (lam A t) (lam A' t)) →
      (∀ Γ A t t', Γ,, A ⊢ t ↦ t' → P (Γ,, A) t t' → P Γ (lam A t) (lam A t')) →
      (∀ Γ u v u', Γ ⊢ u ↦ u' → P Γ u u' → P Γ (app u v) (app u' v)) →
      (∀ Γ u v v', Γ ⊢ v ↦ v' → P Γ v v' → P Γ (app u v) (app u v')) →
      (∀ Γ c ξ ξ',
        OnOne2 (some_rel (λ u v : term, Γ ⊢ u ↦ v)) ξ ξ' →
        OnOne2 (some_rel (P Γ)) ξ ξ' →
        P Γ (const c ξ) (const c ξ')
      ) →
      ∀ Γ u v, Γ ⊢ u ↦ v → P Γ u v.
  Proof.
    intros P hbeta hunf hrl hpid hpic hlamd hlamb happf happa hconst.
    fix aux 4. move aux at top.
    intros Γ u v h. destruct h.
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

Notation "Σ ;; Ξ | Γ ⊢ u ↦ v" :=
  (red1 Σ Ξ Γ u v)
  (at level 80, u, v at next level).

(** Reflexive transitive closure *)

Definition red Σ Ξ Γ := clos_refl_trans (λ u v, Σ ;; Ξ | Γ ⊢ u ↦ v).

Notation "Σ ;; Ξ | Γ ⊢ u ↦* v" :=
  (red Σ Ξ Γ u v)
  (at level 80, u, v at next level).

(** Equivalence *)

Definition equiv Σ Ξ Γ := clos_refl_sym_trans _ (λ u v, Σ ;; Ξ | Γ ⊢ u ↦ v).

Notation "Σ ;; Ξ | Γ ⊢ u ↮ v" :=
  (equiv Σ Ξ Γ u v)
  (at level 80, u, v at next level).

#[export] Instance equiv_refl Σ Ξ Γ : Reflexive (equiv Σ Ξ Γ).
Proof.
  intros u.
  eapply rst_refl.
Qed.

#[export] Instance equiv_sym Σ Ξ Γ : Symmetric (equiv Σ Ξ Γ).
Proof.
  intros u v h.
  eapply rst_sym. eassumption.
Qed.

#[export] Instance equiv_trans Σ Ξ Γ : Transitive (equiv Σ Ξ Γ).
Proof.
  intros u v w h1 h2.
  eapply rst_trans. all: eassumption.
Qed.

Lemma red_ind Σ Ξ Γ Δ f x y :
  (∀ x y, Σ ;; Ξ | Δ ⊢ x ↦ y → Σ ;; Ξ | Γ ⊢ f x ↦* f y) →
  Σ ;; Ξ | Δ ⊢ x ↦* y →
  Σ ;; Ξ | Γ ⊢ f x ↦* f y.
Proof.
  intros hred h.
  eapply rt_step_ind. all: eauto.
Qed.

Lemma equiv_red_ind Σ Ξ Γ Δ f x y :
  (∀ x y, Σ ;; Ξ | Δ ⊢ x ↦ y → Σ ;; Ξ | Γ ⊢ f x ↮ f y) →
  Σ ;; Ξ | Δ ⊢ x ↮ y →
  Σ ;; Ξ | Γ ⊢ f x ↮ f y.
Proof.
  intros hred h.
  eapply rst_step_ind. all: eauto.
Qed.

(** Notion of confluence *)

Definition red_confluent Σ Ξ :=
  ∀ Γ, confluent (red1 Σ Ξ Γ).

(** Joinability *)

Definition red_joinable Σ Ξ Γ :=
  joinable (red Σ Ξ Γ).

Notation "Σ ;; Ξ | Γ ⊢ u ⋈ v" :=
  (red_joinable Σ Ξ Γ u v)
  (at level 80, u, v at next level).

(** Assuming confluence, equivalence is the same as joinability *)

Lemma equiv_join Σ Ξ Γ u v :
  red_confluent Σ Ξ →
  Σ ;; Ξ | Γ ⊢ u ↮ v →
  Σ ;; Ξ | Γ ⊢ u ⋈ v.
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

Lemma equiv_Pi Σ Ξ Γ A A' B B' :
  Σ ;; Ξ | Γ ⊢ A ↮ A' →
  Σ ;; Ξ | Γ ,, A ⊢ B ↮ B' →
  Σ ;; Ξ | Γ ⊢ Pi A B ↮ Pi A' B'.
Proof.
  intros hA hB.
  transitivity (Pi A B').
  - eapply equiv_red_ind. 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
  - eapply equiv_red_ind with (f := λ x, Pi x B'). 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
Qed.

Lemma equiv_lam Σ Ξ Γ A A' t t' :
  Σ ;; Ξ | Γ ⊢ A ↮ A' →
  Σ ;; Ξ | Γ ,, A ⊢ t ↮ t' →
  Σ ;; Ξ | Γ ⊢ lam A t ↮ lam A' t'.
Proof.
  intros hA ht.
  transitivity (lam A t').
  - eapply equiv_red_ind. 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
  - eapply equiv_red_ind with (f := λ x, lam x t'). 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
Qed.

Lemma equiv_app Σ Ξ Γ u u' v v' :
  Σ ;; Ξ | Γ ⊢ u ↮ u' →
  Σ ;; Ξ | Γ ⊢ v ↮ v' →
  Σ ;; Ξ | Γ ⊢ app u v ↮ app u' v'.
Proof.
  intros hu hv.
  transitivity (app u v').
  - eapply equiv_red_ind. 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
  - eapply equiv_red_ind with (f := λ x, app x v'). 2: eassumption.
    intros. apply rst_step. econstructor. assumption.
Qed.

Lemma equiv_const Σ Ξ Γ c ξ ξ' :
  Forall2 (option_rel (λ u v, Σ ;; Ξ | Γ ⊢ u ↮ v)) ξ ξ' →
  Σ ;; Ξ | Γ ⊢ const c ξ ↮ const c ξ'.
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

Lemma conv_equiv Σ Ξ Γ u v :
  Σ ;; Ξ | Γ ⊢ u ≡ v →
  Σ ;; Ξ | Γ ⊢ u ↮ v.
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

#[export] Instance Reflexive_conversion Σ Ξ Γ :
  Reflexive (conversion Σ Ξ Γ).
Proof.
  intros u. ttconv.
Qed.

Lemma inst_typing_Forall_typed Σ Ξ Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  Forall (onSome (λ t, ∃ A, Σ ;; Ξ | Γ ⊢ t : A)) ξ.
Proof.
  intros (heq & h & e).
  rewrite Forall_forall. intros o ho.
  apply In_nth_error in ho as [x hx].
  destruct o as [t |]. 2: constructor.
  cbn.
  unfold inst_iget in h.
  specialize (h x).
  destruct ictx_get as [[]|] eqn: eg.
  3:{
    unfold ictx_get in eg. destruct (_ <=? _) eqn: e1.
    - rewrite Nat.leb_le in e1. rewrite <- e in e1.
      rewrite <- nth_error_None in e1. congruence.
    - rewrite nth_error_None in eg.
      rewrite Nat.leb_gt in e1. lia.
  }
  2:{
    specialize (heq _ _ eg). cbn in heq. intuition congruence.
  }
  specialize h with (1 := eq_refl).
  unfold iget in h. rewrite hx in h. 
  eexists. intuition eauto.
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

Lemma red1_conv Σ Ξ Γ u v :
  Σ ;; Ξ | Γ ⊢ u ↦ v →
  Σ ;; Ξ | Γ ⊢ u ≡ v.
Proof.
  intros h.
  induction h using red1_ind_alt.
  all: try solve [ ttconv ].
  - econstructor. all: eassumption.
  - constructor. apply OnOne2_refl_Forall2. 1: exact _.
    eapply OnOne2_impl.
    + intros ??. apply some_rel_option_rel.
    + assumption.
Qed.

Lemma red_conv Σ Ξ Γ u v :
  Σ ;; Ξ | Γ ⊢ u ↦* v →
  Σ ;; Ξ | Γ ⊢ u ≡ v.
Proof.
  intros h.
  induction h.
  - apply red1_conv. assumption.
  - reflexivity.
  - eapply conv_trans. all: eassumption.
Qed.

Lemma join_conv Σ Ξ Γ u v :
  Σ ;; Ξ | Γ ⊢ u ⋈ v →
  Σ ;; Ξ | Γ ⊢ u ≡ v.
Proof.
  intros (w & hu & hv).
  eapply conv_trans.
  - eapply red_conv. eassumption.
  - apply conv_sym. eapply red_conv. eassumption.
Qed.

(** * Context reduction *)

Reserved Notation "Σ ;; Ξ | Γ ↦* Δ" (at level 80).

Inductive red_ctx (Σ : gctx) (Ξ : ictx) : ctx → ctx → Prop :=
| red_nil : Σ ;; Ξ | ∙ ↦* ∙
| red_cons Γ Δ A B :
    Σ ;; Ξ | Γ ↦* Δ →
    Σ ;; Ξ | Γ ⊢ A ↦* B →
    Σ ;; Ξ | Γ ,, A ↦* Δ ,, B

where "Σ ;; Ξ | Γ ↦* Δ" := (red_ctx Σ Ξ Γ Δ).

Lemma red_ctx_red1 Σ Ξ Γ Δ u v :
  Σ ;; Ξ | Δ ↦* Γ →
  Σ ;; Ξ | Γ ⊢ u ↦ v →
  Σ ;; Ξ | Δ ⊢ u ↦* v.
Proof.
  intros hctx h.
  induction h in Δ, hctx using red1_ind_alt.
  all: try solve [ apply rt_step ; econstructor ; eauto ].
  - apply rt_step. econstructor. all: eauto.
    intros ?.
    (* This would require context conversion for conversion *)
    (* So it might be all worthless in the end *)
    admit.
  - eapply red_ind with (f := λ x, Pi x _). 2: eauto.
    intros. apply rt_step. econstructor. assumption.
  - eapply red_ind.
    2:{ eapply IHh. econstructor. 1: eassumption. apply rt_refl. }
    intros. apply rt_step. econstructor. assumption.
  - eapply red_ind with (f := λ x, lam x _). 2: eauto.
    intros. apply rt_step. econstructor. assumption.
  - eapply red_ind.
    2:{ eapply IHh. econstructor. 1: eassumption. apply rt_refl. }
    intros. apply rt_step. econstructor. assumption.
  - eapply red_ind with (f := λ x, app x _). 2: eauto.
    intros. apply rt_step. econstructor. assumption.
  - eapply red_ind. 2: eauto.
    intros. apply rt_step. econstructor. assumption.
  - admit.
Abort.

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

#[export] Instance Reflexive_red Σ Ξ Γ :
  Reflexive (red Σ Ξ Γ).
Proof.
  intros u. apply rt_refl.
Qed.

Derive Signature for red1.
Derive Signature for clos_refl_trans.

#[export] Instance Transitive_red Σ Ξ Γ :
  Transitive (red Σ Ξ Γ).
Proof.
  intros u v w. eapply rt_trans.
Qed.

Section Injectivity.

  Context Σ Ξ (hnopi : no_pi_lhs Σ Ξ).

  Lemma red1_pi_inv Γ A B T :
    Σ ;; Ξ | Γ ⊢ Pi A B ↦ T →
    ∃ A' B',
      T = Pi A' B' ∧
      Σ ;; Ξ | Γ ⊢ A ↦* A' ∧
      Σ ;; Ξ | Γ ,, A ⊢ B ↦* B'.
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

  Lemma red_pi_inv Γ A B T :
    Σ ;; Ξ | Γ ⊢ Pi A B ↦* T →
    ∃ A' B',
      T = Pi A' B' ∧
      Σ ;; Ξ | Γ ⊢ A ↦* A' ∧
      Σ ;; Ξ | Γ ,, A ⊢ B ↦* B'.
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
      + etransitivity. 1: eassumption.
        (* Would need context conversion *)
  Admitted.

  Lemma join_pi_inv Γ A B A' B' :
    Σ ;; Ξ | Γ ⊢ Pi A B ⋈ Pi A' B' →
    Σ ;; Ξ | Γ ⊢ A ⋈ A' ∧
    Σ ;; Ξ | Γ ,, A ⊢ B ⋈ B'.
  Proof.
    intros (T & h & h').
    eapply red_pi_inv in h as (A1 & B1 & -> & hA1 & hB1), h' as (?&?&e&hA2&hB2).
    noconf e.
    split.
    - exists A1. intuition assumption.
    - exists B1. intuition auto.
      (* Context conversion too *)
      admit.
  Admitted.

End Injectivity.
