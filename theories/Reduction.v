(** Reduction

  We define reduction for the language as a way to study decidability of
  conversion and type checking.
  Those will be achieved with some assumptions on the reduction relation,
  namely confluence and type preservation.

**)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing BasicMetaTheory
  GScope Inversion.
From Stdlib Require Import Setoid Morphisms Relation_Definitions
  Relation_Operators.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Section Red.

  Reserved Notation "Γ ⊢ u ↦ v"
    (at level 80, u, v at next level).

  Context (Σ : gctx) (Ξ : ectx).

  Inductive red1 (Γ : ctx) : term → term → Prop :=

  (** Computation rules **)

  | red_beta A t u : Γ ⊢ app (lam A t) u ↦ t <[ u .. ]

  | red_unfold c ξ Ξ' A t :
      Σ c = Some (Def Ξ' A t) →
      Γ ⊢ const c ξ ↦ einst ξ t

  | red_rule E Ξ' Δ R M ξ' n rule σ :
      Σ E = Some (Ext Ξ' Δ R) →
      ectx_get Ξ M = Some (E, ξ') →
      nth_error R n = Some rule →
      let δ := length Δ in
      let lhs := rlhs M ξ' δ rule in
      let rhs := rrhs M ξ' δ rule in
      Γ ⊢ lhs <[ σ ] ↦ rhs <[ σ ]

  (** Congruence rules **)

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
      OnOne2 (OnOne2 (λ u v, Γ ⊢ u ↦ v)) ξ ξ' →
      Γ ⊢ const c ξ ↦ const c ξ'

  where "Γ ⊢ u ↦ v" := (red1 Γ u v).

  Lemma red1_ind_alt :
    ∀ (P : ctx → term → term → Prop),
      (∀ Γ A t u, P Γ (app (lam A t) u) (t <[ u..])) →
      (∀ Γ c ξ Ξ' A t, Σ c = Some (Def Ξ' A t) → P Γ (const c ξ) (einst ξ t)) →
      (∀ Γ E Ξ' Δ R M ξ' n rule σ,
        Σ E = Some (Ext Ξ' Δ R) →
        ectx_get Ξ M = Some (E, ξ') →
        nth_error R n = Some rule →
        let δ := Datatypes.length Δ in
        let lhs := rlhs M ξ' δ rule in
        let rhs := rrhs M ξ' δ rule in
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
        OnOne2 (OnOne2 (λ u v : term, Γ ⊢ u ↦ v)) ξ ξ' →
        OnOne2 (OnOne2 (P Γ)) ξ ξ' →
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
      intros ξ ξ' h. destruct h as [ σ σ' ξ h | σ ξ ξ' h ].
      - constructor. revert σ σ' h. fix aux2 3.
        intros σ σ' h. destruct h as [ u v σ h | u σ σ' h ].
        + constructor. auto.
        + constructor. auto.
      - constructor. auto.
    }
    all: match goal with h : _ |- _ => eapply h end.
    all: eauto.
  Qed.

End Red.

Notation "Σ ;; Ξ | Γ ⊢ u ↦ v" :=
  (red1 Σ Ξ Γ u v)
  (at level 80, u, v at next level).

(** Reflexive transitive closure **)

Definition red Σ Ξ Γ := clos_refl_trans _ (λ u v, Σ ;; Ξ | Γ ⊢ u ↦ v).

Notation "Σ ;; Ξ | Γ ⊢ u ↦* v" :=
  (red Σ Ξ Γ u v)
  (at level 80, u, v at next level).

(** Equivalence **)

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

Lemma equiv_red_ind Σ Ξ Γ Δ f x y :
  (∀ x y, Σ ;; Ξ | Δ ⊢ x ↦ y → Σ ;; Ξ | Γ ⊢ f x ↮ f y) →
  Σ ;; Ξ | Δ ⊢ x ↮ y →
  Σ ;; Ξ | Γ ⊢ f x ↮ f y.
Proof.
  intros hred h.
  eapply rst_step_ind. all: eauto.
Qed.

(** Notion of confluence **)

Definition red_confluent Σ Ξ :=
  ∀ Γ t u v,
    Σ ;; Ξ | Γ ⊢ t ↦* u →
    Σ ;; Ξ | Γ ⊢ t ↦* v →
    ∃ w,
      Σ ;; Ξ | Γ ⊢ u ↦* w ∧
      Σ ;; Ξ | Γ ⊢ v ↦* w.

(** Joinability **)

Definition joinable Σ Ξ Γ u v :=
  ∃ w,
    Σ ;; Ξ | Γ ⊢ u ↦* w ∧
    Σ ;; Ξ | Γ ⊢ v ↦* w.

Notation "Σ ;; Ξ | Γ ⊢ u ⋈ v" :=
  (joinable Σ Ξ Γ u v)
  (at level 80, u, v at next level).

(** Assuming confluence, equivalence is the same as joinability **)

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

(** Conversion is included in the congruence closure of reduction **)

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
  Forall2 (Forall2 (λ u v, Σ ;; Ξ | Γ ⊢ u ↮ v)) ξ ξ' →
  Σ ;; Ξ | Γ ⊢ const c ξ ↮ const c ξ'.
Proof.
  intros hξ.
  eapply Forall2_impl in hξ. 2: eapply Forall2_rst_OnOne2.
  eapply Forall2_impl in hξ.
  2:{ eapply clos_refl_sym_trans_incl. intros ??. eapply OnOne2_rst_comm. }
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

(** One-step reduction embeds in conversion, provided typing **)

#[export] Instance Reflexive_conversion Σ Ξ Γ :
  Reflexive (conversion Σ Ξ Γ).
Proof.
  intros u. ttconv.
Qed.

Lemma inst_typing_Forall_typed Σ Ξ Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  Forall (Forall (λ t, ∃ A, Σ ;; Ξ | Γ ⊢ t : A)) ξ.
Proof.
  intros (_ & h & e).
  rewrite Forall_forall. intros σ hσ.
  rewrite Forall_forall. intros t ht.
  apply In_nth_error in hσ as [n hn].
  apply In_nth_error in ht as [m hm].
  unfold inst_eget in h.
  specialize (h n).
  destruct ectx_get as [[E ξ']|] eqn: eg.
  2:{ unfold ectx_get in eg. destruct (_ <=? _) eqn: en.
    - rewrite Nat.leb_le in en.
      rewrite <- e in en.
      rewrite <- nth_error_None in en.
      congruence.
    - rewrite nth_error_None in eg.
      rewrite Nat.leb_gt in en.
      lia.
  }
  specialize h with (1 := eq_refl).
  destruct h as (? & ? & Δ & ? & ? & en & h).
  rewrite hn in en. cbn in en.
  destruct (nth_error Δ m) eqn: em.
  2:{ rewrite nth_error_None in em. apply nth_error_Some_alt in hm. lia. }
  specialize h with (1 := em).
  unfold eget in h. rewrite hn, hm in h.
  eexists. eassumption.
Qed.

Definition factor_rules (Σ : gctx) Ξ :=
  ∀ M E ξ' Ξ' Δ R n rule σ Γ A,
    ectx_get Ξ M = Some (E, ξ') →
    Σ E = Some (Ext Ξ' Δ R) →
    nth_error R n = Some rule →
    let δ := length Δ in
    let lhs := rlhs M ξ' δ rule in
    let lhs' := elhs M ξ' δ (crule_eq rule) in
    Σ ;; Ξ | Γ ⊢ lhs <[ σ ] : A →
    ∃ θ, lhs <[ σ ] = lhs' <[ θ ].

Lemma red1_conv Σ Ξ Γ u v A :
  gwf Σ →
  factor_rules Σ Ξ →
  Σ ;; Ξ | Γ ⊢ u : A →
  Σ ;; Ξ | Γ ⊢ u ↦ v →
  Σ ;; Ξ | Γ ⊢ u ≡ v.
Proof.
  intros hΣ hfac hu h.
  induction h in A, hu |- * using red1_ind_alt.
  all: try solve [
    let h' := fresh in
    ttinv hu h' ; destruct_exists h' ;
    intuition ttconv
  ].
  - ttinv hu h'. destruct h' as (? & ? & ? & e & hξ & ?).
    eqtwice. subst.
    econstructor.
    + eassumption.
    + apply hξ.
    + eapply valid_def in e as h. 2: assumption.
      eapply typing_closed. intuition eauto.
  - eapply hfac in hu as h. 2-4: eassumption.
    destruct h as [θ e].
    subst lhs δ. rewrite e.
    (* I suspect crule_eq might be wrong currently for the rhs *)
    (* In any case, factor_rules needs to be fixed as well *)
    admit.
  - constructor. apply OnOne2_refl_Forall2. 1: exact _.
    eapply OnOne2_impl.
    + apply OnOne2_refl_Forall2. exact _.
    + ttinv hu h'. destruct h' as (Ξ' & ? & ? & e & hξ & ?).
      eapply inst_typing_Forall_typed in hξ.
      eapply OnOne2_and_Forall_l in hξ. 2: eassumption.
      eapply OnOne2_impl. 2: eassumption.
      intros σ σ' [hf ho].
      eapply OnOne2_and_Forall_l in hf. 2: eassumption.
      eapply OnOne2_impl. 2: eassumption.
      intros a b [[? ha] h]. eauto.
Admitted.

(** Rest of the approach

  Things might not work as well as I had hoped.

  Assuming factorisation and confluence we get

  u ≡ v entails u ⋈ v
  but then to get that u ⋈ v (+ u and v well typed) entails u ≡ v we will
  also need subject reduction, which for β will require injectivity of Π
  the problem is that we need the entailment above to get it

  ! Potential solution

  Do the usual trick of requiring information you recover from typing in the
  reduction relation. This means the closed stuff, and something like
  lhs [σ] = lhs' [θ] and same for rhs.

  This uses equality so it's wrong. The challenge is going to be how to get
  confluence with this, so separation of concerns crumbles.

  Maybe there is another way by define some typing+ judgement that uses ⋈ for
  conversion (maybe as an extra, only at top-level, or as a replacement for ≡)
  to prove SR.

  Assuming (λ A t) u : T we have to show t[u] : T

  we get by inversion
  λ A t : Π A' B'
  u : A'
  B'[u] ≡ T

  then by inversion
  A ⊢ t : B
  Π A B ≡ Π A' B'

  thus
  Π A B ⋈ Π A' B'

  and thus
  A ⋈ A'
  B ⋈ B'

  we then have u :⁺ A where typing⁺ is defined by adding one layer of ⋈
  conversion on top of typing

  similarly, A ⊢ t :⁺ B'

  now, if we can prove a substitution lemma for typing⁺ (which would be able
  to reuse the substitution lemma for typing + the property that ⋈ is
  substitutive, ie ↦ is) then

  t[u] :⁺ B'[u]

  and then, since B'[u] ⋈ T, we get

  t[u] :⁺ T

  Now, we have to make sure we do have a substitution lemma for it,
  and that it still works for stuff like congruence rules because maybe
  the IH is going to be too weak.

  Take u ↦ u' | u v ↦ u' v

  If u v : T then u : Π A B and v : A and B[v] ≡ T
  by IH, we have u' :⁺ Π A B and we need to show u' v :⁺ B[v]
  why would that be true?

**)
