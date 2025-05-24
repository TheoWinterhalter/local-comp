(** * Patterns

  We provide a notion of pattern as well as ways to verify the criteria
  imposed on reduction in the [Reduction] module.

  For now, we'll start with a very very weak version which only accepts one
  symbol as a left-hand side to a rule.
  TODO: Improve

*)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing BasicMetaTheory
  GScope Inversion Reduction Confluence.
From Stdlib Require Import Setoid Morphisms Relation_Definitions
  Relation_Operators.
From Equations Require Import Equations.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Require Import Equations.Prop.DepElim.

Inductive pat :=
| passm (x : aref).

Definition pat_to_term p :=
  match p with
  | passm x => assm x
  end.

Definition pattern_rules Ξ :=
  ∀ n rl,
    ictx_get Ξ n = Some (Comp rl) →
    ∃ p, rl.(cr_pat) = pat_to_term p.

(** ** Matching *)

Definition match_pat (p : pat) (t : term) : option (list term) :=
  match p, t with
  | passm x, assm y => if x =? y then Some [] else None
  | _, _ => None
  end.

Definition no_match Ξ t :=
  ∀ n rl p,
    ictx_get Ξ n = Some (Comp rl) →
    rl.(cr_pat) = pat_to_term p →
    match_pat p t = None.

(** Turn list into parallel substitution **)

Fixpoint slist (l : list term) :=
  match l with
  | [] => λ _, dummy
  | u :: l => u .: slist l
  end.

Lemma match_pat_sound p t σ :
  match_pat p t = Some σ →
  t = (pat_to_term p) <[ slist σ ].
Proof.
  intros h.
  induction p.
  destruct t. all: try discriminate.
  cbn in h. destruct (Nat.eqb_spec x a). 2: discriminate.
  subst.
  reflexivity.
Qed.

Definition triangle_citerion Ξ :=
  ∀ m n rl1 rl2,
    ictx_get Ξ m = Some (Comp rl1) →
    ictx_get Ξ n = Some (Comp rl2) →
    rl1.(cr_pat) = rl2.(cr_pat) →
    m = n.

(** ** Parallel reduction *)

Section Red.

  Reserved Notation "Γ ⊢ u ⇒ v"
    (at level 80, u, v at next level).

  Context (Σ : gctx) (Ξ : ictx).

  Inductive pred (Γ : ctx) : term → term → Prop :=

  (** Computation rules *)

  | pred_beta A t t' u u' :
      Γ ,, A ⊢ t ⇒ t' →
      Γ ⊢ u ⇒ u' →
      Γ ⊢ app (lam A t) u ⇒ t' <[ u' .. ]

  | pred_unfold c ξ Ξ' A t ξ' t' :
      Σ c = Some (Def Ξ' A t) →
      inst_equations Σ Ξ Γ ξ Ξ' →
      closed t = true →
      ∙ ⊢ t ⇒ t' →
      Forall2 (option_rel (pred Γ)) ξ ξ' →
      Γ ⊢ const c ξ ⇒ inst ξ' t'

  | pred_rule n rl p t σ σ' :
      ictx_get Ξ n = Some (Comp rl) →
      rl.(cr_pat) = pat_to_term p →
      match_pat p t = Some σ →
      Forall2 (pred Γ) σ σ' →
      let rhs := rl.(cr_rep) in
      (* let Θ := rl.(cr_env) in
      let k := length Θ in
      let lhs := rl.(cr_pat) in
      scoped k lhs = true →
      scoped k rhs = true → *)
      Γ ⊢ t ⇒ rhs <[ slist σ' ]

  (** Congruence rules *)

  | pred_Pi A B A' B' :
      Γ ⊢ A ⇒ A' →
      Γ ,, A ⊢ B ⇒ B' →
      Γ ⊢ Pi A B ⇒ Pi A' B'

  | pred_lam A t A' t' :
      Γ ⊢ A ⇒ A' →
      Γ ,, A ⊢ t ⇒ t' →
      Γ ⊢ lam A t ⇒ lam A' t'

  | pred_app u v u' v' :
      Γ ⊢ u ⇒ u' →
      Γ ⊢ v ⇒ v' →
      Γ ⊢ app u v ⇒ app u' v'

  | pred_const c ξ ξ' :
      Forall2 (option_rel (pred Γ)) ξ ξ' →
      Γ ⊢ const c ξ ⇒ const c ξ'

  | pred_var x :
      Γ ⊢ var x ⇒ var x

  where "Γ ⊢ u ⇒ v" := (pred Γ u v).

  Lemma pred_ind_alt :
    ∀ (P : ctx → term → term → Prop),
      (∀ Γ A t t' u u',
        Γ,, A ⊢ t ⇒ t' →
        P (Γ,, A) t t' →
        Γ ⊢ u ⇒ u' →
        P Γ u u' →
        P Γ (app (lam A t) u) (t' <[ u'..])
      ) →
      (∀ Γ c ξ Ξ' A t ξ' t',
        Σ c = Some (Def Ξ' A t) →
        inst_equations Σ Ξ Γ ξ Ξ' →
        closed t = true →
        ∙ ⊢ t ⇒ t' →
        P ∙ t t' →
        Forall2 (option_rel (pred Γ)) ξ ξ' →
        Forall2 (option_rel (P Γ)) ξ ξ' →
        P Γ (const c ξ) (inst ξ' t')
      ) →
      (∀ Γ n rl p t σ σ',
        ictx_get Ξ n = Some (Comp rl) →
        rl.(cr_pat) = pat_to_term p →
        match_pat p t = Some σ →
        Forall2 (pred Γ) σ σ' →
        Forall2 (P Γ) σ σ' →
        let rhs := rl.(cr_rep) in
        (* let Θ := rl.(cr_env) in
        let k := length Θ in
        let lhs := rl.(cr_pat) in
        scoped k lhs = true →
        scoped k rhs = true → *)
        P Γ t (rhs <[ slist σ' ])
      ) →
      (∀ Γ A B A' B',
        Γ ⊢ A ⇒ A' →
        P Γ A A' →
        Γ,, A ⊢ B ⇒ B' →
        P (Γ,, A) B B' →
        P Γ (Pi A B) (Pi A' B')
      ) →
      (∀ Γ A t A' t',
        Γ ⊢ A ⇒ A' →
        P Γ A A' →
        Γ,, A ⊢ t ⇒ t' →
        P (Γ,, A) t t' →
        P Γ (lam A t) (lam A' t')
      ) →
      (∀ Γ u v u' v',
        Γ ⊢ u ⇒ u' →
        P Γ u u' →
        Γ ⊢ v ⇒ v' →
        P Γ v v' →
        P Γ (app u v) (app u' v')
      ) →
      (∀ Γ c ξ ξ',
        Forall2 (option_rel (pred Γ)) ξ ξ' →
        Forall2 (option_rel (P Γ)) ξ ξ' →
        P Γ (const c ξ) (const c ξ')
      ) →
      (∀ Γ x, P Γ (var x) (var x)) →
      ∀ Γ u v, Γ ⊢ u ⇒ v → P Γ u v.
  Proof.
    intros P hbeta hunf hrl hpi hlam happ hconst hvar.
    fix aux 4. move aux at top.
    intros Γ u v h. destruct h.
    7:{
      eapply hconst. 1: assumption.
      revert ξ ξ' H. fix aux1 3.
      intros ξ ξ' h. destruct h as [ | o o' ξ ξ' h ].
      - constructor.
      - constructor. 2: eauto.
        destruct h. all: constructor ; auto.
    }
    3:{
      eapply hrl. 1-4: eauto.
      clear H1.
      revert σ σ' H2. fix aux1 3. 
      intros σ σ' hσ. destruct hσ.
      - constructor.
      - constructor. all: eauto.
    }
    2:{
      eapply hunf. 1-6: eauto.
      clear H0.
      revert ξ ξ' H2. fix aux1 3.
      intros ξ ξ' hh. destruct hh as [ | o o' ξ ξ' hh ].
      - constructor.
      - constructor. 2: eauto.
        destruct hh. all: constructor ; eauto.
    }
    all: match goal with h : _ |- _ => eapply h end.
    all: eauto.
  Qed.

  Lemma pred_meta_r Γ u v v' :
    Γ ⊢ u ⇒ v →
    v = v' →
    Γ ⊢ u ⇒ v'.
  Proof.
    intros ? ->. assumption.
  Qed.

  (** ** Parallel reduction is stable by substitution *)

  Lemma pred_subst_up Δ A σ σ' :
    (∀ x, Δ ⊢ σ x ⇒ σ' x) →
    (∀ x, Δ ,, A <[ σ ] ⊢ (var 0 .: σ >> ren_term S) x ⇒ (var 0 .: σ' >> ren_term S) x).
  Proof.
    intros h x.
    destruct x.
    - cbn. constructor.
    - cbn. unfold core.funcomp. (* Need renaming *) admit.
  Admitted.

  Lemma pred_subst Γ Δ σ σ' u v :
    (∀ x, Δ ⊢ σ x ⇒ σ' x) →
    Γ ⊢ u ⇒ v →
    Δ ⊢ u <[ σ ] ⇒ v <[ σ' ].
  Proof.
    intros hσ h. 
    induction h in Δ, σ, σ', hσ |- * using pred_ind_alt.
    all: try solve [ rasimpl ; econstructor ; eauto using pred_subst_up ].
    - rasimpl. eapply pred_meta_r.
      + econstructor. all: eauto using pred_subst_up.
      + rasimpl. reflexivity.
    - rasimpl. eapply pred_meta_r.
      + change @core.option_map with option_map.
        econstructor. all: eauto.
        * eapply inst_equations_subst_ih. 1: eassumption.
          admit. (* Should prove it once and for all *)
        * eapply Forall2_map_l, Forall2_map_r.
          eapply Forall2_impl. 2: eassumption.
          intros. eapply option_rel_map_l, option_rel_map_r. 
          eapply option_rel_impl. 2: eassumption.
          cbn. eauto using pred_subst_up.
      + rewrite subst_inst_closed. 2: admit.
        reflexivity.
    - admit. (* Stability of matching *)
    - cbn. change @core.option_map with option_map.
      econstructor. eapply Forall2_map_l, Forall2_map_r.
      eapply Forall2_impl. 2: eassumption.
      intros. eapply option_rel_map_l, option_rel_map_r. 
      eapply option_rel_impl. 2: eassumption.
      cbn. eauto using pred_subst_up.
  Admitted.

  (** ** Maximal reduct for parallel reduction *)

  Definition is_lam t :=
    match t with
    | lam A t => true
    | _ => false
    end.

  Lemma is_lam_inv t :
    is_lam t = true →
    ∃ A b, t = lam A b.
  Proof.
    destruct t. all: try discriminate.
    intros _. eexists _,_. reflexivity.
  Qed.

  Reserved Notation "Γ ⊢ u ⇒ᵨ v"
    (at level 80, u, v at next level).

  Inductive pred_max Γ : term → term → Prop :=
  | pred_max_beta A t t' u u' :
      Γ ,, A ⊢ t ⇒ᵨ t' →
      Γ ⊢ u ⇒ᵨ u' →
      Γ ⊢ app (lam A t) u ⇒ᵨ t' <[ u' .. ]

  | pred_max_unfold c ξ Ξ' A t ξ' t' :
      Σ c = Some (Def Ξ' A t) →
      ∙ ⊢ t ⇒ᵨ t' →
      Forall2 (option_rel (pred_max Γ)) ξ ξ' →
      Γ ⊢ const c ξ ⇒ᵨ inst ξ' t'

  | pred_max_Pi A B A' B' :
      Γ ⊢ A ⇒ᵨ A' →
      Γ ,, A ⊢ B ⇒ᵨ B' →
      Γ ⊢ Pi A B ⇒ᵨ Pi A' B'

  | pred_max_lam A t A' t' :
      Γ ⊢ A ⇒ᵨ A' →
      Γ ,, A ⊢ t ⇒ᵨ t' →
      Γ ⊢ lam A t ⇒ᵨ lam A' t'

  | pred_max_app u v u' v' :
      is_lam u = false →
      no_match Ξ (app u v) →
      Γ ⊢ u ⇒ᵨ u' →
      Γ ⊢ v ⇒ᵨ v' →
      Γ ⊢ app u v ⇒ᵨ app u' v'
    
  | pred_max_var x :
      Γ ⊢ var x ⇒ᵨ var x

  | pred_max_rule n rl p t σ σ' :
      ictx_get Ξ n = Some (Comp rl) →
      rl.(cr_pat) = pat_to_term p →
      match_pat p t = Some σ →
      Forall2 (pred Γ) σ σ' →
      let rhs := rl.(cr_rep) in
      (* let Θ := rl.(cr_env) in
      let k := length Θ in
      let lhs := rl.(cr_pat) in
      scoped k lhs = true →
      scoped k rhs = true → *)
      Γ ⊢ t ⇒ᵨ rhs <[ slist σ' ]

  where "Γ ⊢ u ⇒ᵨ v" := (pred_max Γ u v).

  Context (hpr : pattern_rules Ξ).

  Lemma pattern_rules_lhs_no_lam x rl σ A b :
    ictx_get Ξ x = Some (Comp rl) →
    let lhs := rl.(cr_pat) in
    lhs <[ σ ] ≠ lam A b.
  Proof.
    intros hx lhs.
    eapply hpr in hx as hn. fold lhs in hn. clearbody lhs. 
    destruct hn as [p ->].
    destruct p. cbn. discriminate.
  Qed.

  Lemma pattern_rules_lhs_no_const x rl σ c ξ :
    ictx_get Ξ x = Some (Comp rl) →
    let lhs := rl.(cr_pat) in
    lhs <[ σ ] ≠ const c ξ.
  Proof.
    intros hx lhs.
    eapply hpr in hx as hn. fold lhs in hn. clearbody lhs. 
    destruct hn as [p ->].
    destruct p. cbn. discriminate.
  Qed.

  Lemma triangle Γ t u :
    Γ ⊢ t ⇒ u →
    ∃ tᵨ, Γ ⊢ t ⇒ᵨ tᵨ ∧ Γ ⊢ u ⇒ tᵨ.
  Proof.
    induction 1 as [
      ?????? ht iht hu ihu
    | ???????????? iht ? ihξ
    | ???????????? ih
    | ?????? ihA ? ihB
    | ?????? ihA ? iht
    | ? u ??? hu ihu ? ihv
    | ???? ih
    | ?
    ] using pred_ind_alt.
    - destruct iht as [tr [ht1 ht2]], ihu as [ur [hu1 hu2]].
      eexists. split.
      + econstructor. all: eassumption.
      + eapply pred_subst. 2: eauto.
        intros []. all: cbn. 2: constructor.
        assumption.
    - destruct iht as [tr [ht1 ht2]].
      admit.
    - admit.
    - destruct ihA as [Ar [hA1 hA2]], ihB as [Br [hB1 hB2]].
      eexists. split.
      + econstructor. all: eassumption.
      + econstructor. all: eauto. admit.
    - destruct ihA as [Ar [hA1 hA2]], iht as [tr [ht1 ht2]].
      eexists. split.
      + econstructor. all: eassumption.
      + econstructor. all: eauto. admit.
    - destruct ihu as [ur [hu1 hu2]], ihv as [vr [hv1 hv2]].
      destruct (is_lam u) eqn: eu.
      + eapply is_lam_inv in eu as (A & b & ->).
        inversion hu1.
        2:{ exfalso. admit. }
        subst.
        eexists. split.
        * econstructor. all: eassumption.
        * inversion hu. 1: admit.
          subst. econstructor. 2: assumption.
          inversion hu2. 1: admit.
          subst. assumption.
      + (* Need to test whether something is a lhs of a rule 
          so I guess it needs to be a proper function after all.
        *)
        (* eexists. split.
        * econstructor. all: eassumption.
        * econstructor. all: assumption. *)
        admit.
    - admit.
    - eexists. split.
      + econstructor.
      + constructor.
  Admitted.

  Lemma pred_max_functional Γ t u v :
    Γ ⊢ t ⇒ᵨ u →
    Γ ⊢ t ⇒ᵨ v →
    u = v.
  Proof.
    intros hu hv.
    induction hu in v, hv |- *.
    - inversion hv.
      3:{ subst. admit. }
      2:{ discriminate. }
      subst. f_equal. 1: f_equal. all: eauto.
    - inversion hv.
      (* 2:{ exfalso. eapply pattern_rules_lhs_no_const. all: eassumption. } *)
      2: admit.
      subst. f_equal.
      + admit.
      + eqtwice. subst. eauto.
    - inversion hv. 2: admit.
      subst. f_equal. all: eauto.
    - inversion hv. 2: admit.
      subst. f_equal. all: eauto.
    - inversion hv.
      (* 3:{ exfalso. eapply pattern_rules_lhs_no_const. all: eassumption. } *)
      3: admit.
      1:{ subst. discriminate. }
      subst. f_equal. all: eauto.
    - inversion hv. 
      2:{ admit. }
      reflexivity.
    - (* inversion hv. 1-6: admit.
      subst. f_equal. all: eauto. *)
      admit.
  Admitted.

  Lemma pred_diamond Γ :
    diamond (pred Γ).
  Proof.
    intros t u v hu hv.
    eapply triangle in hu as [w [hw ?]], hv as [? []].
    eapply pred_max_functional in hw as e. 2: eassumption.
    subst. exists w. intuition eauto.
  Qed.

End Red.

Notation "Σ ;; Ξ | Γ ⊢ u ⇒ v" :=
  (pred Σ Ξ Γ u v)
  (at level 80, u, v at next level).

(* Not really needed *)
(* Notation "Σ ;; Ξ | Γ ⊢ u ⇒ᵨ v" :=
  (pred_max Σ Ξ Γ u v)
  (at level 80, u, v at next level). *)
