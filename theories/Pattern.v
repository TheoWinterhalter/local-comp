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
  GScope Inversion Confluence Reduction.
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

Record prule := {
  pr_env : ctx ;
  pr_pat : pat ;
  pr_sub : nat → term ;
  pr_rep : term ;
  pr_typ : term
}.

Definition prule_crule (rl : prule) : crule := {|
  cr_env := rl.(pr_env) ;
  cr_pat := pat_to_term rl.(pr_pat) ;
  cr_sub := rl.(pr_sub) ;
  cr_rep := rl.(pr_rep) ;
  cr_typ := rl.(pr_typ)
|}.

Inductive pdecl :=
| pAssm (A : term)
| pComp (rl : prule).

Definition pctx := list pdecl.

Notation pctx_get Ξ x := (lvl_get (A := pdecl) Ξ x).

Lemma lvl_get_map [A B] (f : A → B) l x :
  lvl_get (map f l) x = option_map f (lvl_get l x).
Proof.
  unfold lvl_get. rewrite !length_map.
  destruct (_ <=? _) eqn: e.
  - reflexivity.
  - apply nth_error_map.
Qed.

Definition pdecl_idecl (d : pdecl) : idecl :=
  match d with
  | pAssm A => Assm A
  | pComp rl => Comp (prule_crule rl)
  end.

Definition pctx_ictx (Ξ : pctx) : ictx :=
  map pdecl_idecl Ξ.

(** ** Matching *)

Definition match_pat (p : pat) (t : term) : option (list term) :=
  match p, t with
  | passm x, assm y => if x =? y then Some [] else None
  | _, _ => None
  end.

Fixpoint find_match Ξ t :=
  match Ξ with
  | pComp rl :: Ξ =>
    match match_pat rl.(pr_pat) t with
    | Some σ => Some (length Ξ, rl, σ)
    | None => find_match Ξ t
    end
  | _ :: Ξ => find_match Ξ t
  | [] => None
  end.

Definition no_match Ξ t :=
  find_match Ξ t = None.

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

Lemma find_match_sound Ξ t n rl σ :
  find_match Ξ t = Some (n, rl, σ) →
  pctx_get Ξ n = Some (pComp rl) ∧
  match_pat rl.(pr_pat) t = Some σ.
Proof.
  intros h.
  induction Ξ as [| [A|rl'] Ξ ih].
  - discriminate.
  - cbn in h. erewrite lvl_get_weak. all: intuition eauto.
  - cbn in h. destruct match_pat eqn: e.
    + inversion h. subst.
      rewrite lvl_get_last. intuition eauto.
    + erewrite lvl_get_weak. all: intuition eauto.
Qed.

Definition triangle_citerion Ξ :=
  ∀ m n rl1 rl2,
    pctx_get Ξ m = Some (pComp rl1) →
    pctx_get Ξ n = Some (pComp rl2) →
    rl1.(pr_pat) = rl2.(pr_pat) →
    m = n.

(** ** Parallel reduction *)

Section Red.

  Reserved Notation "Γ ⊢ u ⇒ v"
    (at level 80, u, v at next level).

  Context (Σ : gctx) (Ξ : pctx).

  Inductive pred (Γ : ctx) : term → term → Prop :=

  (** Computation rules *)

  | pred_beta A t t' u u' :
      Γ ,, A ⊢ t ⇒ t' →
      Γ ⊢ u ⇒ u' →
      Γ ⊢ app (lam A t) u ⇒ t' <[ u' .. ]

  | pred_unfold c ξ Ξ' A t ξ' :
      Σ c = Some (Def Ξ' A t) →
      closed t = true →
      Forall2 (option_rel (pred Γ)) ξ ξ' →
      Γ ⊢ const c ξ ⇒ inst ξ' t

  | pred_rule n rl t σ σ' :
      pctx_get Ξ n = Some (pComp rl) →
      match_pat rl.(pr_pat) t = Some σ →
      Forall2 (pred Γ) σ σ' →
      let rhs := rl.(pr_rep) in
      (* let Θ := rl.(pr_env) in *)
      (* let k := length Θ in
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

  | pred_sort s :
      Γ ⊢ Sort s ⇒ Sort s

  | pred_assm x :
      Γ ⊢ assm x ⇒ assm x

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
      (∀ Γ c ξ Ξ' A t ξ',
        Σ c = Some (Def Ξ' A t) →
        closed t = true →
        Forall2 (option_rel (pred Γ)) ξ ξ' →
        Forall2 (option_rel (P Γ)) ξ ξ' →
        P Γ (const c ξ) (inst ξ' t)
      ) →
      (∀ Γ n rl t σ σ',
        pctx_get Ξ n = Some (pComp rl) →
        match_pat rl.(pr_pat) t = Some σ →
        Forall2 (pred Γ) σ σ' →
        Forall2 (P Γ) σ σ' →
        let rhs := rl.(pr_rep) in
        (* let Θ := rl.(pr_env) in *)
        (* let k := length Θ in
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
      (∀ Γ s, P Γ (Sort s) (Sort s)) →
      (∀ Γ x, P Γ (assm x) (assm x)) →
      ∀ Γ u v, Γ ⊢ u ⇒ v → P Γ u v.
  Proof.
    intros P hbeta hunf hrl hpi hlam happ hconst hvar hsort hassm.
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
      eapply hrl. 1-3: eauto.
      clear H0.
      revert σ σ' H1. fix aux1 3.
      intros σ σ' hσ. destruct hσ.
      - constructor.
      - constructor. all: eauto.
    }
    2:{
      eapply hunf. 1-3: eauto.
      revert ξ ξ' H1. fix aux1 3.
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

  (** ** Parallel reduction is reflexive *)

  Lemma pred_refl Γ t :
    Γ ⊢ t ⇒ t.
  Proof.
    induction t using term_rect in Γ |- *.
    all: try solve [ econstructor ; eauto ].
    econstructor. apply Forall2_diag. apply All_Forall.
    eapply All_impl. 2: eassumption.
    intros o ho. apply option_rel_diag. rewrite OnSome_onSome.
    apply onSomeT_onSome. eapply onSomeT_impl. 2: eassumption.
    auto.
  Qed.

  (** ** Parallel reduction doesn't care about contexts

    This can feel a bit silly, but we would need to care about contexts if we
    were to extend the theory with let bindings.
    In the meantime, we allow ourselves to forget about the context from time to
    time.

  *)

  Lemma pred_ctx_irr Γ Δ u v :
    Γ ⊢ u ⇒ v →
    Δ ⊢ u ⇒ v.
  Proof.
    intros h.
    induction h in Δ |- * using pred_ind_alt.
    all: try solve [ econstructor ; eauto ].
    - econstructor. 1,2: eassumption.
      eapply Forall2_impl. 2: eassumption.
      intros. eapply option_rel_impl. 2: eassumption.
      auto.
    - econstructor. 1,2: eassumption.
      eapply Forall2_impl. 2: eassumption.
      auto.
    - econstructor.
      eapply Forall2_impl. 2: eassumption.
      intros. eapply option_rel_impl. 2: eassumption.
      auto.
  Qed.

  (** ** Parallel reduction is stable by substitution *)

  Lemma match_pat_ren p t l ρ :
    match_pat p t = Some l →
    match_pat p (ρ ⋅ t) = Some (map (ren_term ρ) l).
  Proof.
    intro h.
    destruct p, t. all: try discriminate.
    cbn in *. destruct (_ =? _). 2: discriminate.
    inversion h.
    reflexivity.
  Qed.

  Lemma slist_ren l ρ :
    pointwise_relation _ eq
      (slist l >> ren_term ρ) (slist (map (ren_term ρ) l)).
  Proof.
    intros x. unfold core.funcomp.
    induction l as [| u l ih] in x |- *.
    - cbn. reflexivity.
    - cbn. destruct x.
      + cbn. reflexivity.
      + cbn. eauto.
  Qed.

  Lemma pred_ren Γ Δ ρ u v :
    Γ ⊢ u ⇒ v →
    Δ ⊢ ρ ⋅ u ⇒ ρ ⋅ v.
  Proof.
    intros h.
    induction h in Δ, ρ |- * using pred_ind_alt.
    all: try solve [ rasimpl ; econstructor ; eauto ].
    - rasimpl. eapply pred_meta_r.
      + econstructor. all: eauto.
      + rasimpl. reflexivity.
    - rasimpl. change @core.option_map with option_map.
      eapply pred_meta_r.
      + econstructor. 1,2: eauto.
        eapply Forall2_map_l, Forall2_map_r.
        eapply Forall2_impl. 2: eassumption.
        intros. eapply option_rel_map_l, option_rel_map_r.
        eapply option_rel_impl. 2: eassumption.
        cbn. auto.
      + rewrite ren_inst. f_equal.
        rewrite closed_ren. 2: assumption.
        reflexivity.
    - rasimpl. setoid_rewrite slist_ren.
      econstructor.
      + eassumption.
      + eapply match_pat_ren. eassumption.
      + apply Forall2_map_l, Forall2_map_r. eapply Forall2_impl. 2: eassumption.
        cbn. eauto.
    - cbn. change @core.option_map with option_map.
      econstructor.
      eapply Forall2_map_l, Forall2_map_r.
      eapply Forall2_impl. 2: eassumption.
      intros. eapply option_rel_map_l, option_rel_map_r.
      eapply option_rel_impl. 2: eassumption.
      cbn. auto.
  Qed.

  Lemma pred_subst_up Δ A σ σ' :
    (∀ x, Δ ⊢ σ x ⇒ σ' x) →
    (∀ x, Δ ,, A <[ σ ] ⊢ (var 0 .: σ >> ren_term S) x ⇒ (var 0 .: σ' >> ren_term S) x).
  Proof.
    intros h x.
    destruct x.
    - cbn. constructor.
    - cbn. unfold core.funcomp. eapply pred_ren. eauto.
  Qed.

  Lemma match_pat_subst p t l σ :
    match_pat p t = Some l →
    match_pat p (t <[ σ ]) = Some (map (subst_term σ) l).
  Proof.
    intro h.
    destruct p, t. all: try discriminate.
    cbn in *. destruct (_ =? _). 2: discriminate.
    inversion h.
    reflexivity.
  Qed.

  Lemma slist_subst l σ :
    pointwise_relation _ eq
      (slist l >> subst_term σ) (slist (map (subst_term σ) l)).
  Proof.
    intros x. unfold core.funcomp.
    induction l as [| u l ih] in x |- *.
    - cbn. reflexivity.
    - cbn. destruct x.
      + cbn. reflexivity.
      + cbn. eauto.
  Qed.

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
        econstructor. 1,2: eauto.
        eapply Forall2_map_l, Forall2_map_r.
        eapply Forall2_impl. 2: eassumption.
        intros. eapply option_rel_map_l, option_rel_map_r.
        eapply option_rel_impl. 2: eassumption.
        cbn. eauto using pred_subst_up.
      + rewrite subst_inst_closed. 2: assumption.
        reflexivity.
    - rasimpl. setoid_rewrite slist_subst.
      econstructor.
      + eassumption.
      + eapply match_pat_subst. eassumption.
      + apply Forall2_map_l, Forall2_map_r. eapply Forall2_impl. 2: eassumption.
        cbn. eauto.
    - cbn. change @core.option_map with option_map.
      econstructor.
      eapply Forall2_map_l, Forall2_map_r.
      eapply Forall2_impl. 2: eassumption.
      intros. eapply option_rel_map_l, option_rel_map_r.
      eapply option_rel_impl. 2: eassumption.
      cbn. eauto using pred_subst_up.
    - cbn. eauto.
  Qed.

  Lemma lift_instance_pred Γ A ξ ξ' :
    Forall2 (option_rel (pred Γ)) ξ ξ' →
    Forall2 (option_rel (pred (Γ ,, inst ξ A))) (lift_instance ξ) (lift_instance ξ').
  Proof.
    intros h.
    apply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros o o' ho.
    apply option_rel_map_l, option_rel_map_r.
    eapply option_rel_impl. 2: eassumption.
    intros. eauto using pred_ren.
  Qed.

  Lemma pred_inst Γ ξ ξ' t :
    Forall2 (option_rel (pred Γ)) ξ ξ' →
    Γ ⊢ inst ξ t ⇒ inst ξ' t.
  Proof.
    intros h.
    induction t using term_rect in Γ, ξ, ξ', h |- *.
    all: try solve [ cbn ; constructor ; eauto using lift_instance_pred ].
    - cbn. econstructor.
      apply Forall2_map_l, Forall2_map_r.
      apply Forall2_diag. apply All_Forall.
      eapply All_impl. 2: eassumption.
      intros.
      apply option_rel_map_l, option_rel_map_r.
      apply option_rel_diag. rewrite OnSome_onSome. apply onSomeT_onSome.
      eapply onSomeT_impl. 2: eassumption.
      cbn. intros. eauto.
    - cbn. unfold iget. destruct (nth_error ξ _) as [o1 |] eqn:e1.
      2:{
        destruct (nth_error ξ' _) eqn:e2.
        1:{
          eapply nth_error_None in e1. eapply Forall2_length in h.
          rewrite h in e1. rewrite <- nth_error_None in e1. congruence.
        }
        constructor.
      }
      eapply Forall2_nth_error_l in e1 as e2. 2: eassumption.
      destruct e2 as (o2 & e2 & ho). rewrite e2.
      destruct ho. 1: constructor.
      assumption.
  Qed.

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

  Definition cst_def c :=
    match Σ c with
    | Some (Def Ξ' A t) => if closed t then Some (Ξ', A, t) else None
    | _ => None
    end.

  Lemma cst_def_Some c Ξ' A t :
    cst_def c = Some (Ξ', A, t) ↔ Σ c = Some (Def Ξ' A t) ∧ closed t = true.
  Proof.
    unfold cst_def. destruct (Σ c) as [[] |]. 2: intuition congruence.
    destruct (closed _) eqn: e. 2: intuition congruence.
    intuition congruence.
  Qed.

  Reserved Notation "Γ ⊢ u ⇒ᵨ v"
    (at level 80, u, v at next level).

  Inductive pred_max Γ : term → term → Prop :=
  | pred_max_beta A t t' u u' :
      no_match Ξ (app (lam A t) u) →
      Γ ,, A ⊢ t ⇒ᵨ t' →
      Γ ⊢ u ⇒ᵨ u' →
      Γ ⊢ app (lam A t) u ⇒ᵨ t' <[ u' .. ]

  | pred_max_unfold c ξ Ξ' A t ξ' :
      no_match Ξ (const c ξ) →
      cst_def c = Some (Ξ', A, t) →
      Forall2 (option_rel (pred_max Γ)) ξ ξ' →
      Γ ⊢ const c ξ ⇒ᵨ inst ξ' t

  | pred_max_Pi A B A' B' :
      no_match Ξ (Pi A B) →
      Γ ⊢ A ⇒ᵨ A' →
      Γ ,, A ⊢ B ⇒ᵨ B' →
      Γ ⊢ Pi A B ⇒ᵨ Pi A' B'

  | pred_max_lam A t A' t' :
      no_match Ξ (lam A t) →
      Γ ⊢ A ⇒ᵨ A' →
      Γ ,, A ⊢ t ⇒ᵨ t' →
      Γ ⊢ lam A t ⇒ᵨ lam A' t'

  | pred_max_app u v u' v' :
      is_lam u = false →
      no_match Ξ (app u v) →
      Γ ⊢ u ⇒ᵨ u' →
      Γ ⊢ v ⇒ᵨ v' →
      Γ ⊢ app u v ⇒ᵨ app u' v'

  | pred_max_const c ξ ξ' :
      no_match Ξ (const c ξ) →
      cst_def c = None →
      Forall2 (option_rel (pred_max Γ)) ξ ξ' →
      Γ ⊢ const c ξ ⇒ᵨ const c ξ'

  | pred_max_var x :
      no_match Ξ (var x) →
      Γ ⊢ var x ⇒ᵨ var x

  | pred_max_sort s :
      no_match Ξ (Sort s) →
      Γ ⊢ Sort s ⇒ᵨ Sort s

  | pred_max_assm x :
      no_match Ξ (assm x) →
      Γ ⊢ assm x ⇒ᵨ assm x

  | pred_max_rule n rl t σ σ' :
      pctx_get Ξ n = Some (pComp rl) →
      match_pat rl.(pr_pat) t = Some σ →
      Forall2 (pred_max Γ) σ σ' →
      let rhs := rl.(pr_rep) in
      (* let Θ := rl.(cr_env) in
      let k := length Θ in
      let lhs := rl.(cr_pat) in
      scoped k lhs = true →
      scoped k rhs = true → *)
      Γ ⊢ t ⇒ᵨ rhs <[ slist σ' ]

  where "Γ ⊢ u ⇒ᵨ v" := (pred_max Γ u v).

  Lemma pred_max_ind_alt :
    ∀ (P : list term → term → term → Prop),
      (∀ Γ A t t' u u',
        no_match Ξ (app (lam A t) u) →
        Γ,, A ⊢ t ⇒ᵨ t' →
        P (Γ,, A) t t' →
        Γ ⊢ u ⇒ᵨ u' →
        P Γ u u' →
        P Γ (app (lam A t) u) (t' <[ u'..])
      ) →
      (∀ Γ c ξ Ξ' A t ξ',
        no_match Ξ (const c ξ) →
        cst_def c = Some (Ξ', A, t) →
        Forall2 (option_rel (pred_max Γ)) ξ ξ' →
        Forall2 (option_rel (P Γ)) ξ ξ' →
        P Γ (const c ξ) (inst ξ' t)
      ) →
      (∀ Γ A B A' B',
        no_match Ξ (Pi A B) →
        Γ ⊢ A ⇒ᵨ A' →
        P Γ A A' →
        Γ,, A ⊢ B ⇒ᵨ B' →
        P (Γ,, A) B B' →
        P Γ (Pi A B) (Pi A' B')
      ) →
      (∀ Γ A t A' t',
        no_match Ξ (lam A t) →
        Γ ⊢ A ⇒ᵨ A' →
        P Γ A A' →
        Γ,, A ⊢ t ⇒ᵨ t' →
        P (Γ,, A) t t' →
        P Γ (lam A t) (lam A' t')
      ) →
      (∀ Γ u v u' v',
        is_lam u = false →
        no_match Ξ (app u v) →
        Γ ⊢ u ⇒ᵨ u' →
        P Γ u u' →
        Γ ⊢ v ⇒ᵨ v' →
        P Γ v v' →
        P Γ (app u v) (app u' v')
      ) →
      (∀ Γ c ξ ξ',
        no_match Ξ (const c ξ) →
        cst_def c = None →
        Forall2 (option_rel (pred_max Γ)) ξ ξ' →
        Forall2 (option_rel (P Γ)) ξ ξ' →
        P Γ (const c ξ) (const c ξ')
      ) →
      (∀ Γ x,
        no_match Ξ (var x) →
        P Γ (var x) (var x)
      ) →
      (∀ Γ s,
        no_match Ξ (Sort s) →
        P Γ (Sort s) (Sort s)
      ) →
      (∀ Γ x,
        no_match Ξ (assm x) →
        P Γ (assm x) (assm x)
      ) →
      (∀ Γ n rl t σ σ',
        pctx_get Ξ n = Some (pComp rl) →
        match_pat rl.(pr_pat) t = Some σ →
        Forall2 (pred_max Γ) σ σ' →
        Forall2 (P Γ) σ σ' →
        let rhs := rl.(pr_rep) in
        P Γ t (rhs <[ slist σ'])
      ) →
      ∀ Γ u v, Γ ⊢ u ⇒ᵨ v → P Γ u v.
  Proof.
    intros P hbeta hunf hpi hlam happ hcst hvar hsort hassm hrl.
    fix aux 4. move aux at top.
    intros Γ u v h. destruct h.
    10:{
      eapply hrl. 1-4: eauto.
      clear H0.
      revert σ σ' H1. fix aux1 3.
      intros σ σ' hσ. destruct hσ.
      - constructor.
      - constructor. all: eauto.
    }
    6:{
      eapply hcst. 1-3: assumption.
      clear H.
      revert ξ ξ' H1. fix aux1 3.
      intros ξ ξ' hh. destruct hh as [ | o o' ξ ξ' hh ].
      - constructor.
      - constructor. 2: eauto.
        destruct hh. all: constructor ; eauto.
    }
    2:{
      eapply hunf. 1-3: eauto.
      clear H.
      revert ξ ξ' H1. fix aux1 3.
      intros ξ ξ' hh. destruct hh as [ | o o' ξ ξ' hh ].
      - constructor.
      - constructor. 2: eauto.
        destruct hh. all: constructor ; eauto.
    }
    all: match goal with h : _ |- _ => eapply h end.
    all: eauto.
  Qed.

  Lemma pat_no_lam p σ A b :
    lam A b ≠ (pat_to_term p) <[ σ ].
  Proof.
    destruct p. cbn. discriminate.
  Qed.

  Lemma pat_no_beta p σ A b u :
    app (lam A b) u ≠ (pat_to_term p) <[ σ ].
  Proof.
    destruct p. cbn. discriminate.
  Qed.

  Lemma pat_no_Pi p σ A B :
    Pi A B ≠ (pat_to_term p) <[ σ ].
  Proof.
    destruct p. cbn. discriminate.
  Qed.

  Lemma pat_no_const p σ c ξ :
    const c ξ ≠ (pat_to_term p) <[ σ ].
  Proof.
    destruct p. cbn. discriminate.
  Qed.

  Lemma pat_no_var p σ x :
    var x ≠ (pat_to_term p) <[ σ ].
  Proof.
    destruct p. cbn. discriminate.
  Qed.

  Lemma pat_no_sort p σ s :
    Sort s ≠ (pat_to_term p) <[ σ ].
  Proof.
    destruct p. cbn. discriminate.
  Qed.

  Lemma pat_no_app p σ u v :
    (app u v) ≠ (pat_to_term p) <[ σ ].
  Proof.
    destruct p. cbn. discriminate.
  Qed.

  Lemma match_pat_not_lam p A b σ :
    match_pat p (lam A b) = Some σ →
    False.
  Proof.
    intros h%match_pat_sound.
    eapply pat_no_lam. eassumption.
  Qed.

  Lemma match_pat_not_beta p A b u σ :
    match_pat p (app (lam A b) u) = Some σ →
    False.
  Proof.
    intros h%match_pat_sound.
    eapply pat_no_beta. eassumption.
  Qed.

  Lemma match_pat_not_Pi p A B σ :
    match_pat p (Pi A B) = Some σ →
    False.
  Proof.
    intros h%match_pat_sound.
    eapply pat_no_Pi. eassumption.
  Qed.

  Lemma prove_no_match t :
    (∀ p σ, match_pat p t = Some σ → False) →
    no_match Ξ t.
  Proof.
    intros h.
    unfold no_match.
    destruct find_match as [[[]]|] eqn: e. 2: reflexivity.
    exfalso. eapply find_match_sound in e.
    eapply h. intuition eauto.
  Qed.

  Lemma no_match_lam A t :
    no_match Ξ (lam A t).
  Proof.
    eapply prove_no_match. eauto using match_pat_not_lam.
  Qed.

  Lemma no_match_beta A t u :
    no_match Ξ (app (lam A t) u).
  Proof.
    eapply prove_no_match. eauto using match_pat_not_beta.
  Qed.

  Lemma no_match_Pi A B :
    no_match Ξ (Pi A B).
  Proof.
    eapply prove_no_match. eauto using match_pat_not_Pi.
  Qed.

  Lemma match_pat_not_const p c ξ σ :
    match_pat p (const c ξ) = Some σ →
    False.
  Proof.
    intros h%match_pat_sound.
    eapply pat_no_const. eassumption.
  Qed.

  Lemma no_match_const c ξ :
    no_match Ξ (const c ξ).
  Proof.
    eapply prove_no_match. eauto using match_pat_not_const.
  Qed.

  Lemma match_pat_not_var p x σ :
    match_pat p (var x) = Some σ →
    False.
  Proof.
    intros h%match_pat_sound.
    eapply pat_no_var. eassumption.
  Qed.

  Lemma no_match_var x :
    no_match Ξ (var x).
  Proof.
    eapply prove_no_match. eauto using match_pat_not_var.
  Qed.

  Lemma match_pat_not_sort p s σ :
    match_pat p (Sort s) = Some σ →
    False.
  Proof.
    intros h%match_pat_sound.
    eapply pat_no_sort. eassumption.
  Qed.

  Lemma no_match_sort s :
    no_match Ξ (Sort s).
  Proof.
    eapply prove_no_match. eauto using match_pat_not_sort.
  Qed.

  (* Not yet *)
  Lemma match_pat_not_app p u v σ :
    match_pat p (app u v) = Some σ →
    False.
  Proof.
    intros h%match_pat_sound.
    eapply pat_no_app. eassumption.
  Qed.

  (* TODO MOVE *)
  Lemma lvl_get_In [A] l n a :
    lvl_get (A := A) l n = Some a →
    In a l.
  Proof.
    intros e.
    unfold lvl_get in e.
    destruct (_ <=? _). 1: discriminate.
    eapply nth_error_In. eassumption.
  Qed.

  Lemma no_match_no_match_pat t n rl σ :
    no_match Ξ t →
    pctx_get Ξ n = Some (pComp rl) →
    match_pat rl.(pr_pat) t = Some σ →
    False.
  Proof.
    intros ht hn hm.
    unfold no_match in ht.
    eapply lvl_get_In in hn.
    induction Ξ as [| [| rl'] Ξ' ih]. 1: contradiction.
    - cbn in *. intuition discriminate.
    - cbn in *. destruct match_pat eqn: e. 1: discriminate.
      intuition congruence.
  Qed.

  Lemma match_pat_assm_inv p x σ :
    match_pat p (assm x) = Some σ →
    p = passm x ∧ σ = [].
  Proof.
    intros h.
    destruct p. cbn in h.
    destruct (_ =? _) eqn: e. 2: discriminate.
    rewrite Nat.eqb_eq in e. inversion h. intuition congruence.
  Qed.

  Context (htri : triangle_citerion Ξ).

  Lemma triangle_match n m rl rl' t σ σ' :
    pctx_get Ξ n = Some (pComp rl) →
    match_pat rl.(pr_pat) t = Some σ →
    pctx_get Ξ m = Some (pComp rl') →
    match_pat rl'.(pr_pat) t = Some σ' →
    rl = rl' ∧ σ = σ'.
  Proof.
    intros hn h hm h'.
    eapply htri in hn as e. specialize (e hm).
    eapply match_pat_sound in h as e1, h' as e2.
    destruct rl.(pr_pat). cbn in e1. subst.
    destruct rl'.(pr_pat). cbn in e2. inversion e2. subst.
    specialize (e eq_refl). subst.
    eqtwice. subst.
    eqtwice. subst.
    intuition reflexivity.
  Qed.

  Lemma triangle Γ t u :
    Γ ⊢ t ⇒ u →
    ∃ tᵨ, Γ ⊢ t ⇒ᵨ tᵨ ∧ Γ ⊢ u ⇒ tᵨ.
  Proof.
    induction 1 as [
      ?????? ht iht hu ihu
    | ????????? iht ihξ
    | ???????? hσ ih ?
    | ?????? ihA ? ihB
    | ?????? ihA ? iht
    | ? u ??? hu ihu ? ihv
    | ? c ?? hξ ih
    | ?
    | ?
    | ?
    ] using pred_ind_alt.
    - destruct iht as [tr [ht1 ht2]], ihu as [ur [hu1 hu2]].
      eexists. split.
      + econstructor. 2,3: eassumption.
        apply no_match_beta.
      + eapply pred_subst. 2: eauto.
        intros []. all: cbn. 2: constructor.
        assumption.
    - eapply Forall2_impl in ihξ.
      2:{ intros ??. eapply option_rel_trans_inv. }
      eapply Forall2_trans_inv in ihξ.
      destruct ihξ as (ξᵨ & ? & ?).
      eexists. split.
      + econstructor. 2: rewrite cst_def_Some ; eauto.
        1: apply no_match_const.
        apply Forall2_flip. eapply Forall2_impl. 2: eassumption.
        apply option_rel_flip.
      + apply pred_inst.
        apply Forall2_flip. eapply Forall2_impl. 2: eassumption.
        intros. apply option_rel_flip. eapply option_rel_impl. 2: eassumption.
        auto.
    - eapply Forall2_trans_inv in ih as (σᵨ & ih%Forall2_flip & hr%Forall2_flip).
      eexists. split.
      + econstructor. all: eassumption.
      + eapply pred_subst. 2: apply pred_refl.
        intros x. clear ih hσ. induction hr in x |- *.
        * cbn. constructor.
        * cbn. destruct x.
          -- cbn. assumption.
          -- cbn. eauto.
    - destruct ihA as [Ar [hA1 hA2]], ihB as [Br [hB1 hB2]].
      eexists. split.
      + econstructor. 2-3: eassumption.
        apply no_match_Pi.
      + econstructor. 1: eauto.
        eapply pred_ctx_irr. eauto.
    - destruct ihA as [Ar [hA1 hA2]], iht as [tr [ht1 ht2]].
      eexists. split.
      + econstructor. 2-3: eassumption.
        apply no_match_lam.
      + econstructor. 1: eauto.
        eapply pred_ctx_irr. eauto.
    - destruct ihu as [ur [hu1 hu2]], ihv as [vr [hv1 hv2]].
      destruct (is_lam u) eqn: eu.
      + eapply is_lam_inv in eu as (A & b & ->).
        inversion hu1.
        2:{ exfalso. subst. eapply match_pat_not_lam. eassumption. }
        subst.
        eexists. split.
        * econstructor. 2-3: eassumption.
          apply no_match_beta.
        * inversion hu.
          1:{ exfalso. subst. eapply match_pat_not_lam. eassumption. }
          subst. econstructor. 2: assumption.
          inversion hu2.
          1:{ exfalso. subst. eapply match_pat_not_lam. eassumption. }
          subst. assumption.
      + destruct (find_match Ξ (app u v)) as [[[] ?]|] eqn:e.
        * (* For now we conclude by contradiction, later have some match_pat
            property.
          *)
          exfalso.
          eapply find_match_sound in e.
          eapply match_pat_not_app. intuition eauto.
        * eexists. split.
          -- econstructor. all: eauto.
          -- econstructor. all: assumption.
    - eapply Forall2_impl in ih.
      2:{ intros ??. eapply option_rel_trans_inv. }
      eapply Forall2_trans_inv in ih as (ξᵨ & ?%Forall2_flip & ?).
      (* Testing whether the constant is defined properly *)
      destruct (cst_def c) as [[[Ξ' A] t] |] eqn: ec.
      + eapply cst_def_Some in ec as e.
        eexists. split.
        * econstructor. 1: apply no_match_const. 1: intuition eauto.
          eapply Forall2_impl. 2: eassumption.
          cbn. intros ??. apply option_rel_flip.
        * econstructor. 1,2: intuition eauto.
          eauto using Forall2_flip, Forall2_impl, option_rel_flip, option_rel_impl.
      + eexists. split.
        * eapply pred_max_const. 2: eassumption.
          1: apply no_match_const.
          eauto using Forall2_flip, Forall2_impl, option_rel_flip, option_rel_impl.
        * econstructor.
          eauto using Forall2_flip, Forall2_impl, option_rel_flip, option_rel_impl.
    - eexists. split.
      + econstructor. apply no_match_var.
      + constructor.
    - eexists. split.
      + econstructor. apply no_match_sort.
      + constructor.
    - destruct (find_match Ξ (assm x)) as [[[] ?] |] eqn: e.
      + eapply find_match_sound in e as h. destruct h as (en & ep).
        eapply match_pat_assm_inv in ep as h. destruct h as [? ->].
        eexists. split.
        * eapply pred_max_rule. 1,2: eassumption.
          constructor.
        * econstructor. 1,2: eassumption.
          constructor.
      + eexists. split.
        * econstructor. assumption.
        * constructor.
    Unshelve. constructor.
  Qed.

  Lemma pred_max_functional Γ t u v :
    Γ ⊢ t ⇒ᵨ u →
    Γ ⊢ t ⇒ᵨ v →
    u = v.
  Proof.
    intros hu hv.
    induction hu as [ | | | | | | | | | ??????? h ? ihσ ? ] in v, hv |- *
    using pred_max_ind_alt.
    - inversion hv.
      3:{ exfalso. eapply no_match_no_match_pat. all: eassumption. }
      2: discriminate.
      subst. f_equal. 1: f_equal. all: eauto.
    - inversion hv.
      3:{ exfalso. subst. eapply match_pat_not_const. eassumption. }
      2: congruence.
      subst. f_equal.
      + eapply Forall2_eq.
        eapply Forall2_impl, Forall2_trans. 2,3: eassumption.
        cbn. intros ?? (? & h1 & h2).
        destruct h1.
        * inversion h2. reflexivity.
        * inversion h2. subst. f_equal. eauto.
      + eqtwice. subst. eauto.
    - inversion hv.
      2:{ exfalso. eapply no_match_no_match_pat. all: eassumption. }
      subst. f_equal. all: eauto.
    - inversion hv.
      2:{ exfalso. eapply no_match_no_match_pat. all: eassumption. }
      subst. f_equal. all: eauto.
    - inversion hv.
      3:{ exfalso. eapply no_match_no_match_pat. all: eassumption. }
      1:{ subst. discriminate. }
      subst. f_equal. all: eauto.
    - inversion hv.
      1: congruence.
      2:{ exfalso. subst. eauto using no_match_no_match_pat. }
      subst. f_equal.
      eapply Forall2_eq.
      eapply Forall2_impl, Forall2_trans. 2,3: eassumption.
      cbn. intros ?? (? & h1 & h2).
      destruct h1.
      + inversion h2. reflexivity.
      + inversion h2. subst. f_equal. eauto.
    - inversion hv.
      2:{ exfalso. eapply match_pat_not_var. eassumption. }
      reflexivity.
    - inversion hv.
      2:{ exfalso. eapply match_pat_not_sort. eassumption. }
      reflexivity.
    - inversion hv.
      2:{ exfalso. subst. eauto using no_match_no_match_pat. }
      reflexivity.
    - inversion hv. 1-9: exfalso ; subst ; eapply no_match_no_match_pat ; eauto.
      subst.
      eapply triangle_match in h as ht. 2-4: eassumption.
      destruct ht as [-> ->].
      eqtwice.
      apply ext_term. intros ?. f_equal.
      apply Forall2_eq.
      eapply Forall2_impl, Forall2_trans. 2,3: eassumption.
      cbn. intros ?? (? & h1 & h2). eauto.
  Qed.

  Lemma pred_diamond Γ :
    diamond (pred Γ).
  Proof.
    intros t u v hu hv.
    eapply triangle in hu as [w [hw ?]], hv as [? []].
    eapply pred_max_functional in hw as e. 2: eassumption.
    subst. exists w. intuition eauto.
  Qed.

  Lemma pred_confluence Γ :
    confluent (pred Γ).
  Proof.
    apply diamond_confluent.
    apply pred_diamond.
  Qed.

  #[export] Instance Reflexive_pred Γ :
    Reflexive (pred Γ).
  Proof.
    intros t.
    apply pred_refl.
  Qed.

End Red.

Notation "Σ ;; Ξ | Γ ⊢ u ⇒ v" :=
  (pred Σ Ξ Γ u v)
  (at level 80, u, v at next level).

(** ** Sandwishing reduction *)

Lemma ictx_get_pctx Ξ n rl :
  ictx_get (pctx_ictx Ξ) n = Some (Comp rl) →
  ∃ rl',
    pctx_get Ξ n = Some (pComp rl') ∧
    rl = prule_crule rl'.
Proof.
  intros e. unfold pctx_ictx in e.
  rewrite lvl_get_map in e.
  destruct (pctx_get _ _) as [[] |] eqn: e'. 1,3: discriminate.
  cbn in e. inversion e.
  eexists. intuition eauto.
Qed.

Lemma match_pat_lhs rl σ :
  let lhs := (prule_crule rl).(cr_pat) in
  let Θ := (prule_crule rl).(cr_env) in
  let k := length Θ in
  match_pat rl.(pr_pat) (lhs <[ σ ]) = Some (listify k σ).
Proof.
  intros lhs Θ k.
Admitted.

Lemma eq_subst_listify k σ :
  eq_subst_on k (slist (listify k σ)) σ.
Proof.
  intros x h.
  induction k as [| k ih] in x, h, σ |- *. 1: lia.
  cbn. destruct x as [| x].
  - reflexivity.
  - cbn. apply (ih (S >> σ)). lia.
Qed.

Lemma red1_pred Σ Ξ Γ u v :
  Σ ;; pctx_ictx Ξ | Γ ⊢ u ↦ v →
  Σ ;; Ξ | Γ ⊢ u ⇒ v.
Proof.
  intros h.
  induction h using red1_ind_alt.
  all: try solve [ econstructor ; eauto using pred_refl ].
  - econstructor. 1,2: eassumption.
    apply Forall2_diag. rewrite Forall_forall.
    intros o h. apply option_rel_diag. rewrite OnSome_onSome.
    destruct o. all: cbn. 2: trivial.
    apply pred_refl.
  - eapply ictx_get_pctx in H as h. destruct h as (rl' & hn & ->).
    eapply pred_meta_r.
    + econstructor.
      * eassumption.
      * eapply match_pat_lhs.
      * apply Forall2_diag. apply Forall_forall.
        intros. apply pred_refl.
    + eapply ext_term_scoped. 1: eassumption.
      apply eq_subst_listify.
  - econstructor.
    eapply OnOne2_refl_Forall2. 1: exact _.
    eapply OnOne2_impl. 2: eassumption.
    intros ??. apply some_rel_option_rel.
Qed.

Lemma pred_red Σ Ξ Γ u v :
  Σ ;; Ξ | Γ ⊢ u ⇒ v →
  Σ ;; pctx_ictx Ξ | Γ ⊢ u ↦* v.
Proof.
  intros h.
  induction h using pred_ind_alt.
  - etransitivity.
    + constructor. econstructor.
    + (* Closure by subst *) admit.
      (* Alternatively, I could reduce first in the subterms *)
  - admit. (* Here we will need good_cstrs unless we change red first
      Probably best to do it on the red side and at the boundary with
      conversion.
    *)
  - admit.
  - admit.
Admitted.
