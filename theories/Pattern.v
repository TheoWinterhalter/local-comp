(** * Patterns

  We provide a notion of pattern as well as ways to verify the criteria
  imposed on reduction in the [Reduction] module.

  For now, we'll start with a very very weak version which only accepts one
  symbol as a left-hand side to a rule.
  TODO: Improve

**)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing BasicMetaTheory
  GScope Inversion Reduction.
From Stdlib Require Import Setoid Morphisms Relation_Definitions
  Relation_Operators.
From Equations Require Import Equations.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Require Import Equations.Prop.DepElim.

Inductive pat :=
| passm (M : eref) (x : aref).

Definition pat_to_term p :=
  match p with
  | passm M x => assm M x
  end.

(* TODO UPSTREAM *)
Definition get_rule (Σ : gctx) Ξ M n : option crule :=
  match ectx_get Ξ M with
  | Some (E, ξ') =>
    match Σ E with
    | Some (Ext Ξ' Δ R) =>
      nth_error R n
    | _ => None
    end
  | _ => None
  end.

Lemma get_get_rule (Σ : gctx) Ξ M n E ξ' Ξ' Δ R rl :
  ectx_get Ξ M = Some (E, ξ') →
  Σ E = Some (Ext Ξ' Δ R) →
  nth_error R n = Some rl →
  get_rule Σ Ξ M n = Some rl.
Proof.
  intros hM hE hn.
  unfold get_rule. rewrite hM, hE. assumption.
Qed.

Definition pattern_rules Σ Ξ :=
  ∀ M n rl,
    get_rule Σ Ξ M n = Some rl →
    ∃ p, rl.(cr_pat) = pat_to_term p.

Definition triangle_citerion Σ Ξ :=
  ∀ M N m n rl1 rl2,
    get_rule Σ Ξ M m = Some rl1 →
    get_rule Σ Ξ N n = Some rl2 →
    rl1.(cr_pat) = rl2.(cr_pat) →
    M = N ∧ m = n.

(** ** Parallel reduction *)

Section Red.

  Reserved Notation "Γ ⊢ u ⇒ v"
    (at level 80, u, v at next level).

  Context (Σ : gctx) (Ξ : ectx).

  Inductive pred (Γ : ctx) : term → term → Prop :=

  (** Computation rules **)

  | pred_beta A t t' u u' :
      Γ ,, A ⊢ t ⇒ t' →
      Γ ⊢ u ⇒ u' →
      Γ ⊢ app (lam A t) u ⇒ t' <[ u' .. ]

  | pred_unfold c ξ Ξ' A t ξ' t' :
      Σ c = Some (Def Ξ' A t) →
      inst_equations Σ Ξ Γ ξ Ξ' →
      closed t = true →
      ∙ ⊢ t ⇒ t' →
      Forall2 (Forall2 (pred Γ)) ξ ξ' →
      Γ ⊢ const c ξ ⇒ einst ξ' t'

  | pred_rule E Ξ' Δ R M ξ' n rule σ σ' :
      Σ E = Some (Ext Ξ' Δ R) →
      ectx_get Ξ M = Some (E, ξ') →
      nth_error R n = Some rule →
      let δ := length Δ in
      let lhs := rlhs M ξ' δ rule in
      let rhs := rrhs M ξ' δ rule in
      let k := length rule.(cr_env) in
      scoped k lhs = true →
      scoped k rhs = true →
      (∀ m, Γ ⊢ σ m ⇒ σ' m) →
      Γ ⊢ lhs <[ σ ] ⇒ rhs <[ σ' ]

  (** Congruence rules **)

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
      Forall2 (Forall2 (pred Γ)) ξ ξ' →
      Γ ⊢ const c ξ ⇒ const c ξ'

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
        Forall2 (Forall2 (pred Γ)) ξ ξ' →
        Forall2 (Forall2 (P Γ)) ξ ξ' →
        P Γ (const c ξ) (einst ξ' t')
      ) →
      (∀ Γ E Ξ' Δ R M ξ' n rule σ σ',
        Σ E = Some (Ext Ξ' Δ R) →
        ectx_get Ξ M = Some (E, ξ') →
        nth_error R n = Some rule →
        let δ := Datatypes.length Δ in
        let lhs := rlhs M ξ' δ rule in
        let rhs := rrhs M ξ' δ rule in
        let k := Datatypes.length (cr_env rule) in
        scoped k lhs = true →
        scoped k rhs = true →
        (∀ m : nat, Γ ⊢ σ m ⇒ σ' m) →
        (∀ m : nat, P Γ (σ m) (σ' m)) →
        P Γ (lhs <[ σ]) (rhs <[ σ'])
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
        Forall2 (Forall2 (pred Γ)) ξ ξ' →
        Forall2 (Forall2 (P Γ)) ξ ξ' →
        P Γ (const c ξ) (const c ξ')
      ) →
      ∀ Γ u v, Γ ⊢ u ⇒ v → P Γ u v.
  Proof.
    intros P hbeta hunf hrl hpi hlam happ hconst.
    fix aux 4. move aux at top.
    intros Γ u v h. destruct h.
    7:{
      eapply hconst. 1: assumption.
      revert ξ ξ' H. fix aux1 3.
      intros ξ ξ' h. destruct h as [ | σ σ' ξ ξ' h ].
      - constructor.
      - constructor. 2: eauto.
        revert σ σ' h. fix aux2 3.
        intros σ σ' h. destruct h as [ | u v σ σ' h ].
        + constructor.
        + constructor. all: auto.
    }
    2:{
      eapply hunf. 1-6: eauto.
      clear H0.
      revert ξ ξ' H2. fix aux1 3.
      intros ξ ξ' hh. destruct hh as [ | σ σ' ξ ξ' hh ].
      - constructor.
      - constructor. 2: eauto.
        revert σ σ' hh. fix aux2 3.
        intros σ σ' hh. destruct hh as [ | u v σ σ' hh ].
        + constructor.
        + constructor. all: auto.
    }
    all: match goal with h : _ |- _ => eapply h end.
    all: eauto.
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
      Forall2 (Forall2 (pred_max Γ)) ξ ξ' →
      Γ ⊢ const c ξ ⇒ᵨ einst ξ' t'

  | pred_max_rule E Ξ' Δ R M ξ' n rule σ σ' :
      Σ E = Some (Ext Ξ' Δ R) →
      ectx_get Ξ M = Some (E, ξ') →
      nth_error R n = Some rule →
      let δ := length Δ in
      let lhs := rlhs M ξ' δ rule in
      let rhs := rrhs M ξ' δ rule in
      (∀ m, Γ ⊢ σ m ⇒ᵨ σ' m) →
      Γ ⊢ lhs <[ σ ] ⇒ᵨ rhs <[ σ' ]

  (** Congruence rules **)

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
      Γ ⊢ u ⇒ᵨ u' →
      Γ ⊢ v ⇒ᵨ v' →
      Γ ⊢ app u v ⇒ᵨ app u' v'

  | predmax_const c ξ ξ' :
      Forall2 (Forall2 (pred_max Γ)) ξ ξ' →
      Γ ⊢ const c ξ ⇒ᵨ const c ξ'

  where "Γ ⊢ u ⇒ᵨ v" := (pred_max Γ u v).

  Context (hpr : pattern_rules Σ Ξ).

  Lemma pattern_rules_lhs_no_lam M E ξ' Ξ' Δ R n rl σ A b :
    ectx_get Ξ M = Some (E, ξ') →
    Σ E = Some (Ext Ξ' Δ R) →
    nth_error R n = Some rl →
    let δ := length Δ in
    let lhs := rlhs M ξ' δ rl in
    lhs <[ σ ] ≠ lam A b.
  Proof.
    intros hM hE hn δ lhs e.
    eapply get_get_rule in hn. 2,3: eassumption.
    eapply hpr in hn as [p ep].
    subst lhs. unfold rlhs in e.
    set (t := rl.(cr_pat)) in *. clearbody t. subst t.
    unfold rule_tm in e.
    destruct p. cbn in e.
    (* Problem here: there is no guarantee ξ' won't instantiate the pattern
      We should probably enforce it somehow.


      In fact, the problem is more complex: with the current setting, we can
      never refer to symbols from other interfaces because they will always be
      instantiated, so there is no telling what they become after ξ' has been
      applied. In other words, my definition doesn't actually offer interleaving
      or layering as I had intended.

      A major change is likely needed.
    *)
  Abort.

  Lemma triangle Γ t u :
    Γ ⊢ t ⇒ u →
    ∃ tᵨ, Γ ⊢ t ⇒ᵨ tᵨ ∧ Γ ⊢ u ⇒ tᵨ.
  Proof.
    induction 1 as [
      ?????? ht iht hu ihu
    | ???????????? iht ? ihξ
    | ????????????????????? ih
    | ?????? ihA ? ihB
    | ?????? ihA ? iht
    | ? u ???? ihu ? ihv
    | ???? ih
    ] using pred_ind_alt.
    - destruct iht as [tr [ht1 ht2]], ihu as [ur [hu1 hu2]].
      eexists. split.
      + econstructor. all: eassumption.
      + (* Need substitution lemma for pred *) admit.
    - destruct iht as [tr [ht1 ht2]].
      admit.
    - (* The current ∀∃ is not enough to get a substitution
        It might be easier with an implementation of matching.
        We could also define a ρ function instead.

        We will anyway need to define matching for the rule selection thing
        when we get more interesting patterns.
      *)
      admit.
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
        1:{ exfalso. admit. }
        subst.
        eexists. split.
        * econstructor. all: eassumption.
        * admit.
      + eexists. split.
        * econstructor. all: eassumption.
        * econstructor. all: assumption.
    - admit.
  Admitted.

  Lemma pred_max_functional Γ t u v :
    Γ ⊢ t ⇒ᵨ u →
    Γ ⊢ t ⇒ᵨ v →
    u = v.
  Proof.
  Admitted.

  Lemma diamond Γ t u v :
    Γ ⊢ t ⇒ u →
    Γ ⊢ t ⇒ v →
    ∃ w, Γ ⊢ u ⇒ w ∧ Γ ⊢ v ⇒ w.
  Proof.
    intros hu hv.
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
