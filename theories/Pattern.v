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

  | red_Pi A B A' B' :
      Γ ⊢ A ⇒ A' →
      Γ ,, A ⊢ B ⇒ B' →
      Γ ⊢ Pi A B ⇒ Pi A' B'

  | red_lam A t A' t' :
      Γ ⊢ A ⇒ A' →
      Γ ,, A ⊢ t ⇒ t' →
      Γ ⊢ lam A t ⇒ lam A' t'

  | red_app u v u' v' :
      Γ ⊢ u ⇒ u' →
      Γ ⊢ v ⇒ v' →
      Γ ⊢ app u v ⇒ app u' v'

  | red_const c ξ ξ' :
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

End Red.

Notation "Σ ;; Ξ | Γ ⊢ u ⇒ v" :=
  (pred Σ Ξ Γ u v)
  (at level 80, u, v at next level).
