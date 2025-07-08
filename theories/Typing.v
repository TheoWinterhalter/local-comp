(** * Typing *)

From Stdlib Require Import Utf8 List Arith Bool.
From LocalComp.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

(** ** Closedness property *)

Fixpoint scoped n t :=
  match t with
  | var m => m <? n
  | Sort _ => true
  | Pi A B => scoped n A && scoped (S n) B
  | lam A t => scoped n A && scoped (S n) t
  | app u v => scoped n u && scoped n v
  | const c ξ => forallb (onSomeb (scoped n)) ξ
  | assm x => true
  end.

Notation closed t := (scoped 0 t).

Notation scoped_instance k ξ :=
  (forallb (λ t, onSomeb (scoped k) t) ξ).

Notation closed_instance ξ :=
  (scoped_instance 0 ξ).

(** ** Global scoping (see GScope) *)

Inductive gscope (Σ : gctx) : term → Prop :=
| gscope_var x : gscope Σ (var x)
| gscope_sort i : gscope Σ (Sort i)
| gscope_pi A B : gscope Σ A → gscope Σ B → gscope Σ (Pi A B)
| gscope_lam A t : gscope Σ A → gscope Σ t → gscope Σ (lam A t)
| gscope_app u v : gscope Σ u → gscope Σ v → gscope Σ (app u v)
| gscope_const c ξ Ξ' A t :
    Σ c = Some (Def Ξ' A t) →
    Forall (OnSome (gscope Σ)) ξ →
    gscope Σ (const c ξ)
| gscope_assm x : gscope Σ (assm x).

Notation gscope_instance Σ ξ := (Forall (OnSome (gscope Σ)) ξ).

Definition gscope_crule Σ rule :=
  Forall (gscope Σ) rule.(cr_env) ∧
  gscope Σ rule.(cr_pat) ∧
  gscope Σ rule.(cr_rep) ∧
  gscope Σ rule.(cr_typ).

Section Typing.

Reserved Notation "Γ ⊢ t : A"
  (at level 80, t, A at next level).

Reserved Notation "u ≡ v"
  (at level 80).

Context (Σ : gctx) (Ξ : ictx).

(** Checking that an instance verifies the necessary equations *)
Section Equations.

  Context (conversion : term → term → Prop).

  Notation "u ≡ v" := (conversion u v) (at level 80).

  Definition inst_equations_ (ξ : instance) (Ξ' : ictx) :=
    ∀ x rl,
      ictx_get Ξ' x = Some (Comp rl) →
      let m := length rl.(cr_env) in
      (* let Θ := ctx_inst ξ rl.(cr_env) in *)
      let lhs := inst (liftn m ξ) rl.(cr_pat) in
      let rhs := inst (liftn m ξ) rl.(cr_rep) in
      nth_error ξ x = Some None ∧
      scoped m rl.(cr_pat) = true ∧
      scoped m rl.(cr_rep) = true ∧
      (* Γ ,,, Θ ⊢ *) lhs ≡ rhs.

End Equations.

Inductive conversion : term → term → Prop :=

(** Computation rules *)

| conv_beta :
    ∀ A t u,
      app (lam A t) u ≡ t <[ u .. ]

| conv_unfold :
    ∀ c ξ Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      inst_equations_ conversion ξ Ξ' →
      closed t = true →
      const c ξ ≡ inst ξ t

| conv_red :
    ∀ n rl σ,
      ictx_get Ξ n = Some (Comp rl) →
      let Θ := rl.(cr_env) in
      let k := length Θ in
      let lhs := rl.(cr_pat) in
      let rhs := rl.(cr_rep) in
      scoped k lhs = true →
      scoped k rhs = true →
      lhs <[ σ ] ≡ rhs <[ σ ]

(** Congruence rules *)

| cong_Pi :
    ∀ A A' B B',
      A ≡ A' →
      B ≡ B' →
      Pi A B ≡ Pi A' B'

| cong_lam :
    ∀ A A' t t',
      A ≡ A' →
      t ≡ t' →
      lam A t ≡ lam A' t'

| cong_app :
    ∀ u u' v v',
      u ≡ u' →
      v ≡ v' →
      app u v ≡ app u' v'

| cong_const :
    ∀ c ξ ξ',
      Forall2 (option_rel conversion) ξ ξ' →
      const c ξ ≡ const c ξ'

(** Structural rules *)

| conv_refl :
    ∀ u,
      u ≡ u

| conv_sym :
    ∀ u v,
      u ≡ v →
      v ≡ u

| conv_trans :
    ∀ u v w,
      u ≡ v →
      v ≡ w →
      u ≡ w

where "u ≡ v" := (conversion u v).

Notation inst_equations := (inst_equations_ conversion).

(** ** Instance typing *)
Section Inst.

  Context (typing : ctx → term → term → Prop).

  Notation "Γ ⊢ u : A" := (typing Γ u A).

  Definition inst_iget_ (Γ : ctx) (ξ : instance) (Ξ' : ictx) :=
    ∀ n A,
      ictx_get Ξ' n = Some (Assm A) →
      closed A = true ∧
      iget_def ξ n ∧
      Γ ⊢ iget ξ n : inst ξ A.

  Definition inst_typing_ (Γ : ctx) (ξ : instance) (Ξ' : ictx) :=
    inst_equations ξ Ξ' ∧ inst_iget_ Γ ξ Ξ' ∧ length ξ = length Ξ'.

End Inst.

Inductive typing (Γ : ctx) : term → term → Prop :=

| type_var :
    ∀ x A,
      nth_error Γ x = Some A →
      Γ ⊢ var x : (plus (S x)) ⋅ A

| type_sort :
    ∀ i,
      Γ ⊢ Sort i : Sort (S i)

| type_pi :
    ∀ i j A B,
      Γ ⊢ A : Sort i →
      Γ ,, A ⊢ B : Sort j →
      Γ ⊢ Pi A B : Sort (max i j)

| type_lam :
    ∀ i j A B t,
      Γ ⊢ A : Sort i →
      Γ ,, A ⊢ B : Sort j →
      Γ ,, A ⊢ t : B →
      Γ ⊢ lam A t : Pi A B

| type_app :
    ∀ i j A B t u,
      Γ ⊢ t : Pi A B →
      Γ ⊢ u : A →
      Γ ⊢ A : Sort i →
      Γ ,, A ⊢ B : Sort j →
      Γ ⊢ app t u : B <[ u .. ]

| type_const :
    ∀ c ξ Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      inst_typing_ typing Γ ξ Ξ' →
      closed A = true →
      Γ ⊢ const c ξ : inst ξ A

| type_assm :
    ∀ x A,
      ictx_get Ξ x = Some (Assm A) →
      closed A = true →
      Γ ⊢ assm x : A

| type_conv :
    ∀ i A B t,
      Γ ⊢ t : A →
      A ≡ B →
      Γ ⊢ B : Sort i →
      Γ ⊢ t : B

where "Γ ⊢ t : A" := (typing Γ t A).

(** ** Context formation *)

Inductive wf : ctx → Prop :=
| wf_nil : wf ∙
| wf_cons :
    ∀ Γ i A,
      wf Γ →
      Γ ⊢ A : Sort i →
      wf (Γ ,, A).

End Typing.

Notation "Σ ;; Ξ ⊢ u ≡ v" :=
  (conversion Σ Ξ u v)
  (at level 80, u, v at next level, format "Σ  ;;  Ξ  ⊢  u  ≡  v").

Notation "Σ ;; Ξ | Γ ⊢ t : A" :=
  (typing Σ Ξ Γ t A)
  (at level 80, t, A at next level, format "Σ  ;;  Ξ  |  Γ  ⊢  t  :  A").

(** ** Equation typing *)

Definition equation_typing Σ Ξ ε :=
  let k := length ε.(eq_env) in
  wf Σ Ξ ε.(eq_env) ∧
  (∃ i, Σ ;; Ξ | ε.(eq_env) ⊢ ε.(eq_typ) : Sort i) ∧
  Σ ;; Ξ | ε.(eq_env) ⊢ ε.(eq_lhs) : ε.(eq_typ) ∧
  Σ ;; Ξ | ε.(eq_env) ⊢ ε.(eq_rhs) : ε.(eq_typ).

(** ** Interface typing *)

Inductive iwf (Σ : gctx) : ictx → Prop :=
| iwf_nil : iwf Σ []

| iwf_assm A Ξ i :
    iwf Σ Ξ →
    Σ ;; Ξ | ∙ ⊢ A : Sort i →
    iwf Σ (Assm A :: Ξ)

| iwf_comp rl Ξ :
    iwf Σ Ξ →
    gscope_crule Σ rl →
    equation_typing Σ Ξ (crule_eq rl) →
    iwf Σ (Comp rl :: Ξ).

(** ** Global environment typing *)

Inductive gwf : gctx → Prop :=
| gwf_nil : gwf []

| gwf_def c (Σ : gctx) Ξ A t i :
    Σ c = None → (* freshness *)
    gwf Σ →
    iwf Σ Ξ →
    Σ ;; Ξ | ∙ ⊢ A : Sort i → (* Redundant, makes proofs easier *)
    Σ ;; Ξ | ∙ ⊢ t : A →
    gwf ((c, Def Ξ A t) :: Σ).

(** Automation *)

Create HintDb conv discriminated.
Create HintDb type discriminated.

Hint Resolve conv_beta conv_unfold cong_Pi cong_lam cong_app cong_const
  conv_refl
: conv.

Hint Resolve type_var type_sort type_pi type_lam type_app type_const type_assm
: type.

Ltac ttconv :=
  unshelve typeclasses eauto with conv shelvedb ; shelve_unifiable.

Ltac tttype :=
  unshelve typeclasses eauto with type shelvedb ; shelve_unifiable.

(** Util *)

Lemma meta_conv :
  ∀ Σ Ξ Γ t A B,
    Σ ;; Ξ | Γ ⊢ t : A →
    A = B →
    Σ ;; Ξ | Γ ⊢ t : B.
Proof.
  intros Σ Ξ Γ t A B h ->. assumption.
Qed.

Lemma meta_conv_trans_l :
  ∀ Σ Ξ u v w,
    u = v →
    Σ ;; Ξ ⊢ v ≡ w →
    Σ ;; Ξ ⊢ u ≡ w.
Proof.
  intros Σ Ξ ??? <- h. assumption.
Qed.

Lemma meta_conv_trans_r :
  ∀ Σ Ξ u v w,
    Σ ;; Ξ ⊢ u ≡ v →
    v = w →
    Σ ;; Ξ ⊢ u ≡ w.
Proof.
  intros Σ Ξ u v ? h <-. assumption.
Qed.

Lemma meta_conv_refl :
  ∀ Σ Ξ u v,
    u = v →
    Σ ;; Ξ ⊢ u ≡ v.
Proof.
  intros Σ Ξ u ? <-. ttconv.
Qed.

Notation inst_equations Σ Ξ := (inst_equations_ (conversion Σ Ξ)).
Notation inst_iget Σ Ξ := (inst_iget_ (typing Σ Ξ)).
Notation inst_typing Σ Ξ := (inst_typing_ Σ Ξ (typing Σ Ξ)).
