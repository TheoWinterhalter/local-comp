(** Typing **)

From Stdlib Require Import Utf8 List Arith Bool.
From LocalComp.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

(** Closedness property **)

Fixpoint scoped n t :=
  match t with
  | var m => m <? n
  | Sort _ => true
  | Pi A B => scoped n A && scoped (S n) B
  | lam A t => scoped n A && scoped (S n) t
  | app u v => scoped n u && scoped n v
  | const c ξ => forallb (forallb (scoped n)) ξ
  | assm M x => true
  end.

Notation closed t := (scoped 0 t).

Definition closed_eargs (ξ : eargs) :=
  forallb (forallb (λ t, closed t)) ξ.

Section Typing.

Reserved Notation "Γ ⊢ t : A"
  (at level 80, t, A at next level).

Reserved Notation "Γ ⊢ u ≡ v"
  (at level 80, u, v at next level).

Context (Σ : gctx) (Ξ : ectx).

Inductive conversion (Γ : ctx) : term → term → Prop :=

(** Computation rules **)

| conv_beta :
    ∀ A t u,
      Γ ⊢ app (lam A t) u ≡ t <[ u .. ]

| conv_unfold :
    ∀ c ξ Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      closed t = true →
      Γ ⊢ const c ξ ≡ einst ξ t

| conv_red :
    ∀ E Ξ' Δ R M ξ' n rule σ,
      Σ E = Some (Ext Ξ' Δ R) →
      ectx_get Ξ M = Some (E, ξ') →
      nth_error R n = Some rule →
      let δ := length Δ in
      let lhs := rule_lhs M ξ' δ rule in
      let rhs := rule_rhs M ξ' δ rule in
      let k := length rule.(cr_env) in
      scoped k lhs = true →
      scoped k rhs = true →
      Γ ⊢ lhs <[ σ ] ≡ rhs <[ σ ]

(** Congruence rules **)

| cong_Pi :
    ∀ A A' B B',
      Γ ⊢ A ≡ A' →
      Γ ,, A ⊢ B ≡ B' →
      Γ ⊢ Pi A B ≡ Pi A' B'

| cong_lam :
    ∀ A A' t t',
      Γ ⊢ A ≡ A' →
      Γ ,, A ⊢ t ≡ t' →
      Γ ⊢ lam A t ≡ lam A' t'

| cong_app :
    ∀ u u' v v',
      Γ ⊢ u ≡ u' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ app u v ≡ app u' v'

| cong_const :
    ∀ c ξ ξ',
      Forall2 (Forall2 (conversion Γ)) ξ ξ' →
      Γ ⊢ const c ξ ≡ const c ξ'

(** Structural rules **)

| conv_refl :
    ∀ u,
      Γ ⊢ u ≡ u

| conv_sym :
    ∀ u v,
      Γ ⊢ u ≡ v →
      Γ ⊢ v ≡ u

| conv_trans :
    ∀ u v w,
      Γ ⊢ u ≡ v →
      Γ ⊢ v ≡ w →
      Γ ⊢ u ≡ w

where "Γ ⊢ u ≡ v" := (conversion Γ u v).

(** Turn list into parallel substitution **)

Definition dummy := (Sort 0).

Fixpoint slist (l : list term) :=
  match l with
  | [] => λ _, dummy
  | u :: l => u .: slist l
  end.

(** Instance typing (relative to typing for now) **)
Section Inst.

  Context (typing : ctx → term → term → Prop).

  Notation "Γ ⊢ u : A" := (typing Γ u A).

  Definition inst_equations (Γ : ctx) (ξ : eargs) (Ξ' : ectx) :=
    ∀ E M ξ',
      ectx_get Ξ' M = Some (E, ξ') →
      ∃ Ξ'' Δ R,
        Σ E = Some (Ext Ξ'' Δ R) ∧
        ∀ n rule,
          nth_error R n = Some rule →
          let m := length rule.(cr_env) in
          let δ := length Δ in
          let Θ := ctx_einst ξ (ctx_einst ξ' rule.(cr_env)) in
          let lhs0 := rule_lhs M ξ' δ rule in
          let rhs0 := rule_rhs M ξ' δ rule in
          scoped m lhs0 = true →
          scoped m rhs0 = true →
          let lhs := einst (liftn m ξ) lhs0 in
          let rhs := einst (liftn m ξ) rhs0 in
          Γ ,,, Θ ⊢ lhs ≡ rhs.

  Definition inst_eget_ (Γ : ctx) (ξ : eargs) (Ξ' : ectx) :=
    ∀ M E ξ',
      ectx_get Ξ' M = Some (E, ξ') →
      closed_eargs ξ' = true ∧
      ∃ Ξ'' Δ R,
        Σ E = Some (Ext Ξ'' Δ R) ∧
        ∀ x A,
          nth_error Δ x = Some A →
          Γ ⊢ eget ξ M x : einst ξ (delocal M (einst ξ' (plus (S x) ⋅ A))).

  Definition inst_typing_ (Γ : ctx) (ξ : eargs) (Ξ' : ectx) :=
    inst_equations Γ ξ Ξ' ∧ inst_eget_ Γ ξ Ξ'.

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
      Γ ⊢ const c ξ : einst ξ A

| type_assm :
    ∀ M x E ξ Ξ' Δ R A,
      ectx_get Ξ M = Some (E, ξ) →
      Σ E = Some (Ext Ξ' Δ R) →
      nth_error Δ x = Some A →
      closed_eargs ξ = true →
      Γ ⊢ assm M x : delocal M (einst ξ ((plus (S x)) ⋅ A))

| type_conv :
    ∀ i A B t,
      Γ ⊢ t : A →
      Γ ⊢ A ≡ B →
      Γ ⊢ B : Sort i →
      Γ ⊢ t : B

where "Γ ⊢ t : A" := (typing Γ t A).

(** Context formation **)

Inductive wf : ctx → Prop :=
| wf_nil : wf ∙
| wf_cons :
    ∀ Γ i A,
      wf Γ →
      Γ ⊢ A : Sort i →
      wf (Γ ,, A).

End Typing.

Notation "Σ ;; Ξ | Γ ⊢ u ≡ v" :=
  (conversion Σ Ξ Γ u v)
  (at level 80, u, v at next level, format "Σ  ;;  Ξ  |  Γ  ⊢  u  ≡  v").

Notation "Σ ;; Ξ | Γ ⊢ t : A" :=
  (typing Σ Ξ Γ t A)
  (at level 80, t, A at next level, format "Σ  ;;  Ξ  |  Γ  ⊢  t  :  A").

(** Extension context typing **)

Inductive ewf (Σ : gctx) : ectx → Prop :=
| ewf_nil : ewf Σ []
| ewf_cons Ξ E ξ' Ξ' Δ R :
    ewf Σ Ξ →
    Σ E = Some (Ext Ξ' Δ R) →
    inst_typing_ Σ Ξ (typing Σ Ξ) ∙ ξ' Ξ' →
    ewf Σ ((E, ξ') :: Ξ).

(** Computation rule typing

  TODO: We could also have some pattern typing to make sure forced terms are
  indeed forced.

**)

Definition rule_typing Σ Ξ Δ rule :=
  let k := length rule.(cr_env) in
  Σ ;; Ξ | Δ ,,, rule.(cr_env) ⊢ plinst k rule.(cr_pat) : rule.(cr_typ) ∧
  Σ ;; Ξ | Δ ,,, rule.(cr_env) ⊢ rule.(cr_rep) : rule.(cr_typ).

(** Global environment typing **)

Inductive gwf : gctx → Prop :=
| gwf_nil : gwf []

| gwf_ext c (Σ : gctx) Ξ Δ R :
    Σ c = None → (* freshness *)
    gwf Σ →
    ewf Σ Ξ →
    wf Σ Ξ Δ →
    Forall (rule_typing Σ Ξ Δ) R →
    gwf ((c, Ext Ξ Δ R) :: Σ)

| gwf_def c (Σ : gctx) Ξ A t i :
    Σ c = None → (* freshness *)
    gwf Σ →
    ewf Σ Ξ →
    Σ ;; Ξ | ∙ ⊢ A : Sort i → (* Redundant, makes proofs easier *)
    Σ ;; Ξ | ∙ ⊢ t : A →
    gwf ((c, Def Ξ A t) :: Σ).

(** Automation **)

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

(** Util **)

Lemma meta_conv :
  ∀ Σ Ξ Γ t A B,
    Σ ;; Ξ | Γ ⊢ t : A →
    A = B →
    Σ ;; Ξ | Γ ⊢ t : B.
Proof.
  intros Σ Ξ Γ t A B h ->. assumption.
Qed.

Lemma meta_conv_trans_l :
  ∀ Σ Ξ Γ u v w,
    u = v →
    Σ ;; Ξ | Γ ⊢ v ≡ w →
    Σ ;; Ξ | Γ ⊢ u ≡ w.
Proof.
  intros Σ Ξ Γ ??? <- h. assumption.
Qed.

Lemma meta_conv_trans_r :
  ∀ Σ Ξ Γ u v w,
    Σ ;; Ξ | Γ ⊢ u ≡ v →
    v = w →
    Σ ;; Ξ | Γ ⊢ u ≡ w.
Proof.
  intros Σ Ξ Γ u v ? h <-. assumption.
Qed.

Lemma meta_conv_refl :
  ∀ Σ Ξ Γ u v,
    u = v →
    Σ ;; Ξ | Γ ⊢ u ≡ v.
Proof.
  intros Σ Ξ Γ u ? <-. ttconv.
Qed.

Notation inst_eget Σ Ξ := (inst_eget_ Σ (typing Σ Ξ)).
Notation inst_typing Σ Ξ := (inst_typing_ Σ Ξ (typing Σ Ξ)).
