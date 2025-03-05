(** Typing **)

From Coq Require Import Utf8 List Arith Bool.
From LocalComp.autosubst
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst.
From Coq Require Import Setoid Morphisms Relation_Definitions.

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
      nth_error Σ c = Some (Def Ξ' A t) →
      closed t = true →
      Γ ⊢ const c ξ ≡ einst ξ t

| conv_red :
    ∀ E Ξ' Δ R M ξ' n rule σ,
      nth_error Σ E = Some (Ext Ξ' Δ R) →
      nth_error Ξ M = Some (E, ξ') →
      nth_error R n = Some rule →
      Γ ⊢ (plinst M rule.(cr_pat)) <[ σ ] ≡ (delocal M rule.(cr_rep)) <[ σ ]

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

Fixpoint ups n σ :=
  match n with
  | 0 => σ
  | S n => up_term (ups n σ)
  end.

(** Instance typing (relative to typing for now) **)
Section Inst.

  Context (typing : ctx → term → term → Prop).

  Notation "Γ ⊢ u : A" := (typing Γ u A).

  (** Substitution typing **)
  Inductive styping_ (Γ : ctx) (σ : nat → term) : ctx → Prop :=
  | type_nil : styping_ Γ σ ∙
  | type_cons Δ A :
      styping_ Γ (S >> σ) Δ →
      Γ ⊢ σ 0 : A <[ S >> σ ] →
      styping_ Γ σ (Δ ,, A).

  Definition inst_equations (Γ : ctx) (ξ : eargs) (Ξ' : ectx) :=
    ∀ E Ξ'' Δ R M ξ' σ n rule,
      nth_error Σ E = Some (Ext Ξ'' Δ R) →
      nth_error Ξ' M = Some (E, ξ') →
      nth_error ξ M = Some σ →
      nth_error R n = Some rule →
      let m := length rule.(cr_env) in
      let θ := ups m (slist σ) in
      let Θ := ctx_einst ξ (ctx_einst ξ' rule.(cr_env)) in
      let lhs := (einst ξ (einst ξ' (plinst M rule.(cr_pat)))) <[ θ ] in
      let rhs := (einst ξ (einst ξ' (delocal M rule.(cr_rep)))) <[ θ ] in
      Γ ,,, Θ ⊢ lhs ≡ rhs.

  Definition inst_typing_ (Γ : ctx) (ξ : eargs) (Ξ' : ectx) :=
    ∀ M x E ξ' Ξ'' Δ R A,
      nth_error Ξ' M = Some (E, ξ') →
      nth_error Σ E = Some (Ext Ξ'' Δ R) →
      nth_error Δ x = Some A →
      Γ ⊢ eget ξ M x : einst ξ (einst ξ' (delocal M A)).

  (* Inductive inst_typing Γ : eargs → ectx → Prop :=
  | inst_nil : inst_typing Γ [] []
  | inst_cons σ ξ E ξ' Ξ' Ξ'' Δ R :
      nth_error Σ E = Some (Ext Ξ'' Δ R) →
      inst_typing Γ ξ Ξ' →
      (* TODO: Do we need to check Ξ' ⊢ ξ' : Ξ''? *)
      styping_ Γ (slist σ) (ctx_einst ξ (ctx_einst ξ' Δ)) →
      inst_equations Γ E (slist σ) R ξ ξ' →
      inst_typing Γ (σ :: ξ) ((E,ξ') :: Ξ'). *)

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
      nth_error Σ c = Some (Def Ξ' A t) →
      inst_typing_ typing Γ ξ Ξ' →
      closed A = true →
      Γ ⊢ const c ξ : einst ξ A

| type_assm :
    ∀ M x E ξ Ξ' Δ R A,
      nth_error Ξ M = Some (E, ξ) →
      nth_error Σ E = Some (Ext Ξ' Δ R) →
      nth_error Δ x = Some A →
      closed_eargs ξ = true →
      Γ ⊢ assm M x : einst ξ (delocal M A)

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
    nth_error Σ E = Some (Ext Ξ' Δ R) →
    inst_typing_ Σ (typing Σ Ξ) ∙ ξ' Ξ' →
    ewf Σ ((E, ξ') :: Ξ).

(** Global environment typing **)

Inductive gwf : gctx → Prop :=
| gwf_nil : gwf []

| gwf_ext Σ Ξ Δ R :
    gwf Σ →
    ewf Σ Ξ →
    wf Σ Ξ Δ →
    (* TODO Something about R that ensures all typed instances factor through *)
    gwf (Ext Ξ Δ R :: Σ)

| gwf_def Σ Ξ A t :
    gwf Σ →
    ewf Σ Ξ →
    Σ ;; Ξ | ∙ ⊢ t : A →
    gwf (Def Ξ A t :: Σ).

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

Notation styping Σ Ξ := (styping_ (typing Σ Ξ)).
Notation inst_typing Σ Ξ := (inst_typing_ Σ (typing Σ Ξ)).

#[export] Instance styping_morphism Σ Ξ :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) (styping Σ Ξ).
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| ? ? ? ? ih ? ] in σ', e |- *.
  - constructor.
  - constructor.
    + apply ih. intros n. apply e.
    + rewrite <- e. assumption.
Qed.

Lemma autosubst_simpl_styping :
  ∀ Σ Ξ Γ Δ r s,
    SubstSimplification r s →
    styping Σ Ξ Γ r Δ ↔ styping Σ Ξ Γ s Δ.
Proof.
  intros Σ Ξ Γ Δ r s H.
  apply styping_morphism. 1,3: reflexivity.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_styping : rasimpl_outermost.

Lemma styping_and P Q Γ σ Δ :
  styping_ P Γ σ Δ →
  styping_ Q Γ σ Δ →
  styping_ (λ Θ t A, P Θ t A ∧ Q Θ t A) Γ σ Δ.
Proof.
  intros h1 h2.
  induction h1. 1: constructor.
  inversion h2. subst.
  constructor. all: eauto.
Qed.

Lemma styping_impl P Q Γ σ Δ :
  styping_ P Γ σ Δ →
  (∀ Θ t A, P Θ t A → Q Θ t A) →
  styping_ Q Γ σ Δ.
Proof.
  intros h hi.
  induction h. 1: constructor.
  constructor. 1: assumption.
  eauto.
Qed.
