(** Typing **)

From Coq Require Import Utf8 List Arith Bool.
From LocalComp.autosubst Require Import AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst.
Import ListNotations.

Open Scope subst_scope.

(** Closedness property **)

Fixpoint scoped n t :=
  match t with
  | var m => m <=? n
  | Sort _ => true
  | Pi A B => scoped n A && scoped (S n) B
  | lam A t => scoped n A && scoped (S n) t
  | app u v => scoped n u && scoped n v
  | const c ξ => forallb (forallb (scoped n)) ξ
  | assm M x => true
  end.

Notation closed t := (scoped 0 t).

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
      (* TODO: Add conversion for ξ, similar to its typing
        Could/should we implement those as actual substitutions?
        Would that make some things easier? Like no need to do the einst thing
        which has to lift manually in the end.
      *)
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

(** Instance typing (relative to typing for now) **)
Section Inst.

  Context (typing : ctx → term → term → Prop).

  Notation "Γ ⊢ u : A" := (typing Γ u A).

  Inductive typings Γ : list term → ctx → Prop :=
  | type_nil : typings Γ [] ∙
  | type_cons Δ σ t A :
      typings Γ σ Δ →
      Γ ⊢ t : A → (* TODO Missing substitution *)
      typings Γ (t :: σ) (Δ ,, A).

  Inductive inst_typing Γ : eargs → ectx → Prop :=
  | inst_nil : inst_typing Γ [] []
  | inst_cons σ ξ E ξ' Ξ' Ξ'' Δ R :
      nth_error Σ E = Some (Ext Ξ'' Δ R) →
      inst_typing Γ ξ Ξ' →
      (* TODO: Do we need to check ξ' : Ξ''? *)
      (* TODO: Typing for σ needs subst by ξ and ξ' *)
      typings Γ σ Δ →
      (* TODO: verification of equations *)
      inst_typing Γ (σ :: ξ) ((E,ξ') :: Ξ').

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
      inst_typing typing Γ ξ Ξ' →
      Γ ⊢ const c ξ : A (* TODO: Subst *)

| type_assm :
    ∀ M x E ξ Ξ' Δ R A,
      nth_error Ξ M = Some (E, ξ) →
      nth_error Σ E = Some (Ext Ξ' Δ R) →
      nth_error Δ x = Some A →
      Γ ⊢ assm M x : A (* TODO: Subst *)

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

(* TODO: Environment typing *)

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
