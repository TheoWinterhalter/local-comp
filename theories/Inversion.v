(** Inversion of typing *)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

From Equations Require Import Equations.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Derive NoConfusion NoConfusionHom for list.
Derive NoConfusion NoConfusionHom for term.
Derive Signature for typing.

Require Import Equations.Prop.DepElim.

Ltac destruct_exists h :=
  match type of h with
  | ∃ _, _ => destruct h as [? h] ; destruct_exists h
  | _ => idtac
  end.

Ltac destruct_all_exists :=
  repeat
  match goal with
  | h : ∃ _, _ |- _ => destruct h
  end.

#[local] Ltac do_eexists :=
  lazymatch goal with
  | |- ∃ _, _ => eexists
  end.

#[local] Ltac invtac h :=
  dependent induction h ; [
    repeat do_eexists ; intuition eauto ; apply conv_refl
  | destruct_all_exists ; repeat do_eexists ; intuition eauto ;
    eapply conv_trans ; eauto
  ].

Lemma type_var_inv Σ Ξ Γ x A :
  Σ ;; Ξ | Γ ⊢ var x : A →
  ∃ B,
    nth_error Γ x = Some B ∧
    Σ ;; Ξ ⊢ (plus (S x)) ⋅ B ≡ A.
Proof.
  intros h. invtac h.
Qed.

Lemma type_sort_inv Σ Ξ Γ i A :
  Σ ;; Ξ | Γ ⊢ Sort i : A →
  Σ ;; Ξ ⊢ Sort (S i) ≡ A.
Proof.
  intros h. invtac h.
Qed.

Lemma type_pi_inv Σ Ξ Γ A B T :
  Σ ;; Ξ | Γ ⊢ Pi A B : T →
  ∃ i j,
    Σ ;; Ξ | Γ ⊢ A : Sort i ∧
    Σ ;; Ξ | Γ ,, A ⊢ B : Sort j ∧
    Σ ;; Ξ ⊢ Sort (max i j) ≡ T.
Proof.
  intros h. invtac h.
Qed.

Lemma type_lam_inv Σ Ξ Γ A t T :
  Σ ;; Ξ | Γ ⊢ lam A t : T →
  ∃ i j B,
    Σ ;; Ξ | Γ ⊢ A : Sort i ∧
    Σ ;; Ξ | Γ ,, A ⊢ B : Sort j ∧
    Σ ;; Ξ | Γ ,, A ⊢ t : B ∧
    Σ ;; Ξ ⊢ Pi A B ≡ T.
Proof.
  intros h. invtac h.
Qed.

Lemma type_app_inv Σ Ξ Γ u v T :
  Σ ;; Ξ | Γ ⊢ app u v : T →
  ∃ i j A B,
    Σ ;; Ξ | Γ ⊢ u : Pi A B ∧
    Σ ;; Ξ | Γ ⊢ v : A ∧
    Σ ;; Ξ | Γ ⊢ A : Sort i ∧
    Σ ;; Ξ | Γ ,, A ⊢ B : Sort j ∧
    Σ ;; Ξ ⊢ B <[ v .. ] ≡ T.
Proof.
  intros h. invtac h.
Qed.

Lemma type_const_inv Σ Ξ Γ c ξ T :
  Σ ;; Ξ | Γ ⊢ const c ξ : T →
  ∃ Ξ' A t,
    Σ c = Some (Def Ξ' A t) ∧
    inst_typing Σ Ξ Γ ξ Ξ' ∧
    closed A = true ∧
    Σ ;; Ξ ⊢ inst ξ A ≡ T.
Proof.
  intros h. invtac h.
Qed.

Lemma type_assm_inv Σ Ξ Γ x T :
  Σ ;; Ξ | Γ ⊢ assm x : T →
  ∃ A,
    ictx_get Ξ x = Some (Assm A) ∧
    closed A = true ∧
    Σ ;; Ξ ⊢ A ≡ T.
Proof.
  intros h. invtac h.
Qed.

Ltac ttinv h h' :=
  lazymatch type of h with
  | _ ;; _ | _ ⊢ ?t : _ =>
    lazymatch t with
    | var _ => eapply type_var_inv in h as h'
    | Sort _ => eapply type_sort_inv in h as h'
    | Pi _ _ => eapply type_pi_inv in h as h'
    | lam _ _ => eapply type_lam_inv in h as h'
    | app _ _ => eapply type_app_inv in h as h'
    | const _ _ => eapply type_const_inv in h as h'
    | assm _ => eapply type_assm_inv in h as h'
    end
  end.
