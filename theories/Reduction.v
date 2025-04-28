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
  GScope.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

Section Red.

  Reserved Notation "Γ ⊢ u ↦ v"
    (at level 80, u, v at next level).

  Context (Σ : gctx) (Ξ : ectx).

  Inductive red1 (Γ : ctx) : term → term → Prop :=
  | red_beta A t u : Γ ⊢ app (lam A t) u ↦ t <[ u .. ]

  | red_unfold c ξ Ξ' A t :
      Σ c = Some (Def Ξ' A t) →
      (* inst_equations_ conversion Γ ξ Ξ' → *)
      (* closed t = true → *)
      Γ ⊢ const c ξ ↦ einst ξ t

(*   | conv_red E Ξ' Δ R M ξ' n rule σ :
      Σ E = Some (Ext Ξ' Δ R) →
      ectx_get Ξ M = Some (E, ξ') →
      nth_error R n = Some rule →
      let δ := length Δ in
      (* TODO Need linear version without forced terms *)
      (* let lhs := rule_lhs M ξ' δ rule in
      let rhs := rule_rhs M ξ' δ rule in *)
      let k := length rule.(cr_env) in
      scoped k lhs = true →
      scoped k rhs = true →
      Γ ⊢ lhs <[ σ ] ↦ rhs <[ σ ] *)

  where "Γ ⊢ u ↦ v" := (red1 Γ u v).

End Red.
