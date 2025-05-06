(** Extension and pattern instantiation **)

From Stdlib Require Import Utf8 List.
From LocalComp.autosubst Require Import AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST Env.
Import ListNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

(** Extension instantiation **)

Definition eget (ξ : eargs) M x :=
  let default := Sort 0 in
  match nth_error ξ M with
  | Some σ =>
    match nth_error σ x with
    | Some t => t
    | None => default
    end
  | None => default
  end.

Notation ren_eargs ρ ξ :=
  (map (map (ren_term ρ)) ξ).

Notation lift_eargs ξ := (ren_eargs S ξ).

Notation liftn n ξ := (ren_eargs (plus n) ξ).

Fixpoint einst (ξ : eargs) (t : term) :=
  match t with
  | var n => var n
  | Sort i => Sort i
  | Pi A B => Pi (einst ξ A) (einst (lift_eargs ξ) B)
  | lam A t => lam (einst ξ A) (einst (lift_eargs ξ) t)
  | app u v => app (einst ξ u) (einst ξ v)
  | const c ξ' => const c (map (map (einst ξ)) ξ')
  | assm M x => eget ξ M x
  end.

Notation einst_eargs ξ ξ' := (map (map (einst ξ)) ξ').

(** Instance for a context **)

Fixpoint ctx_einst (ξ : eargs) (Γ : ctx) : ctx :=
  match Γ with
  | [] => []
  | A :: Γ => ctx_einst ξ Γ ,, einst (liftn (length Γ) ξ) A
  end.

(** n-ary application **)

Fixpoint apps (u : term) (l : list term) :=
  match l with
  | [] => u
  | v :: l => apps (app u v) l
  end.

(** Substitution lifting **)

Fixpoint ups n σ :=
  match n with
  | 0 => σ
  | S n => up_term (ups n σ)
  end.

(** Delocalising a term

  That is replacing all local variables x by M.x.
  In some cases, we want to do it only for certain variables, so we use [ups].

**)

Definition delocal M t :=
  t <[ assm M ].

Definition delocal_lift M k t :=
  t <[ ups k (assm M) ].

(** Rules lhs and rhs **)

Definition rule_tm M ξ δ k t :=
  delocal_lift M k (einst (liftn (δ + k) ξ) t).

Definition rule_lhs M ξ δ rule :=
  rule_tm M ξ δ (length rule.(cr_env)) (rule.(cr_pat) <[ rule.(cr_sub) ]).

Definition rule_rhs M ξ δ rule :=
  rule_tm M ξ δ (length rule.(cr_env)) rule.(cr_rep).
