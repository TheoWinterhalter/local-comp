(** * Interface instantiation *)

From Stdlib Require Import Utf8 List.
From LocalComp.autosubst Require Import AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST Env.
Import ListNotations.

Set Default Goal Selector "!".

Open Scope subst_scope.

Definition dummy := (Sort 0).

Definition iget (ξ : instance) x :=
  match nth_error ξ x with
  | Some (Some t) => t
  | _ => dummy
  end.

Notation map_instance f ξ :=
  (map (option_map f) ξ).

Notation ren_instance ρ ξ :=
  (map_instance (ren_term ρ) ξ).

Notation lift_instance ξ := (ren_instance S ξ).

Notation liftn n ξ := (ren_instance (plus n) ξ).

Fixpoint inst (ξ : instance) (t : term) :=
  match t with
  | var n => var n
  | Sort i => Sort i
  | Pi A B => Pi (inst ξ A) (inst (lift_instance ξ) B)
  | lam A t => lam (inst ξ A) (inst (lift_instance ξ) t)
  | app u v => app (inst ξ u) (inst ξ v)
  | const c ξ' => const c (map_instance (inst ξ) ξ')
  | assm x => iget ξ x
  end.

Notation inst_instance ξ ξ' := (map_instance (inst ξ) ξ').

(** Instance for a context *)

Fixpoint ctx_inst (ξ : instance) (Γ : ctx) : ctx :=
  match Γ with
  | [] => []
  | A :: Γ => ctx_inst ξ Γ ,, inst (liftn (length Γ) ξ) A
  end.

(** ** Unrelated utility

  TODO MOVE

*)

(** n-ary application *)

Fixpoint apps (u : term) (l : list term) :=
  match l with
  | [] => u
  | v :: l => apps (app u v) l
  end.

(** Substitution lifting *)

Fixpoint ups n σ :=
  match n with
  | 0 => σ
  | S n => up_term (ups n σ)
  end.
