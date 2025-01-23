(** Extension and pattern instantiation **)

From Coq Require Import Utf8 List.
From LocalComp.autosubst Require Import AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST Env.
Import ListNotations.

(** Extension instantiation **)

Definition eget (ξ : eargs) M x :=
  let default := assm M x in (* Could also be a dummy *)
  match nth_error ξ M with
  | Some σ =>
    match nth_error σ x with
    | Some t => t
    | None => default
    end
  | None => default
  end.

Definition ren_eargs ρ (ξ : eargs) : eargs :=
  map (map (ren_term ρ)) ξ.

Notation lift_eargs ξ := (ren_eargs S ξ).

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

(** n-ary application **)

Fixpoint apps (u : term) (l : list term) :=
  match l with
  | [] => u
  | v :: l => apps (app u v) l
  end.

(** Pattern linear instantiation **)

Definition plinst_args (plinst_arg : parg → nat → term * nat) (l : list parg) n :=
  fold_left (λ '(acc, k) p,
    let '(t,m) := plinst_arg p k in (t :: acc, m)
  ) l ([], n).

Fixpoint plinst_arg M (p : parg) n : term * nat :=
  match p with
  | pvar => (var n, S n)
  | pforce t => (t, n)
  | psymb x l =>
      let '(l', m) := plinst_args (plinst_arg M) l n in
      (apps (assm M x) (rev l'), m)
  end.

Definition plinst M (p : pat) : term :=
  let '(l,_) := plinst_args (plinst_arg M) p.(pat_args) 0 in
  apps (assm M p.(pat_head)) l.
