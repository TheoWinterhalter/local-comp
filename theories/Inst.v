(** Extension instantiation **)

From Coq Require Import Utf8 List.
From LocalComp.autosubst Require Import AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST Env.
Import ListNotations.

(**

  The argument [t] of [einst ξ t] is expected to be closed.
  This is the reason why we use a dummy value for variables, this way we don't
  need to worry about the function being partial.
  Thanks to this, we also don't need to worry about lifting [ξ] when going under
  binders.

**)

Definition dummy := Sort 0.

Fixpoint einst (ξ : eargs) (t : term) :=
  match t with
  | var n => dummy
  | Sort i => Sort i
  | Pi A B => Pi (einst ξ A) (einst ξ B)
  | lam A t => lam (einst ξ A) (einst ξ t)
  | app u v => app (einst ξ u) (einst ξ v)
  | const c ξ' => const c (map (map (einst ξ)) ξ')
  | assm M x => assm M x
  end.
