(** Extension instantiation **)

From Coq Require Import Utf8 List.
From LocalComp.autosubst Require Import AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST Env.
Import ListNotations.

Fixpoint einst (ξ : eargs) (t : term) :=
  match t with
  | var n => var n
  | Sort i => Sort i
  | Pi A B => Pi (einst ξ A) (einst ξ B)
  | lam A t => lam (einst ξ A) (einst ξ t)
  | app u v => app (einst ξ u) (einst ξ v)
  | const c ξ' => const c (map (map (einst ξ)) ξ')
  | assm M x => assm M x
  end.
