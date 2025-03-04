(** Notations for substitutions and renamings

  They replace those of Autosubst that are incompatible with list notation.

**)

From Coq Require Import Utf8 List.
From LocalComp.autosubst Require Import core unscoped RAsimpl AST.
From Coq Require Import Setoid Morphisms Relation_Definitions.

#[global] Disable Notation "[ sigma_term ]" : fscope.
#[global] Disable Notation "s [ sigma_term ]" : subst_scope.
#[global] Disable Notation "'var'" : subst_scope.

Import ListNotations.

Notation "a ⋅ x" :=
  (ren_term a x) (at level 20, right associativity) : subst_scope.

Notation "t <[ s ]" :=
  (subst_term s t) (at level 10, right associativity) : subst_scope.

Notation "↑" := (shift) : subst_scope.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.

Ltac autosubst_unfold :=
  unfold Ren_term, upRen_term_term, Subst_term, VarInstance_term.

Ltac resubst :=
  rewrite ?renRen_term, ?renSubst_term, ?substRen_term, ?substSubst_term.

Ltac ssimpl :=
  asimpl ;
  autosubst_unfold ;
  asimpl ;
  repeat unfold_funcomp ;
  resubst ;
  asimpl ;
  repeat unfold_funcomp.
