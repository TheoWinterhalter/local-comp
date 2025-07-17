(** * Monads *)

From Stdlib Require Import Utf8 List Bool Setoid Morphisms Relation_Definitions
  Setoid Morphisms Relation_Definitions Relation_Operators.
From Equations Require Import Equations.

Import ListNotations.

Set Default Goal Selector "!".
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Typeclasses Default Mode "!".
Hint Constants Opaque : typeclass_instances.

Class Monad (M : Type → Type) := {
  ret : ∀ A, A → M A ;
  bind : ∀ A B, M A → (A → M B) → M B
}.

Arguments ret {M _ A}.
Arguments bind {M _ A B}.

Definition fmap {M} `{Monad M} {A B} (f : A → B) (m : M A) : M B :=
  bind m (λ x, ret (f x)).

Definition ap {M} `{Monad M} {A B} (f : M (A → B)) (c : M A) : M B :=
  bind f (λ g, bind c (λ x, ret (g x))).

Module MonadNotations.

  Declare Scope monad_scope.
  Delimit Scope monad_scope with monad.

  Open Scope monad_scope.

  Notation "c >>= f" :=
    (bind c f)
    (at level 50, left associativity) : monad_scope.

  Notation "x ← e `; f" :=
    (bind e (λ x, f))
    (at level 100, e at next level, right associativity)
    : monad_scope.

  Notation "' pat ← e `; f" :=
    (bind e (λ pat, f))
    (at level 100, e at next level, right associativity, pat pattern)
    : monad_scope.

  Notation "e `; f" :=
    (bind e (λ _, f))
    (at level 100, right associativity)
    : monad_scope.

  Notation "f '<*>' m" :=
    (fmap f m)
    (at level 50, left associativity)
    : monad_scope.

  Notation "f '<@>' m" :=
    (ap f m)
    (at level 50, left associativity)
    : monad_scope.

End MonadNotations.

(** * State monad *)

Definition St state A := state → state * A.

Definition retSt {st A} (a : A) : St st A :=
  λ s, (s, a).

Definition bindSt {st A B} (a : St st A) (f : A → St st B) : St st B :=
  λ s, let (s', x) := a s in f x s'.

#[export] Instance MonadSt st : Monad (St st) := {|
  ret A x := retSt x ;
  bind A B c f := bindSt c f
|}.

Definition runSt {st A} (s : st) (a : St st A) : A :=
  snd (a s).

Definition getSt {st} : St st st :=
  λ s, (s,s).

Definition putSt {st} (s : st) : St st unit :=
  λ _, (s, tt).

(** * Exception monad *)

Definition Exn A := option A.

Definition retExn {A} (a : A) : Exn A :=
  Some a.

Definition bindExn {A B} (a : Exn A) (f : A → Exn B) : Exn B :=
  match a with
  | Some x => f x
  | None => None
  end.

#[export] Instance MonadExn : Monad Exn := {|
  ret A x := retExn x ;
  bind A B c f := bindExn c f
|}.

Definition fail {A} : Exn A :=
  None.
