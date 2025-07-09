(** * Environments

  We have three kinds of environments:
  - Σ the global signature, containing definitions and interfaces.
  - Ξ the extension environment.
  - Γ the local environment.

*)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import AST SubstNotations RAsimpl AST_rasimpl.
From LocalComp Require Import Util BasicAST.

Import ListNotations.

(** Local environment, a list of types *)
Definition ctx := list term.

(** ** Custom computation rule

  We consider them as definitional equalities which might be nonlinear.
  For implementation purposes however, it's better to have a linear version
  (as well as pattern syntax) so we consider the left-hand side as the result of
  applying a "forcing" substitution.

  To make the inlining proof easier and more general, we will consider an
  equation proxy where the substitution is already applied.

  Fields are
  - [cr_env]: the environment of the rule [Θ]
  - [cr_pat]: the "pattern" for the left-hand side [p]
  - [cr_sub]: the "forcing" substitution [ρ] to go from [p] to the actual lhs
  - [cr_rep]: the replacing term [r]
  - [cr_typ]: the type for both sides [A]

  This represents the following (typed) definitional equality:
  [Θ ⊢ l <[ρ] ≡ r : A]

*)
Record crule := {
  cr_env : ctx ;
  cr_pat : term ;
  cr_sub : nat → term ;
  cr_rep : term ;
  cr_typ : term
}.

Record equation := {
  eq_env : ctx ;
  eq_lhs : term ;
  eq_rhs : term ;
  eq_typ : term
}.

Definition crule_eq rule : equation := {|
  eq_env := rule.(cr_env) ;
  (* eq_lhs := rule.(cr_pat) <[ rule.(cr_sub) ] ; *)
  eq_lhs := subst_term rule.(cr_sub) rule.(cr_pat) ;
  eq_rhs := rule.(cr_rep) ;
  eq_typ := rule.(cr_typ)
|}.

(** Interface declaration

  An interface interleaves assumptions (or symbols) and computation rules.

*)
Inductive idecl :=
| Assm (A : term)
| Comp (rl : crule).

Derive NoConfusion for idecl.

(** Interface *)
Definition ictx := list idecl.

(** Instances

  It is given by a list of terms corresponding to assumptions of an interface.
  Because an interface also contains rules, we opt for the use of [None] in
  the corresponding positions.

  Maybe an association list would make more sense.

*)
Definition instance := list (option term).

(** Access in an interface

  This is special because we use de Bruijn levels so we need to perform some
  simple arithmetic. We also avoid returning [Some] for de Bruijn levels that go
  too far.

*)

Definition lvl_get [A] (l : list A) (x : aref) :=
  nth_error (rev l) x.

Notation ictx_get Ξ x := (lvl_get (A := idecl) Ξ x).

Lemma lvl_get_weak [A] d l n a :
  lvl_get (A := A) l n = Some a →
  lvl_get (d :: l) n = Some a.
Proof.
  unfold lvl_get. cbn.
  intro.
  rewrite nth_error_app1; auto.
  apply nth_error_Some. intros e; rewrite e in H; discriminate.
Qed.

Lemma lvl_get_last [A] (a : A) l :
  lvl_get (a :: l) (length l) = Some a.
Proof.
  unfold lvl_get. cbn.
  rewrite nth_error_app2, length_rev, Nat.sub_diag; auto.
  rewrite length_rev. auto.
Qed.

Lemma lvl_get_length A (l : list A) x a :
  lvl_get l x = Some a →
  x < length l.
Proof.
  intros h.
  unfold lvl_get in h.
  rewrite <- length_rev.
  apply nth_error_Some.
  rewrite h. intro. easy.
Qed.

Lemma lvl_get_In [A] l n a :
  lvl_get (A := A) l n = Some a →
  In a l.
Proof.
  intros e.
  unfold lvl_get in e.
  apply In_rev.
  eapply nth_error_In. eassumption.
Qed.

(** Global declaration *)
Inductive gdecl :=
| Def (Ξ : ictx) (A : term) (t : term).

Definition gctx : Type := list (gref * gdecl).

Fixpoint gctx_get (Σ : gctx) (c : gref) : option gdecl :=
  match Σ with
  | [] => None
  | (k,d) :: Σ => if (c =? k)%string then Some d else gctx_get Σ c
  end.

Coercion gctx_get : gctx >-> Funclass.

Definition extends (Σ Σ' : gctx) :=
  ∀ r d,
    Σ r = Some d →
    Σ' r = Some d.

Notation "a ⊑ b" := (extends a b) (at level 70, b at next level).

(** ** Notations *)

Notation "'∙'" :=
  (@nil term).

Notation "Γ ,, d" :=
  (@cons term d Γ) (at level 20, d at next level).

Notation "Γ ,,, Δ" :=
  (@List.app term Δ Γ) (at level 25, Δ at next level, left associativity).
