From Stdlib Require Import Utf8 List Bool.
From Equations Require Import Equations.

Import ListNotations.

Set Default Goal Selector "!".

Notation "'∑' x .. y , p" := (sigT (λ x, .. (sigT (λ y, p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Ltac forward_gen h tac :=
  match type of h with
  | ?P → _ =>
    let h' := fresh in
    assert (h' : P) ; [ tac | specialize (h h') ; clear h' ]
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Create HintDb shelvedb.

Hint Extern 10000 => shelve : shelvedb.

Ltac forall_iff_impl T :=
  lazymatch eval cbn beta in T with
  | forall x : ?A, @?T' x =>
    let y := fresh x in
    refine (forall y, _) ;
    forall_iff_impl (@T' x)
  | ?P ↔ ?Q => exact (P → Q)
  | _ => fail "not a quantified ↔"
  end.

Ltac wlog_iff_using tac :=
  lazymatch goal with
  | |- ?G =>
    let G' := fresh in
    unshelve refine (let G' : Prop := _ in _) ; [ forall_iff_impl G |] ;
    let h := fresh in
    assert (h : G') ; [
      subst G'
    | subst G' ; intros ; split ; eauto ; apply h ; clear h ; tac
    ]
  end.

Ltac wlog_iff :=
  wlog_iff_using firstorder.

Inductive All {A} (P : A → Type) : list A → Type :=
| All_nil : All P []
| All_cons a l : P a → All P l → All P (a :: l).

Lemma All_Forall :
  ∀ A (P : A → Prop) l,
    All P l →
    Forall P l.
Proof.
  intros A P l h.
  induction h. all: eauto.
Qed.

Lemma map_ext_All :
  ∀ A B (f g : A → B) l,
    All (λ x, f x = g x) l →
    map f l = map g l.
Proof.
  intros A B f g l h.
  apply map_ext_Forall. apply All_Forall. assumption.
Qed.

Lemma All_impl A (P Q : A → Type) l :
  (∀ a, P a → Q a) →
  All P l →
  All Q l.
Proof.
  intros hPQ hP.
  induction hP. all: constructor ; eauto.
Qed.

Lemma forallb_All :
  ∀ A p l,
    @forallb A p l = true →
    All (λ x, p x = true) l.
Proof.
  intros A p l h.
  induction l as [| a l ih]. 1: constructor.
  cbn in h. apply andb_prop in h as [].
  constructor. all: auto.
Qed.

Lemma All_forallb A (p : A → bool) l :
  All (λ x, p x = true) l →
  forallb p l = true.
Proof.
  intro h. induction h.
  - reflexivity.
  - cbn. eauto using andb_true_intro.
Qed.

Lemma All_prod :
  ∀ A P Q l,
    All (A := A) P l →
    All Q l →
    All (λ a, P a * Q a)%type l.
Proof.
  intros A P Q l hP hQ.
  induction hP. 1: constructor.
  inversion hQ. subst.
  constructor. all: eauto.
Qed.

Lemma All_map A B (f : A → B) P l :
  All (λ x, P (f x)) l →
  All P (map f l).
Proof.
  intro h. induction h.
  - constructor.
  - cbn. constructor. all: auto.
Qed.

Lemma Forall2_map_l :
  ∀ A B C (f : A → B) R l (l' : list C),
    Forall2 R (map f l) l' ↔ Forall2 (λ x y, R (f x) y) l l'.
Proof.
  intros A B C f R l l'.
  split.
  - intro h. remember (map f l) as l'' eqn: e.
    induction h in l, e |- *.
    + destruct l. 2: discriminate.
      constructor.
    + destruct l. 1: discriminate.
      inversion e. subst.
      constructor. all: auto.
  - intro h. induction h. 1: constructor.
    cbn. constructor. all: auto.
Qed.

Lemma Forall2_map_r :
  ∀ A B C (f : A → B) R (l : list C) l',
    Forall2 R l (map f l') ↔ Forall2 (λ x y, R x (f y)) l l'.
Proof.
  intros A B C f R l l'.
  split.
  - intro h. apply Forall2_flip in h. rewrite Forall2_map_l in h.
    apply Forall2_flip. assumption.
  - intro h. apply Forall2_flip in h.
    apply Forall2_flip. rewrite Forall2_map_l. assumption.
Qed.

(** [option] util **)

Definition onSome [A] (P : A → Prop) (o : option A) : Prop :=
  match o with
  | Some a => P a
  | None => True
  end.
