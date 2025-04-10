From Stdlib Require Import Utf8 List Bool Setoid Morphisms Relation_Definitions.
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

Lemma Forall2_diag A (R : A → A → Prop) l :
  Forall (λ x, R x x) l →
  Forall2 R l l.
Proof.
  intros h. induction h.
  - constructor.
  - constructor. all: assumption.
Qed.

Lemma Forall2_nth_error_l A B (R : A → B → Prop) l1 l2 n a :
  Forall2 R l1 l2 →
  nth_error l1 n = Some a →
  ∃ b, nth_error l2 n = Some b ∧ R a b.
Proof.
  intros h e.
  induction h as [| x y l1 l2 hab h ih] in n, a, e |- *.
  - destruct n. all: discriminate.
  - destruct n as [| n].
    + cbn in e. inversion e. subst. clear e.
      cbn. eexists. intuition eauto.
    + cbn in e. eapply ih in e as (b & e1 & e2).
      eexists. intuition eauto.
Qed.

(** [option] util **)

Definition onSome [A] (P : A → Prop) (o : option A) : Prop :=
  match o with
  | Some a => P a
  | None => True
  end.

Lemma onSome_map A B f P o :
  onSome P (@option_map A B f o) ↔ onSome (λ a, P (f a)) o.
Proof.
  destruct o as [x|].
  - cbn. reflexivity.
  - cbn. reflexivity.
Qed.

#[export] Instance onSome_morphism A :
  Proper (pointwise_relation _ iff ==> eq ==> iff) (@onSome A).
Proof.
  intros P Q hPQ o ? <-.
  destruct o.
  - cbn. apply hPQ.
  - cbn. reflexivity.
Qed.

(** [fold_left] util **)

Lemma fold_left_map A B C (f : A → B → A) l a g :
  fold_left f (map g l) a = fold_left (λ a (c : C), f a (g c)) l a.
Proof.
  induction l as [| x l ih] in a |- *.
  - cbn. reflexivity.
  - cbn. apply ih.
Qed.

Lemma fold_left_ind A B (f : A → B → A) l a P :
  P a →
  (∀ a b, P a → P (f a b)) →
  P (fold_left f l a).
Proof.
  intros ha h.
  induction l as [| x l ih] in a, ha |- *.
  - cbn. assumption.
  - cbn. eapply ih. eapply h. assumption.
Qed.

Lemma fold_left_ext A B (f g : A → B → A) l a :
  (∀ x, f x = g x) →
  fold_left f l a = fold_left g l a.
Proof.
  intros h.
  induction l as [| x l ih] in a |- *.
  - reflexivity.
  - cbn. rewrite ih. rewrite h. reflexivity.
Qed.
