From Stdlib Require Import Utf8 List Bool Setoid Morphisms Relation_Definitions
  Setoid Morphisms Relation_Definitions Relation_Operators.
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

(** Relations *)

Lemma rt_step_ind A B R R' f x y :
  (∀ x y, R x y → clos_refl_trans B R' (f x) (f y)) →
  clos_refl_trans A R x y →
  clos_refl_trans B R' (f x) (f y).
Proof.
  intros hstep h.
  induction h.
  - eauto.
  - apply rt_refl.
  - eapply rt_trans. all: eassumption.
Qed.

Lemma rst_step_ind A B R R' f x y :
  (∀ x y, R x y → clos_refl_sym_trans B R' (f x) (f y)) →
  clos_refl_sym_trans A R x y →
  clos_refl_sym_trans B R' (f x) (f y).
Proof.
  intros hstep h.
  induction h.
  - eauto.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans. all: eassumption.
Qed.

Lemma clos_refl_sym_trans_incl A R R' :
  inclusion A R R' →
  inclusion A (clos_refl_sym_trans A R) (clos_refl_sym_trans A R').
Proof.
  intros hR x y h.
  eapply rst_step_ind with (f := λ x, x). 2: eassumption.
  intros. apply rst_step. eauto.
Qed.

Lemma clos_refl_trans_incl A R R' :
  inclusion A R R' →
  inclusion A (clos_refl_trans A R) (clos_refl_trans A R').
Proof.
  intros hR x y h.
  eapply rt_step_ind with (f := λ x, x). 2: eassumption.
  intros. apply rt_step. eauto.
Qed.

#[export] Instance Reflexive_eta A (R : relation A) :
  Reflexive R →
  Reflexive (λ x y, R x y).
Proof.
  auto.
Qed.

(** [Forall] util *)

Lemma Forall_funct A (P Q : A → Prop) l :
  Forall P l →
  Forall (λ x, P x → Q x) l →
  Forall Q l.
Proof.
  intros h hi.
  rewrite Forall_forall in *.
  eauto.
Qed.

(** [All] predicate *)

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

Lemma forall_All A (P : A → Type) l :
  (forall x, In x l → P x) →
  All P l.
Proof.
  intros h.
  induction l as [| x l ih].
  - constructor.
  - econstructor.
    + eapply h. cbn. auto.
    + eapply ih. intros y hy.
      eapply h. cbn. auto.
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

#[export] Instance Reflexive_Forall2 A (R : relation A) :
  Reflexive R →
  Reflexive (Forall2 R).
Proof.
  intros hrefl. intros l.
  apply Forall2_diag. rewrite Forall_forall. auto.
Qed.

Lemma Forall2_trans A B C P R a b c :
  @Forall2 C A P c a →
  @Forall2 C B R c b →
  Forall2 (λ x y, ∃ z, P z x ∧ R z y) a b.
Proof.
  intros ha hb.
  induction ha in b, hb |- *.
  - inversion hb. constructor.
  - inversion hb. subst.
    constructor.
    + eexists. intuition eauto.
    + eauto.
Qed.

Lemma Forall2_trans_inv A B C P R a b :
  Forall2 (λ x y, ∃ z, P z x ∧ R z y) a b →
  ∃ c, @Forall2 C A P c a ∧ @Forall2 C B R c b.
Proof.
  intros h. induction h as [| x y l l' hxy hl ih].
  - eexists. intuition constructor.
  - destruct hxy as (?&?&?), ih as (?&?&?).
    eexists. intuition econstructor. all: eauto.
Qed.

Lemma Forall2_eq A u v :
  @Forall2 A A eq u v →
  u = v.
Proof.
  induction 1. all: subst ; eauto.
Qed.

Fixpoint rForall [A] (P : A → Prop) l :=
  match l with
  | [] => True
  | x :: l => P x ∧ rForall P l
  end.

Lemma rForall_Forall A P l :
  @rForall A P l ↔ Forall P l.
Proof.
  split.
  - intros h. induction l.
    + constructor.
    + cbn in h. econstructor ; intuition eauto.
  - intros h. induction h. all: cbn.
    + constructor.
    + intuition eauto.
Qed.

(** [OnOne2] predicate *)

Inductive OnOne2 {A} (R : A → A → Prop) : list A → list A → Prop :=
| OnOne2_hd a a' l : R a a' → OnOne2 R (a :: l) (a' :: l)
| OnOne2_tl a l l' : OnOne2 R l l' → OnOne2 R (a :: l) (a :: l').

Lemma OnOne2_length A P (l l' : list A) :
  OnOne2 P l l' →
  length l = length l'.
Proof.
  intros h. induction h.
  - cbn. reflexivity.
  - cbn. auto.
Qed.

Lemma Forall2_rst_OnOne2 A (R : relation A) l l' :
  Forall2 R l l' →
  clos_refl_sym_trans _ (OnOne2 R) l l'.
Proof.
  intros h.
  induction h as [| x y l l' h hl ih].
  - apply rst_refl.
  - eapply rst_trans.
    + apply rst_step. constructor. eassumption.
    + eapply rst_step_ind. 2: eassumption.
      intros. eapply rst_step. constructor. assumption.
Qed.

Lemma Forall2_rt_OnOne2 A (R : relation A) l l' :
  Forall2 R l l' →
  clos_refl_trans _ (OnOne2 R) l l'.
Proof.
  intros h.
  induction h as [| x y l l' h hl ih].
  - apply rt_refl.
  - eapply rt_trans.
    + apply rt_step. constructor. eassumption.
    + eapply rt_step_ind. 2: eassumption.
      intros. eapply rt_step. constructor. assumption.
Qed.

Lemma OnOne2_rst_comm A R l l' :
  OnOne2 (clos_refl_sym_trans A R) l l' →
  clos_refl_sym_trans _ (OnOne2 R) l l'.
Proof.
  intros h.
  induction h as [| x l l' hl ih].
  - eapply rst_step_ind with (f := λ z, z :: l). 2: eassumption.
    intros. apply rst_step. constructor. assumption.
  - eapply rst_step_ind. 2: eassumption.
    intros. apply rst_step. constructor. assumption.
Qed.

Lemma OnOne2_rt_comm A R l l' :
  OnOne2 (clos_refl_trans A R) l l' →
  clos_refl_trans _ (OnOne2 R) l l'.
Proof.
  intros h.
  induction h as [| x l l' hl ih].
  - eapply rt_step_ind with (f := λ z, z :: l). 2: eassumption.
    intros. apply rt_step. constructor. assumption.
  - eapply rt_step_ind. 2: eassumption.
    intros. apply rt_step. constructor. assumption.
Qed.

Lemma OnOne2_refl_Forall2 A (R : relation A) :
  Reflexive R →
  inclusion _ (OnOne2 R) (Forall2 R).
Proof.
  intros hrefl l l' h.
  induction h as [ x y l h | x l l' h ih ].
  - constructor.
    + assumption.
    + reflexivity.
  - constructor. all: auto.
Qed.

Lemma OnOne2_impl A (R R' : relation A) l l' :
  inclusion _ R R' →
  OnOne2 R l l' →
  OnOne2 R' l l'.
Proof.
  intros hR h.
  induction h.
  - constructor. auto.
  - constructor. auto.
Qed.

Lemma OnOne2_and_Forall2 A (R R' : relation A) l l' :
  Forall2 R l l' →
  OnOne2 R' l l' →
  OnOne2 (λ x y, R x y ∧ R' x y) l l'.
Proof.
  intros hf ho.
  induction ho in hf |- *.
  - constructor. inversion hf. intuition auto.
  - constructor. inversion hf. intuition auto.
Qed.

Lemma OnOne2_and_Forall_l A P (R : relation A) l l' :
  Forall P l →
  OnOne2 R l l' →
  OnOne2 (λ x y, P x ∧ R x y) l l'.
Proof.
  intros hf ho.
  induction ho in hf |- *.
  - constructor. inversion hf. intuition auto.
  - constructor. inversion hf. intuition auto.
Qed.

Lemma Forall_OnOne2_r A (P : A → Prop) l l' :
  Forall P l →
  OnOne2 (λ _ y, P y) l l' →
  Forall P l'.
Proof.
  intros h h2.
  induction h2 in h |- *.
  - constructor.
    + assumption.
    + inversion h. assumption.
  - inversion h. subst.
    constructor. all: eauto.
Qed.

Lemma OnOne2_nth_error [A] R (l l' : list A) x a :
  OnOne2 R l l' →
  nth_error l x = Some a →
  (nth_error l' x = Some a) ∨ (∃ a', R a a' ∧ nth_error l' x = Some a').
Proof.
  intros h e.
  induction h in x, a, e |- *.
  - destruct x.
    + cbn in *. inversion e. subst.
      right. eexists. intuition eauto.
    + cbn in *. eauto.
  - destruct x.
    + cbn in *. eauto.
    + cbn in *. eauto.
Qed.

Lemma OnOne2_map A R l l' (f : A → A) :
  OnOne2 (λ x y, R (f x) (f y)) l l' →
  OnOne2 R (map f l) (map f l').
Proof.
  intro h. induction h.
  - constructor. assumption.
  - cbn. constructor. assumption.
Qed.

Lemma OnOne2_split A R (l l' : list A) :
  OnOne2 R l l' →
  ∃ n a a',
    nth_error l n = Some a ∧
    nth_error l' n = Some a' ∧
    R a a' ∧
    (∀ m, n ≠ m → nth_error l m = nth_error l' m).
Proof.
  intros h.
  induction h as [ x y l h | x l l' h ih ].
  - eexists 0, _, _. cbn.
    split. 2: split. 3: split. 1-3: eauto.
    intros m ?.
    destruct m. 1: contradiction.
    cbn. reflexivity.
  - destruct ih as (n & a & a' & ? & ? & ? & ?).
    exists (S n), a, a'.
    split. 2: split. 3: split. 1-3: eauto.
    intros m hm.
    destruct m.
    + cbn. reflexivity.
    + cbn. eauto.
Qed.

(** Some mini [congruence] *)

Ltac eqtwice :=
  match goal with
  | e1 : ?x = _, e2 : ?x = _ |- _ =>
    rewrite e2 in e1 ; inversion e1 ; clear e1
  end.

(** On [nth_error] *)

Lemma nth_error_Some_alt A (l : list A) n x :
  nth_error l n = Some x →
  n < length l.
Proof.
  intro h.
  rewrite <- nth_error_Some. congruence.
Qed.

(** [option] util *)

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

Definition onSomeb [A] (P : A → bool) (o : option A) : bool :=
  match o with
  | Some a => P a
  | None => true
  end.

Inductive OnSome [A] (P : A → Prop) : option A → Prop :=
| OnSome_None : OnSome P None
| OnSome_Some a : P a → OnSome P (Some a).

Lemma OnSome_onSome A P o :
  @OnSome A P o ↔ onSome P o.
Proof.
  split.
  - destruct 1. all: cbn. all: auto.
  - destruct o. all: cbn. all: intros ; constructor ; auto.
Qed.

Definition onSomeT [A] (P : A → Type) (o : option A) : Type :=
  match o with
  | Some a => P a
  | None => unit
  end.

Lemma onSomeT_impl A P Q o :
  (∀ a, P a → Q a) →
  @onSomeT A P o →
  onSomeT Q o.
Proof.
  intros hPQ h.
  destruct o. all: cbn in *. all: auto.
Qed.

Lemma onSome_impl A P Q o :
  (∀ a, P a → Q a) →
  @onSome A P o →
  onSome Q o.
Proof.
  intros hPQ h.
  destruct o. all: cbn in *. all: auto.
Qed.

Lemma onSomeT_prod A P Q o :
  @onSomeT A P o →
  onSomeT Q o →
  onSomeT (λ x, P x * Q x)%type o.
Proof.
  destruct o. all: cbn. all: auto.
Qed.

Lemma onSomeb_onSome A P o :
  @onSomeb A P o = true ↔ onSome (λ x, P x = true) o.
Proof.
  split. all: destruct o. all: cbn. all: auto.
Qed.

Lemma onSome_onSomeT A P o :
  @onSome A P o →
  onSomeT P o.
Proof.
  destruct o. all: cbn.
  - auto.
  - intros. constructor.
Qed.

Lemma onSomeT_onSome A (P : _ → Prop) o :
  @onSomeT A P o →
  onSome P o.
Proof.
  destruct o. all: cbn.
  - auto.
  - intros. constructor.
Qed.

Lemma onSomeT_map [A B] (f : A → B) P o :
  onSomeT (λ x, P (f x)) o →
  onSomeT P (option_map f o).
Proof.
  intros h. destruct o. all: cbn in *. all: auto.
Qed.

Inductive option_rel [A B] (R : A → B → Prop) : option A → option B → Prop :=
| option_none : option_rel R None None
| option_some x y : R x y → option_rel R (Some x) (Some y).

Lemma option_rel_impl [A B] (R R' : A → B → Prop) x y :
  (∀ x y, R x y → R' x y) →
  option_rel R x y →
  option_rel R' x y.
Proof.
  intros hinc h.
  destruct h.
  - constructor.
  - constructor. eauto.
Qed.

Lemma option_rel_map_l A B C (f : A → B) (R : B → C → Prop) o o' :
  option_rel R (option_map f o) o' ↔ option_rel (λ x y, R (f x) y) o o'.
Proof.
  split.
  - intro h. remember (option_map f o) as o'' eqn: e.
    induction h in o, e |- *.
    + destruct o. 1: discriminate.
      constructor.
    + destruct o. 2: discriminate.
      cbn in e. inversion e. subst.
      constructor. assumption.
  - intro h. induction h. 1: constructor.
    cbn. constructor. assumption.
Qed.

Lemma option_rel_flip A B R a b :
  @option_rel A B R a b →
  option_rel (λ b a, R a b) b a.
Proof.
  intro h. induction h. all: constructor ; auto.
Qed.

Lemma option_rel_map_r A B C (f : A → B) R (o : option C) o' :
  option_rel R o (option_map f o') ↔ option_rel (λ x y, R x (f y)) o o'.
Proof.
  split.
  - intro h. apply option_rel_flip in h. rewrite option_rel_map_l in h.
    apply option_rel_flip. assumption.
  - intro h. apply option_rel_flip in h.
    apply option_rel_flip. rewrite option_rel_map_l. assumption.
Qed.

Lemma option_rel_diag [A] (R : A → A → Prop) o :
  OnSome (λ x, R x x) o →
  option_rel R o o.
Proof.
  intros h. destruct h. all: constructor ; auto.
Qed.

Lemma option_rel_trans_inv A B C P R a b :
  option_rel (λ x y, ∃ z, P z x ∧ R z y) a b →
  ∃ c, @option_rel C A P c a ∧ @option_rel C B R c b.
Proof.
  intros h. destruct h as [| x y h].
  - exists None. intuition constructor.
  - destruct h.
    eexists. intuition constructor. all: eassumption.
Qed.

#[export] Instance Reflexive_option_rel A (R : relation A) :
  Reflexive R →
  Reflexive (option_rel R).
Proof.
  intros hrefl. intros o.
  apply option_rel_diag. destruct o. all: constructor ; eauto.
Qed.

Lemma option_map_option_map [A B C] (f : A → B) (g : B → C) o :
  option_map g (option_map f o) = option_map (λ x, g (f x)) o.
Proof.
  destruct o. all: reflexivity.
Qed.

Lemma option_map_ext [A B] (f g : A → B) o :
  (∀ a, f a = g a) →
  option_map f o = option_map g o.
Proof.
  intros e.
  destruct o. 2: reflexivity.
  cbn. f_equal. auto.
Qed.

Lemma option_map_ext_onSomeT [A B] (f g : A → B) o :
  onSomeT (λ x, f x = g x) o →
  option_map f o = option_map g o.
Proof.
  destruct o. all: cbn. all: congruence.
Qed.

Lemma option_map_id [A] o :
  @option_map A A id o = o.
Proof.
  destruct o. all: reflexivity.
Qed.

Lemma option_map_id_onSomeT [A] f (o : option A) :
  onSomeT (λ x, f x = x) o →
  option_map f o = o.
Proof.
  intro h.
  rewrite <- option_map_id.
  apply option_map_ext_onSomeT. assumption.
Qed.

Inductive some_rel [A B] (R : A → B → Prop) : option A → option B → Prop :=
| some_rel_some a b : R a b → some_rel R (Some a) (Some b).

Lemma option_rel_rst_some_rel A (R : relation A) a b :
  option_rel R a b →
  clos_refl_sym_trans _ (some_rel R) a b.
Proof.
  intros h. destruct h.
  - apply rst_refl.
  - apply rst_step. constructor. assumption.
Qed.

Lemma option_rel_rt_some_rel A (R : relation A) a b :
  option_rel R a b →
  clos_refl_trans _ (some_rel R) a b.
Proof.
  intros h. destruct h.
  - apply rt_refl.
  - apply rt_step. constructor. assumption.
Qed.

Lemma some_rel_rst_comm A R x y :
  some_rel (clos_refl_sym_trans A R) x y →
  clos_refl_sym_trans _ (some_rel R) x y.
Proof.
  intros h. destruct h.
  eapply rst_step_ind. 2: eassumption.
  intros. apply rst_step. constructor. assumption.
Qed.

Lemma some_rel_rt_comm A R x y :
  some_rel (clos_refl_trans A R) x y →
  clos_refl_trans _ (some_rel R) x y.
Proof.
  intros h. destruct h.
  eapply rt_step_ind. 2: eassumption.
  intros. apply rt_step. constructor. assumption.
Qed.

Lemma some_rel_option_rel A B (R : A → B → Prop) a b :
  some_rel R a b →
  option_rel R a b.
Proof.
  intro h. destruct h.
  constructor. assumption.
Qed.

Lemma OnOne2_some_rel_nth_error A R l l' x (a : A) :
  OnOne2 (some_rel R) l l' →
  nth_error l x = Some (Some a) →
  (nth_error l' x = Some (Some a)) ∨
  (∃ a', R a a' ∧ nth_error l' x = Some (Some a')).
Proof.
  intros h e.
  eapply OnOne2_nth_error in h. 2: eassumption.
  destruct h as [h|h].
  - auto.
  - right.
    destruct h as (a' & h & e').
    inversion h. subst.
    eexists. intuition eauto.
Qed.

Lemma some_rel_map A R o o' (f : A → A) :
  some_rel (λ x y, R (f x) (f y)) o o' →
  some_rel R (option_map f o) (option_map f o').
Proof.
  intro h. induction h.
  constructor. assumption.
Qed.

Lemma some_rel_impl A R R' (o o' : option A) :
  some_rel R o o' →
  inclusion _ R R' →
  some_rel R' o o'.
Proof.
  intros h hi. induction h.
  constructor. auto.
Qed.

(** [fold_left] util *)

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

(** [list] util *)

Lemma list_last_split [A] (l : list A) :
  l = [] ∨ (∃ a l', l = l' ++ [ a ]).
Proof.
  replace l with (rev (rev l)) by apply rev_involutive.
  set (l' := rev l). clearbody l'.
  destruct l'.
  - left. reflexivity.
  - right. cbn. eexists _,_. reflexivity.
Qed.

(** Some Equations signatures *)

Derive Signature for Forall2.
Derive Signature for option_rel.
