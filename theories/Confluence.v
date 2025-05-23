(** * Generic results about confluence 

  Heavily inspired from MetaRocq's proofs.

*)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp Require Import Util.
From Stdlib Require Import Setoid Morphisms Relation_Definitions
  Relation_Operators.
From Equations Require Import Equations.

Import ListNotations.

Set Default Goal Selector "!".

Require Import Equations.Prop.DepElim.

Arguments clos_refl_trans {A}.
Arguments clos_refl_trans_n1 {A}.
Arguments clos_refl_trans_1n {A}.
Arguments inclusion {A}.

Definition joinable [A] (R : relation A) u v :=
  ∃ w, R u w ∧ R v w.

Definition diamond [A] (R : relation A) :=
  ∀ t u v, R t u → R t v → joinable R u v.

Definition confluent [A] (R : relation A) :=
  diamond (clos_refl_trans R).

Lemma diamond_aux A R t u v :
  @diamond A R →
  clos_refl_trans_1n R t u →
  R t v →
  joinable (clos_refl_trans R) u v.
Proof.
  intros hd hu hv.
  induction hu as [| x y z hxy hyz ih ] in v, hv |- *.
  - eexists. split.
    + constructor. eassumption.
    + apply rt_refl.
  - eapply hd in hxy as h'. forward h' by eassumption.
    destruct h' as [w [hw1 hw2]].
    specialize ih with (1 := hw1) as [w' [h1 h2]].
    eexists. split.
    + eassumption.
    + eapply rt_trans. 2: eassumption.
      constructor. assumption.
Qed.

Lemma diamond_confluent A R :
  @diamond A R →
  confluent R.
Proof.
  intros hd t u v hu hv.
  apply Operators_Properties.clos_rt_rt1n in hv.
  induction hv as [| ??? h ? ih ] in u, hu |- *.
  - eexists. split.
    + apply rt_refl.
    + eassumption.
  - eapply diamond_aux in h. 2: eassumption.
    2:{ apply Operators_Properties.clos_rt_rt1n. eassumption. }
    destruct h as [w [h1 h2]].
    specialize ih with (1 := h2) as [w' [h1' h2']].
    exists w'. split.
    + eapply rt_trans. all: eassumption.
    + assumption.
Qed.

Instance diamond_morphism A : 
  Proper (relation_equivalence ==> iff) (@diamond A).
Proof.
  intros R R' h. revert R R' h. wlog_iff. 
  intros R R' h hR.
  intros t u v hu hv.
  apply h in hu, hv.
  eapply hR in hu. forward hu by eassumption.
  destruct hu as [w [h1 h2]].
  exists w.
  unfold relation_equivalence in h. unfold predicate_equivalence in h.
  unfold pointwise_lifting in h. rewrite <- !h.
  intuition eauto.
Qed.

Instance clos_refl_trans_morphism A :
  Proper (relation_equivalence ==> relation_equivalence) (@clos_refl_trans A).
Proof.
  intros R R' h x y.
  unfold relation_equivalence, predicate_equivalence, pointwise_lifting in *.
  split.
  - intros hR. eapply rt_step_ind with (f := λ x, x). 2: eassumption.
    intros ?? h'. rewrite h in h'.
    apply rt_step. assumption.
  - intros hR. eapply rt_step_ind with (f := λ x, x). 2: eassumption.
    intros ?? h'. rewrite <- h in h'.
    apply rt_step. assumption.
Qed.

Instance confluent_morphism A : 
  Proper (relation_equivalence ==> iff) (@confluent A).
Proof.
  intros R R' h.
  apply diamond_morphism.
  apply clos_refl_trans_morphism. assumption.
Qed.

Lemma clos_rt_monotone A (R R' : relation A) :
  inclusion R R' →
  inclusion (clos_refl_trans R) (clos_refl_trans R').
Proof.
  intros h x y hxy.
  eapply rt_step_ind with (f := id). 2: eassumption.
  intros. constructor. apply h. assumption.
Qed.

Lemma sandwish A (R P : relation A) :
  inclusion R P →
  inclusion P (clos_refl_trans R) →
  confluent P →
  confluent R.
Proof.
  intros hRP%clos_rt_monotone hPR%clos_rt_monotone hP.
  eapply diamond_morphism. 2: eassumption.
  intros x y. split. 1: eauto.
  intro. apply Operators_Properties.clos_rt_idempotent. auto.
Qed.
