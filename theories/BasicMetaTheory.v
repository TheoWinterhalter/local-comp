(** Basic meta-theory *)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

(** Better induction principle for [term] *)

Lemma term_rect :
   ∀ (P : term → Type),
    (∀ n, P (var n)) →
    (∀ i, P (Sort i)) →
    (∀ A, P A → ∀ B, P B → P (Pi A B)) →
    (∀ A, P A → ∀ t, P t → P (lam A t)) →
    (∀ u, P u → ∀ v, P v → P (app u v)) →
    (∀ (c : gref) (ξ : instance), All (onSomeT P) ξ → P (const c ξ)) →
    (∀ (x : aref), P (assm x)) →
    ∀ t, P t.
Proof.
  intros P hvar hsort hpi hlam happ hconst hassm.
  fix aux 1. move aux at top.
  intro t. destruct t.
  6:{
    eapply hconst.
    revert l. fix aux1 1.
    intro ξ. destruct ξ as [| t ξ]. 1: constructor.
    constructor. 2: eauto.
    destruct t. 2: constructor.
    cbn. auto.
  }
  all: match goal with h : _ |- _ => eapply h end.
  all: eauto.
Defined.

(** Better induction principle for [gscope] *)

Lemma gscope_ind :
  ∀ Σ (P : term → Prop),
  (∀ x, P (var x)) →
  (∀ i, P (Sort i)) →
  (∀ A B, gscope Σ A → P A → gscope Σ B → P B → P (Pi A B)) →
  (∀ A t, gscope Σ A → P A → gscope Σ t → P t → P (lam A t)) →
  (∀ u v, gscope Σ u → P u → gscope Σ v → P v → P (app u v)) →
  (∀ c ξ Ξ' A t,
    Σ c = Some (Def Ξ' A t) →
    gscope_instance Σ ξ →
    Forall (OnSome P) ξ →
    P (const c ξ)
  ) →
  (∀ x, P (assm x)) →
  ∀ t, gscope Σ t → P t.
Proof.
  intros Σ P hvar hsort hpi hlam happ hconst hassm.
  fix aux 2. move aux at top.
  intros t h. destruct h as [| | | | | c ξ ??? hc h |].
  6:{
    eapply hconst. 1,2: eassumption.
    revert ξ h.
    fix aux1 2.
    intros ξ h. destruct h as [| u ξ hu hξ].
    - constructor.
    - constructor. 2: eauto.
      destruct hu.
      + constructor.
      + constructor. eauto.
  }
  all: match goal with h : _ |- _ => solve [ eapply h ; eauto ] end.
Qed.

(** Better induction principle for [conversion] *)

Lemma conversion_ind :
  ∀ (Σ : gctx) Ξ (P : term → term → Prop),
    (∀ A t u, P (app (lam A t) u) (t <[ u.. ])) →
    (∀ c ξ Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      inst_equations Σ Ξ ξ Ξ' →
      inst_equations_ P ξ Ξ' →
      closed t = true →
      P (const c ξ) (inst ξ t)
    ) →
    (∀ n rl σ,
      ictx_get Ξ n = Some (Comp rl) →
      let Θ := rl.(cr_env) in
      let k := length Θ in
      let lhs := rl.(cr_pat) in
      let rhs := rl.(cr_rep) in
      scoped k lhs = true →
      scoped k rhs = true →
      P (lhs <[ σ ]) (rhs <[ σ ])
    ) →
    (∀ A A' B B',
      Σ ;; Ξ ⊢ A ≡ A' →
      P A A' →
      Σ ;; Ξ ⊢ B ≡ B' →
      P B B' →
      P (Pi A B) (Pi A' B')
    ) →
    (∀ A A' t t',
      Σ ;; Ξ ⊢ A ≡ A' →
      P A A' →
      Σ ;; Ξ ⊢ t ≡ t' →
      P t t' →
      P (lam A t) (lam A' t')
    ) →
    (∀ u u' v v',
      Σ ;; Ξ ⊢ u ≡ u' →
      P u u' →
      Σ ;; Ξ ⊢ v ≡ v' →
      P v v' →
      P (app u v) (app u' v')
    ) →
    (∀ c ξ ξ',
      Forall2 (option_rel (conversion Σ Ξ)) ξ ξ' →
      Forall2 (option_rel P) ξ ξ' →
      P (const c ξ) (const c ξ')
    ) →
    (∀ u, P u u) →
    (∀ u v, Σ ;; Ξ ⊢ u ≡ v → P u v → P v u) →
    (∀ u v w,
      Σ ;; Ξ ⊢ u ≡ v →
      P u v →
      Σ ;; Ξ ⊢ v ≡ w →
      P v w →
      P u w
    ) →
    ∀ u v, Σ ;; Ξ ⊢ u ≡ v → P u v.
Proof.
  intros Σ Ξ P hbeta hunfold hred hpi hlam happ hconst hrefl hsym htrans.
  fix aux 3. move aux at top.
  intros u v h. destruct h.
  7:{
    eapply hconst. 1: assumption.
    revert ξ ξ' H.
    fix aux1 3.
    intros ξ ξ' h. destruct h as [| u u' ξ ξ' hu hξ].
    - constructor.
    - constructor. 2: eauto.
      destruct hu. 1: constructor.
      constructor. eauto.
  }
  2:{
    eapply hunfold. 1,2,4: eassumption.
    intros x rl hx. specialize (H0 _ _ hx) as (? & ? & ?).
    intuition eauto.
  }
  all: match goal with h : _ |- _ => solve [ eapply h ; eauto ] end.
Qed.

(** Better induction principle for [typing] *)

Lemma typing_ind :
  ∀ Σ Ξ (P : ctx → term → term → Prop),
    (∀ Γ x A, nth_error Γ x = Some A → P Γ (var x) (Nat.add (S x) ⋅ A)) →
    (∀ Γ i, P Γ (Sort i) (Sort (S i))) →
    (∀ Γ i j A B,
      Σ ;; Ξ | Γ ⊢ A : Sort i →
      P Γ A (Sort i) →
      Σ ;; Ξ | Γ,, A ⊢ B : Sort j →
      P (Γ,, A) B (Sort j) →
      P Γ (Pi A B) (Sort (Nat.max i j))
    ) →
    (∀ Γ i j A B t,
      Σ ;; Ξ | Γ ⊢ A : Sort i →
      P Γ A (Sort i) →
      Σ ;; Ξ | Γ,, A ⊢ B : Sort j →
      P (Γ,, A) B (Sort j) →
      Σ ;; Ξ | Γ,, A ⊢ t : B →
      P (Γ,, A) t B → P Γ (lam A t) (Pi A B)
    ) →
    (∀ Γ i j A B t u,
      Σ ;; Ξ | Γ ⊢ t : Pi A B →
      P Γ t (Pi A B) →
      Σ ;; Ξ | Γ ⊢ u : A →
      P Γ u A → Σ ;; Ξ | Γ ⊢ A : Sort i →
      P Γ A (Sort i) → Σ ;; Ξ | Γ,, A ⊢ B : Sort j →
      P (Γ,, A) B (Sort j) →
      P Γ (app t u) (B <[ u..])
    ) →
    (∀ Γ c ξ Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      inst_typing Σ Ξ Γ ξ Ξ' →
      inst_typing_ Σ Ξ P Γ ξ Ξ' →
      closed A = true →
      P Γ (const c ξ) (inst ξ A)
    ) →
    (∀ Γ x A,
      ictx_get Ξ x = Some (Assm A) →
      closed A = true →
      P Γ (assm x) A
    ) →
    (∀ Γ i A B t,
      Σ ;; Ξ | Γ ⊢ t : A →
      P Γ t A →
      Σ ;; Ξ ⊢ A ≡ B →
      Σ ;; Ξ | Γ ⊢ B : Sort i →
      P Γ B (Sort i) →
      P Γ t B
    ) →
    ∀ Γ t A, Σ ;; Ξ | Γ ⊢ t : A → P Γ t A.
Proof.
  intros Σ Ξ P hvar hsort hpi hlam happ hconst hassm hconv.
  fix aux 4. move aux at top.
  intros Γ t A h. destruct h as [| | | | | ????? hc h hA | |].
  6:{
    eapply hconst. 1,2,4: eassumption.
    destruct h as [h1 [h2 h3]].
    split. 1: assumption.
    split. 2: assumption.
    intros n B hn. specialize (h2 _ _ hn).
    intuition eauto.
  }
  all: match goal with h : _ |- _ => solve [ eapply h ; eauto ] end.
Qed.

(** Reasoning principle on [inst_typing] *)

Lemma inst_typing_prop_ih Σ Ξ Γ ξ Ξ' P :
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ _ t _, P t) Γ ξ Ξ' →
  Forall (OnSome P) ξ.
Proof.
  intros h ih.
  rewrite Forall_forall. intros o ho.
  eapply In_nth_error in ho as [x hx].
  destruct o as [u |]. 2: constructor.
  constructor.
  destruct ih as [heq [ih e]]. red in ih. specialize (ih x).
  destruct (ictx_get Ξ' x) as [[] |] eqn:e'.
  3:{
    unfold ictx_get in e'. destruct (_ <=? _) eqn: e1.
    - rewrite Nat.leb_le in e1. rewrite <- e in e1.
      rewrite <- nth_error_None in e1. congruence.
    - rewrite nth_error_None in e'.
      rewrite Nat.leb_gt in e1. lia.
    }
    2:{
      specialize (heq _ _ e'). cbn in heq. intuition congruence.
    }
    specialize ih with (1 := eq_refl).
    unfold iget in ih. rewrite hx in ih.
    apply ih.
Qed.

(** Typing implies scoping *)

Lemma typing_scoped Σ Ξ Γ t A :
  Σ ;; Ξ | Γ ⊢ t : A →
  scoped (length Γ) t = true.
Proof.
  intro h.
  induction h using typing_ind.
  all: try solve [ cbn - ["<?"] in * ; eauto ].
  all: try solve [
    cbn - ["<?"] in * ;
    rewrite Bool.andb_true_iff in * ;
    intuition eauto
  ].
  - cbn - ["<?"]. rewrite Nat.ltb_lt. eapply nth_error_Some. congruence.
  - cbn. eapply forallb_forall. intros u hu.
    eapply In_nth_error in hu as [n hn].
    destruct u. 2: reflexivity.
    cbn.
    destruct H1 as [heq [ih e]]. red in ih. specialize (ih n).
    destruct (ictx_get Ξ' n) as [[] |] eqn:e'.
    3:{
      unfold ictx_get in e'. destruct (_ <=? _) eqn: e1.
      - rewrite Nat.leb_le in e1. rewrite <- e in e1.
        rewrite <- nth_error_None in e1. congruence.
      - rewrite nth_error_None in e'.
        rewrite Nat.leb_gt in e1. lia.
    }
    2:{
      specialize (heq _ _ e'). cbn in heq. intuition congruence.
    }
    specialize ih with (1 := eq_refl).
    unfold iget in ih. rewrite hn in ih.
    cbn. apply ih.
Qed.

Lemma typing_closed Σ Ξ t A :
  Σ ;; Ξ | ∙ ⊢ t : A →
  closed t = true.
Proof.
  intros h.
  eapply typing_scoped with (Γ := ∙).
  eassumption.
Qed.

(** Renaming preserves typing *)

Definition rtyping (Γ : ctx) (ρ : nat → nat) (Δ : ctx) : Prop :=
  ∀ x A,
    nth_error Δ x = Some A →
    ∃ B,
      nth_error Γ (ρ x) = Some B ∧
      (plus (S x) >> ρ) ⋅ A = (plus (S (ρ x))) ⋅ B.

#[export] Instance rtyping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) rtyping.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  intros n A en. rewrite <- e.
  eapply h in en as [B [en eB]].
  eexists. split. 1: eassumption.
  rasimpl. rasimpl in eB. rewrite <- eB.
  apply extRen_term. intro x. cbn. core.unfold_funcomp.
  rewrite <- e. reflexivity.
Qed.

Lemma autosubst_simpl_rtyping :
  ∀ Γ Δ r s,
    RenSimplification r s →
    rtyping Γ r Δ ↔ rtyping Γ s Δ.
Proof.
  intros Γ Δ r s H.
  apply rtyping_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_rtyping : rasimpl_outermost.

Lemma rtyping_up :
  ∀ Γ Δ A ρ,
    rtyping Γ ρ Δ →
    rtyping (Γ ,, (ρ ⋅ A)) (upRen_term_term ρ) (Δ,, A).
Proof.
  intros Γ Δ A ρ hρ.
  intros y B hy.
  destruct y.
  - cbn in *. inversion hy. eexists.
    split. 1: reflexivity.
    rasimpl. reflexivity.
  - cbn in *. eapply hρ in hy. destruct hy as [C [en eC]].
    eexists. split. 1: eassumption.
    rasimpl.
    apply (f_equal (λ t, S ⋅ t)) in eC. rasimpl in eC.
    assumption.
Qed.

Lemma rtyping_S :
  ∀ Γ A,
    rtyping (Γ ,, A) S Γ.
Proof.
  intros Γ A. intros x B e.
  simpl. rasimpl.
  eexists. split. 1: eassumption.
  rasimpl. reflexivity.
Qed.

Lemma rtyping_comp Γ Δ Θ ρ ρ' :
  rtyping Δ ρ Θ →
  rtyping Γ ρ' Δ →
  rtyping Γ (ρ >> ρ') Θ.
Proof.
  intros hρ hρ'. intros x A e.
  simpl. rasimpl.
  eapply hρ in e as [B [e h]].
  eapply hρ' in e as [C [e h']].
  exists C. split. 1: assumption.
  apply (f_equal (λ t, ρ' ⋅ t)) in h. rasimpl in h.
  rasimpl in h'. rewrite h' in h.
  etransitivity. 1: exact h.
  reflexivity.
Qed.

Lemma rtyping_add Γ Δ :
  rtyping (Γ ,,, Δ) (plus (length Δ)) Γ.
Proof.
  intros x A e.
  exists A. split.
  - rewrite nth_error_app2. 2: lia.
    rewrite <- e. f_equal. lia.
  - apply extRen_term. intro. core.unfold_funcomp. lia.
Qed.

Lemma ren_instance_comp :
  ∀ ρ ρ' ξ,
    ren_instance ρ (ren_instance ρ' ξ) = ren_instance (ρ' >> ρ) ξ.
Proof.
  intros ρ ρ' ξ.
  rewrite map_map.
  apply map_ext. intro u.
  rewrite option_map_option_map.
  apply option_map_ext. intro t.
  rasimpl. reflexivity.
Qed.

Lemma lift_ren_instance :
  ∀ ρ ξ,
    lift_instance (ren_instance ρ ξ) =
    ren_instance (upRen_term_term ρ) (lift_instance ξ).
Proof.
  intros ρ ξ.
  rewrite !ren_instance_comp. reflexivity.
Qed.

Lemma ren_instance_ext ρ ζ ξ :
  (∀ n, ρ n = ζ n) →
  ren_instance ρ ξ = ren_instance ζ ξ.
Proof.
  intros h.
  apply map_ext. intro.
  apply option_map_ext. intro.
  apply extRen_term. assumption.
Qed.

Lemma liftn_liftn n m ξ :
  liftn n (liftn m ξ) = liftn (n + m) ξ.
Proof.
  rewrite ren_instance_comp.
  apply ren_instance_ext. unfold core.funcomp. intro. lia.
Qed.

Fixpoint uprens k (ρ : nat → nat) :=
  match k with
  | 0 => ρ
  | S k => upRen_term_term (uprens k ρ)
  end.

Lemma liftn_ren_instance n ρ ξ :
  liftn n (ren_instance ρ ξ) = ren_instance (uprens n ρ) (liftn n ξ).
Proof.
  rewrite 2!ren_instance_comp. apply ren_instance_ext.
  intros m. unfold core.funcomp.
  induction n as [| n ih] in m, ρ |- *.
  - reflexivity.
  - cbn. unfold core.funcomp. rewrite <- ih.
    reflexivity.
Qed.

Lemma iget_ren ξ x ρ :
  iget (ren_instance ρ ξ) x = ρ ⋅ (iget ξ x).
Proof.
  unfold iget.
  rewrite nth_error_map.
  destruct (nth_error ξ x) as [[] |]. all: reflexivity.
Qed.

Lemma ren_inst :
  ∀ ρ ξ t,
    ρ ⋅ (inst ξ t) = inst (ren_instance ρ ξ) (ρ ⋅ t).
Proof.
  intros ρ ξ t.
  induction t using term_rect in ρ, ξ |- *.
  all: try solve [ cbn ; rewrite ?lift_ren_instance ; f_equal ; eauto ].
  - cbn. f_equal.
    rewrite !map_map. apply map_ext_All.
    eapply All_impl. 2: eassumption.
    intros u h.
    change @core.option_map with @option_map.
    rewrite !option_map_option_map. apply option_map_ext_onSomeT.
    eapply onSomeT_impl. 2: eassumption.
    cbn. intros t ht. auto.
  - cbn. rewrite iget_ren. reflexivity.
Qed.

Lemma scoped_ren :
  ∀ ρ k t,
    scoped k t = true →
    (uprens k ρ) ⋅ t = t.
Proof.
  intros ρ k t h.
  induction t using term_rect in k, h |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn ;
    apply andb_prop in h as [] ;
    change (upRen_term_term (uprens ?k ?ρ)) with (uprens (S k) ρ) ;
    f_equal ;
    eauto
  ].
  - cbn - ["<?"] in *. f_equal.
    apply Nat.ltb_lt in h.
    induction n as [| n ih] in k, h |- *.
    + destruct k. 1: lia.
      reflexivity.
    + destruct k. 1: lia.
      cbn. core.unfold_funcomp. f_equal.
      apply ih. lia.
  - cbn in *. f_equal.
    rewrite <- map_id. apply map_ext_All.
    apply forallb_All in h. move h at top.
    eapply All_prod in h. 2: eassumption.
    eapply All_impl. 2: eassumption. clear.
    cbn. intros o [h1 h2].
    change @core.option_map with @option_map.
    apply option_map_id_onSomeT.
    rewrite onSomeb_onSome in h2. eapply onSome_onSomeT in h2.
    eapply onSomeT_prod in h1. 2: eassumption.
    eapply onSomeT_impl. 2: eassumption. clear.
    cbn. intros t [h1 h2]. eauto.
Qed.

Corollary closed_ren :
  ∀ ρ t,
    closed t = true →
    ρ ⋅ t = t.
Proof.
  intros ρ t h.
  eapply scoped_ren in h. eauto.
Qed.

Lemma ren_instance_id ξ :
  ren_instance id ξ = ξ .
Proof.
  rewrite <- map_id. apply map_ext. intro.
  rewrite <- option_map_id. apply option_map_ext. intro.
  rasimpl. reflexivity.
Qed.

Lemma ren_instance_id_ext ρ ξ :
  (∀ n, ρ n = n) →
  ren_instance ρ ξ = ξ.
Proof.
  intro h.
  etransitivity. 2: eapply ren_instance_id.
  apply ren_instance_ext. assumption.
Qed.

Corollary closed_ren_instance ρ ξ :
  closed_instance ξ = true →
  ren_instance ρ ξ = ξ.
Proof.
  intros h.
  etransitivity. 2: apply ren_instance_id.
  apply map_ext_All. eapply All_impl.
  2:{ apply forallb_All. eassumption. }
  cbn. intros o ho%onSomeb_onSome%onSome_onSomeT.
  apply option_map_ext_onSomeT. eapply onSomeT_impl. 2: eassumption.
  cbn. rasimpl. apply closed_ren.
Qed.

Lemma inst_equations_ren_ih Σ Ξ ρ ξ Ξ' :
  inst_equations Σ Ξ ξ Ξ' →
  inst_equations_ (λ u v, ∀ ρ, Σ ;; Ξ ⊢ ρ ⋅ u ≡ ρ ⋅ v) ξ Ξ' →
  inst_equations Σ Ξ (ren_instance ρ ξ) Ξ'.
Proof.
  intros h ih.
  intros x rl hx m. cbn.
  rewrite nth_error_map.
  rewrite liftn_ren_instance.
  specialize (ih _ _ hx) as (e & hl & hr & ih).
  fold m in hl, hr, ih.
  specialize ih with (ρ := uprens m ρ).
  rewrite e. cbn.
  rewrite 2!ren_inst in ih.
  rewrite 2!scoped_ren in ih. 2,3: eassumption.
  intuition eauto.
Qed.

Lemma conv_ren Σ Ξ ρ u v :
  Σ ;; Ξ ⊢ u ≡ v →
  Σ ;; Ξ ⊢ ρ ⋅ u ≡ ρ ⋅ v.
Proof.
  intros h.
  induction h using conversion_ind in ρ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto ].
  - rasimpl. eapply meta_conv_trans_r. 1: econstructor.
    rasimpl. reflexivity.
  - rasimpl. eapply conv_trans. 1: econstructor. 1,3: eassumption.
    1: eauto using inst_equations_ren_ih.
    rewrite ren_inst. rewrite closed_ren. 2: assumption.
    ttconv.
  - cbn. constructor.
    rewrite Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros o o' h.
    rewrite option_rel_map_l, option_rel_map_r.
    eapply option_rel_impl. 2: eassumption.
    cbn. intros u v ih. eauto.
Qed.

Fixpoint ren_ctx ρ Γ {struct Γ} :=
  match Γ with
  | [] => ∙
  | A :: Γ => (ren_ctx ρ Γ) ,, (uprens (length Γ) ρ ⋅ A)
  end.

Lemma rtyping_uprens Γ Δ Θ ρ :
  rtyping Δ ρ Γ →
  rtyping (Δ ,,, ren_ctx ρ Θ) (uprens (length Θ) ρ) (Γ ,,, Θ).
Proof.
  intros h.
  induction Θ as [| A Θ ih].
  - cbn. assumption.
  - cbn. rewrite app_comm_cons. cbn. eapply rtyping_up. assumption.
Qed.

Corollary rtyping_uprens_eq Γ Δ Θ ρ k :
  rtyping Δ ρ Γ →
  k = length Θ →
  rtyping (Δ ,,, ren_ctx ρ Θ) (uprens k ρ) (Γ ,,, Θ).
Proof.
  intros h ->.
  eapply rtyping_uprens. assumption.
Qed.

Lemma ups_below k σ n :
  n < k →
  ups k σ n = var n.
Proof.
  intro h.
  induction k as [| k ih] in n, σ, h |- *. 1: lia.
  cbn. destruct n as [| ].
  - reflexivity.
  - cbn. core.unfold_funcomp. rewrite ih. 2: lia.
    reflexivity.
Qed.

Lemma ups_above k σ n :
  ups k σ (k + n) = (plus k) ⋅ σ n.
Proof.
  induction k as [| k ih] in n |- *.
  - cbn. rasimpl. reflexivity.
  - cbn. core.unfold_funcomp. rewrite ih.
    rasimpl. reflexivity.
Qed.

Lemma length_ctx_inst ξ Γ :
  length (ctx_inst ξ Γ) = length Γ.
Proof.
  induction Γ in ξ |- *.
  - reflexivity.
  - cbn. eauto.
Qed.

Lemma ren_ctx_inst ρ ξ Γ :
  ren_ctx ρ (ctx_inst ξ Γ) = ctx_inst (ren_instance ρ ξ) Γ.
Proof.
  induction Γ as [| A Γ ih] in ρ, ξ |- *.
  - reflexivity.
  - cbn. rewrite ih. f_equal.
    rewrite length_ctx_inst.
    rewrite ren_inst.
    rewrite <- liftn_ren_instance. f_equal.
    apply scoped_ren.
    (* Would need the context to be closed *)
Abort.

(* TODO MOVE *)
Lemma inst_equations_prop Σ Ξ ξ Ξ' P :
  inst_equations Σ Ξ ξ Ξ' →
  (∀ u v, Σ ;; Ξ ⊢ u ≡ v → P u v) →
  inst_equations_ P ξ Ξ'.
Proof.
  intros h ih.
  intros x rl hx. specialize (h _ _ hx).
  cbn in *. intuition eauto.
Qed.

Lemma inst_typing_ren Σ Ξ Δ Γ ρ ξ Ξ' :
  rtyping Δ ρ Γ →
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ Γ t A,
    ∀ Δ ρ, rtyping Δ ρ Γ → Σ ;; Ξ | Δ ⊢ ρ ⋅ t : ρ ⋅ A
  ) Γ ξ Ξ' →
  inst_typing Σ Ξ Δ (ren_instance ρ ξ) Ξ'.
Proof.
  intros hρ [h1 [h2 h3]] [ih1 [ih2 ih3]].
  split. 2: split.
  - eauto using inst_equations_ren_ih, inst_equations_prop, conv_ren.
  - intros x A hx. specialize (ih2 _ _ hx) as [hc ih2]. cbn in ih2.
    split. 1: assumption.
    rewrite iget_ren. eapply meta_conv.
    + eauto.
    + rewrite !ren_inst. f_equal.
      apply closed_ren. assumption.
  - rewrite length_map. assumption.
Qed.

Lemma typing_ren :
  ∀ Σ Ξ Γ Δ ρ t A,
    rtyping Δ ρ Γ →
    Σ ;; Ξ | Γ ⊢ t : A →
    Σ ;; Ξ | Δ ⊢ ρ ⋅ t : ρ ⋅ A.
Proof.
  intros Σ Ξ Γ Δ ρ t A hρ ht.
  induction ht using typing_ind in Δ, ρ, hρ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto using rtyping_up ].
  - rasimpl. eapply hρ in H as [B [? eB]].
    rasimpl in eB. rewrite eB.
    econstructor. eassumption.
  - rasimpl. rasimpl in IHht1. rasimpl in IHht4.
    eapply meta_conv. 1: econstructor. all: eauto.
    1:{ eauto using rtyping_up. }
    rasimpl. reflexivity.
  - rasimpl. eapply meta_conv. 1: econstructor.
    + eassumption.
    + eapply inst_typing_ren. all: eassumption.
    + assumption.
    + rewrite ren_inst. f_equal.
      symmetry. apply closed_ren. assumption.
  - rasimpl. rewrite closed_ren. 2: assumption.
    econstructor. all: assumption.
  - rasimpl. rasimpl in IHht2.
    econstructor. all: eauto.
    eapply conv_ren. all: eassumption.
Qed.

(** Reproving [ext_term] but with scoping assumption *)

Definition eq_subst_on k (σ θ : nat → term) :=
  ∀ x, x < k → σ x = θ x.

Lemma eq_subst_on_up k σ θ :
  eq_subst_on k σ θ →
  eq_subst_on (S k) (up_term σ) (up_term θ).
Proof.
  intros h [] he.
  - reflexivity.
  - cbn. repeat core.unfold_funcomp. f_equal.
    apply h. lia.
Qed.

Lemma ext_term_scoped k t σ θ :
  scoped k t = true →
  eq_subst_on k σ θ →
  t <[ σ ] = t <[ θ ].
Proof.
  intros h e.
  induction t using term_rect in k, h, σ, θ, e |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn in * ; apply andb_prop in h ;
    f_equal ; intuition eauto using eq_subst_on_up
  ].
  - cbn. apply e. cbn - ["<?"] in h. rewrite Nat.ltb_lt in h. assumption.
  - cbn in *. f_equal.
    apply map_ext_All.
    apply forallb_All in h. move h at top.
    eapply All_prod in h. 2: eassumption.
    eapply All_impl. 2: eassumption. clear - e.
    cbn. intros o [h1 h2].
    apply option_map_ext_onSomeT.
    apply onSomeb_onSome, onSome_onSomeT in h2.
    eapply onSomeT_prod in h1. 2: eassumption.
    eapply onSomeT_impl. 2: eassumption. clear - e.
    cbn. intros t [h1 h2]. eauto.
Qed.

(** Corollary: every substitution acts like a list of terms

  We present two versions: one with actual lists, and one where we truncate
  a substitution directly, behaving as a shift outside.
  The latter has the advantage that it verifies the condition for
  [subst_inst] later.

*)

Fixpoint listify k (σ : nat → term) :=
  match k with
  | 0 => []
  | S k => σ 0 :: listify k (S >> σ)
  end.

Fixpoint trunc k d (σ : nat → term) :=
  match k with
  | 0 => plus d >> ids
  | S k => σ 0 .: trunc k d (S >> σ)
  end.

Lemma eq_subst_trunc k d σ :
  eq_subst_on k σ (trunc k d σ).
Proof.
  intros x h.
  induction k as [| k ih] in x, h, σ |- *. 1: lia.
  cbn. destruct x as [| x].
  - reflexivity.
  - cbn. apply (ih (S >> σ)). lia.
Qed.

Lemma trunc_bounds k d σ x :
  trunc k d σ (k + x) = var (d + x).
Proof.
  induction k as [| k ih] in σ, x |- *.
  - cbn. reflexivity.
  - cbn. apply ih.
Qed.

(** Substitution preserves typing *)

Inductive styping Σ Ξ (Γ : ctx) (σ : nat → term) : ctx → Prop :=
| type_nil : styping Σ Ξ Γ σ ∙
| type_cons Δ A :
    styping Σ Ξ Γ (S >> σ) Δ →
    Σ ;; Ξ | Γ ⊢ σ 0 : A <[ S >> σ ] →
    styping Σ Ξ Γ σ (Δ ,, A).

#[export] Instance styping_morphism Σ Ξ :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) (styping Σ Ξ).
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| ? ? ? ? ih ? ] in σ', e |- *.
  - constructor.
  - constructor.
    + apply ih. intros n. apply e.
    + rewrite <- e. eapply meta_conv. 1: eassumption.
      apply ext_term. intro. apply e.
Qed.

Lemma autosubst_simpl_styping :
  ∀ Σ Ξ Γ Δ r s,
    SubstSimplification r s →
    styping Σ Ξ Γ r Δ ↔ styping Σ Ξ Γ s Δ.
Proof.
  intros Σ Ξ Γ Δ r s H.
  apply styping_morphism. 1,3: reflexivity.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_styping : rasimpl_outermost.

Lemma styping_weak Σ Ξ Γ Δ σ A :
  styping Σ Ξ Γ σ Δ →
  styping Σ Ξ (Γ,, A) (σ >> ren_term S) Δ.
Proof.
  intros h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + eapply meta_conv.
      * eapply typing_ren. 2: eassumption.
        apply rtyping_S.
      * rasimpl. reflexivity.
Qed.

Lemma styping_up Σ Ξ Γ Δ A σ :
  styping Σ Ξ Γ σ Δ →
  styping Σ Ξ (Γ ,, A <[ σ ]) (up_term σ) (Δ,, A).
Proof.
  intros h.
  constructor.
  - rasimpl. apply styping_weak. assumption.
  - rasimpl. eapply meta_conv.
    + econstructor. cbn. reflexivity.
    + rasimpl. reflexivity.
Qed.

Lemma lift_liftn n ξ :
  lift_instance (liftn n ξ) = liftn (S n) ξ.
Proof.
  rewrite ren_instance_comp. reflexivity.
Qed.

(**

  Note: the condition is weird, because we can just use [trunc] to make it work
  for any [m]. The fact that we're free to choose [m] suggests there is a better
  lemma to be had.

*)

Lemma subst_inst σ ξ t n m :
  (∀ k, σ (m + k) = var (n + k)) →
  inst (liftn n ξ) (t <[ σ ]) =
  (inst (liftn m ξ) t) <[ σ >> inst (liftn n ξ) ].
Proof.
  intro hσ.
  induction t using term_rect in n, m, σ, hσ, ξ |- *.
  all: try solve [ cbn ; f_equal ; eauto ].
  - cbn. f_equal. 1: eauto.
    rewrite lift_liftn. rewrite IHt2 with (m := S m).
    2:{ intro. cbn. core.unfold_funcomp. rewrite hσ. reflexivity. }
    rasimpl. rewrite lift_liftn.
    apply ext_term.
    intro. core.unfold_funcomp. cbn.
    destruct x.
    + cbn. reflexivity.
    + cbn. repeat core.unfold_funcomp.
      rewrite ren_inst.
      rewrite lift_liftn. reflexivity.
  - cbn. f_equal. 1: eauto.
    rewrite lift_liftn. rewrite IHt2 with (m := S m).
    2:{ intro. cbn. core.unfold_funcomp. rewrite hσ. reflexivity. }
    rasimpl. rewrite lift_liftn.
    apply ext_term.
    intro. core.unfold_funcomp. cbn.
    destruct x.
    + cbn. reflexivity.
    + cbn. repeat core.unfold_funcomp.
      rewrite ren_inst.
      rewrite lift_liftn. reflexivity.
  - cbn. f_equal.
    rewrite !map_map. apply map_ext_All.
    eapply All_impl. 2: eassumption.
    intros o ho. change @core.option_map with @option_map.
    rewrite !option_map_option_map. apply option_map_ext_onSomeT.
    eapply onSomeT_impl. 2: eassumption.
    eauto.
  - cbn. rewrite !iget_ren. rasimpl.
    rewrite rinstInst'_term.
    apply ext_term. intro k.
    unfold core.funcomp.
    rewrite hσ. cbn. reflexivity.
Qed.

Notation subst_instance σ ξ :=
  (map_instance (subst_term σ) ξ).

Lemma iget_subst σ ξ x :
  iget (subst_instance σ ξ) x = (iget ξ x) <[ σ ].
Proof.
  unfold iget.
  rewrite nth_error_map. destruct nth_error as [ [] |]. all: reflexivity.
Qed.

Lemma subst_inst_scoped σ ξ t k :
  scoped k t = true →
  (∀ n, n < k → σ n = var n) →
  (inst ξ t) <[ σ ] = inst (subst_instance σ ξ) t.
Proof.
  intros h hσ.
  induction t using term_rect in k, h, σ, hσ, ξ |- *.
  all: try solve [ cbn ; f_equal ; eauto ].
  - cbn - ["<?"] in *. apply Nat.ltb_lt in h. auto.
  - cbn in *. apply andb_prop in h as [].
    f_equal. 1: eauto.
    erewrite IHt2. 2: eassumption.
    2:{
      intros [] h. 1: reflexivity.
      rasimpl. cbn. core.unfold_funcomp. rewrite hσ. 2: lia.
      reflexivity.
    }
    f_equal.
    rewrite !map_map. apply map_ext. intro l.
    rewrite !option_map_option_map. apply option_map_ext. intro t.
    rasimpl. reflexivity.
  - cbn in *. apply andb_prop in h as [].
    f_equal. 1: eauto.
    erewrite IHt2. 2: eassumption.
    2:{
      intros [] h. 1: reflexivity.
      rasimpl. cbn. core.unfold_funcomp. rewrite hσ. 2: lia.
      reflexivity.
    }
    f_equal.
    rewrite !map_map. apply map_ext. intro l.
    rewrite !option_map_option_map. apply option_map_ext. intro o.
    rasimpl. reflexivity.
  - cbn in *. apply andb_prop in h as [].
    f_equal. all: eauto.
  - cbn in *. f_equal.
    rewrite map_map. apply map_ext_All.
    apply forallb_All in h. move h at top.
    eapply All_prod in h. 2: eassumption.
    eapply All_impl. 2: eassumption. clear - hσ.
    cbn. intros o [h1 h2].
    change @core.option_map with option_map.
    rewrite option_map_option_map. apply option_map_ext_onSomeT.
    apply onSomeb_onSome, onSome_onSomeT in h2.
    eapply onSomeT_prod in h1. 2: eassumption.
    eapply onSomeT_impl. 2: eassumption. clear - hσ.
    cbn. intros t [h1 h2]. eauto.
  - cbn. symmetry. apply iget_subst.
Qed.

Corollary subst_inst_closed σ ξ t :
  closed t = true →
  (inst ξ t) <[ σ ] = inst (subst_instance σ ξ) t.
Proof.
  intro h.
  eapply subst_inst_scoped.
  - eassumption.
  - lia.
Qed.

Corollary subst_inst_ups σ ξ t k :
  scoped k t = true →
  (inst ξ t) <[ ups k σ ] = inst (subst_instance (ups k σ) ξ) t.
Proof.
  intros h.
  eapply subst_inst_scoped. 1: eassumption.
  intros n hn.
  induction k as [| k ih] in n, hn |- *. 1: lia.
  cbn. destruct n.
  - reflexivity.
  - cbn. unfold core.funcomp. rewrite ih. 2: lia.
    reflexivity.
Qed.

Lemma subst_instance_ext σ θ ξ :
  (∀ n, σ n = θ n) →
  subst_instance σ ξ = subst_instance θ ξ.
Proof.
  intros h.
  apply map_ext. intro.
  apply option_map_ext. intro.
  apply ext_term. assumption.
Qed.

Lemma ren_subst_instance ρ σ ξ :
  ren_instance ρ (subst_instance σ ξ) = subst_instance (σ >> (ren_term ρ)) ξ.
Proof.
  rewrite map_map. apply map_ext. intro.
  rewrite option_map_option_map. apply option_map_ext. intro.
  rasimpl. reflexivity.
Qed.

Lemma subst_ren_instance ρ σ ξ :
  subst_instance σ (ren_instance ρ ξ) = subst_instance (ρ >> σ) ξ.
Proof.
  rewrite map_map. apply map_ext. intro.
  rewrite option_map_option_map. apply option_map_ext. intro.
  rasimpl. reflexivity.
Qed.

Corollary liftn_subst_instance n σ ξ :
  liftn n (subst_instance σ ξ) = subst_instance (ups n σ) (liftn n ξ).
Proof.
  rewrite subst_ren_instance. rewrite ren_subst_instance.
  apply subst_instance_ext. intro m.
  unfold core.funcomp.
  induction n as [| n ih] in m, σ |- *.
  - cbn. rasimpl. reflexivity.
  - cbn. unfold core.funcomp. rewrite <- ih.
    rasimpl. reflexivity.
Qed.

Lemma inst_equations_subst_ih Σ Ξ σ ξ Ξ' :
  inst_equations Σ Ξ ξ Ξ' →
  inst_equations_ (λ u v, ∀ σ, Σ ;; Ξ ⊢ u <[ σ ] ≡ v <[ σ ]) ξ Ξ' →
  inst_equations Σ Ξ (subst_instance σ ξ) Ξ'.
Proof.
  intros h ih.
  intros x rl hx m. specialize (ih _ _ hx).
  cbn in ih. fold m in ih. destruct ih as (e & hl & hr & ih).
  specialize ih with (σ := ups m σ).
  cbn.
  rewrite !liftn_subst_instance.
  erewrite 2!subst_inst_ups in ih. 2,3: eassumption.
  rewrite nth_error_map. rewrite e.
  intuition eauto.
Qed.

(** Note:

  It is a bit silly because the context is ignored for conversion (for now).

*)
Lemma conv_subst Σ Ξ σ u v :
  Σ ;; Ξ ⊢ u ≡ v →
  Σ ;; Ξ ⊢ u <[ σ ] ≡ v <[ σ ].
Proof.
  intros h.
  induction h using conversion_ind in σ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto ].
  - rasimpl. eapply meta_conv_trans_r. 1: econstructor.
    rasimpl. reflexivity.
  - cbn. eapply meta_conv_trans_r.
    1:{ econstructor. 1,3: eassumption. 1: eauto using inst_equations_subst_ih. }
    symmetry. apply subst_inst_closed. assumption.
  - cbn. constructor.
    apply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros l l' h.
    apply option_rel_map_l, option_rel_map_r.
    eapply option_rel_impl. 2: eassumption.
    cbn. auto.
Qed.

Lemma scoped_subst σ k t :
  scoped k t = true →
  t <[ ups k σ ] = t.
Proof.
  intros h.
  induction t using term_rect in k, σ, h |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn ;
    apply andb_prop in h as [] ;
    change (up_term_term (ups ?k ?σ)) with (ups (S k) σ) ;
    f_equal ;
    eauto
  ].
  - cbn - ["<?"] in *.
    apply ups_below.
    apply Nat.ltb_lt. assumption.
  - cbn in *. f_equal.
    rewrite <- map_id. apply map_ext_All.
    apply forallb_All in h. move h at top.
    eapply All_prod in h. 2: eassumption.
    eapply All_impl. 2: eassumption. clear.
    cbn. intros ? [h1 h2].
    change @core.option_map with option_map.
    apply option_map_id_onSomeT.
    apply onSomeb_onSome, onSome_onSomeT in h2.
    eapply onSomeT_prod in h1. 2: eassumption.
    eapply onSomeT_impl. 2: eassumption. clear.
    cbn. intros t [h1 h2]. eauto.
Qed.

Corollary closed_subst σ t :
  closed t = true →
  t <[ σ ] = t.
Proof.
  intros h.
  eapply scoped_subst in h. eauto.
Qed.

Lemma subst_instance_id ξ :
  subst_instance ids ξ = ξ.
Proof.
  rewrite <- map_id. apply map_ext. intro.
  rewrite <- option_map_id. apply option_map_ext. intro.
  rasimpl. reflexivity.
Qed.

Lemma closed_subst_instance σ ξ :
  closed_instance ξ = true →
  subst_instance σ ξ = ξ.
Proof.
  intros h.
  etransitivity. 2: apply subst_instance_id.
  apply map_ext_All. eapply All_impl.
  2:{ apply forallb_All. eassumption. }
  cbn. intros ? ho%onSomeb_onSome%onSome_onSomeT.
  apply option_map_ext_onSomeT. eapply onSomeT_impl. 2: eassumption.
  cbn. rasimpl. apply closed_subst.
Qed.

Lemma closed_lift_instance ξ :
  closed_instance ξ = true →
  closed_instance (lift_instance ξ) = true.
Proof.
  intro h.
  rewrite closed_ren_instance. all: assumption.
Qed.

Lemma scoped_upwards k l t :
  scoped k t = true →
  k ≤ l →
  scoped l t = true.
Proof.
  intros ht hkl.
  induction t using term_rect in k, l, ht, hkl |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn in * ; rewrite Bool.andb_true_iff in * ;
    intuition eauto with arith
  ].
  - cbn - ["<?"] in *. rewrite Nat.ltb_lt in *. lia.
  - cbn in *. apply All_forallb. apply forallb_All in ht.
    move ht at top. eapply All_prod in ht. 2: eassumption.
    eapply All_impl. 2: eassumption.
    cbn. intros ? [h1 h2]. apply onSomeb_onSome, onSomeT_onSome.
    apply onSomeb_onSome, onSome_onSomeT in h2.
    eapply onSomeT_prod in h1. 2: eassumption.
    eapply onSomeT_impl. 2: eassumption.
    cbn. intros ? []. eauto.
Qed.

Lemma uprens_below k ρ n :
  n < k →
  uprens k ρ n = n.
Proof.
  intro h.
  induction k as [| k ih] in n, ρ, h |- *. 1: lia.
  cbn. destruct n as [| ].
  - reflexivity.
  - cbn. core.unfold_funcomp. rewrite ih. 2: lia.
    reflexivity.
Qed.

Lemma uprens_above k ρ n :
  uprens k ρ (k + n) = k + ρ n.
Proof.
  induction k as [| k ih] in n |- *.
  - cbn. rasimpl. reflexivity.
  - cbn. core.unfold_funcomp. rewrite ih.
    rasimpl. reflexivity.
Qed.

Lemma scoped_lift_gen k l t m :
  scoped (m + l) t = true →
  scoped (m + k + l) (uprens m (plus k) ⋅ t) = true.
Proof.
  intros h.
  induction t using term_rect in m, k, l, h |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn in * ; rewrite Bool.andb_true_iff in * ;
    (* rewrite Nat.ltb_lt in * ; *)
    intuition eauto with arith
  ].
  - cbn - ["<=?"] in *. rewrite Nat.ltb_lt in *.
    destruct (lt_dec n m).
    + rewrite uprens_below. 2: assumption.
      lia.
    + pose (p := n - m). replace n with (m + p) by lia.
      rewrite uprens_above. lia.
  - cbn in *. rewrite Bool.andb_true_iff in *.
    intuition eauto.
    change (upRen_term_term (uprens m ?ρ)) with (uprens (S m) ρ).
    change (S (m + k + l)) with (S m + k + l).
    eauto.
  - cbn in *. rewrite Bool.andb_true_iff in *.
    intuition eauto.
    change (upRen_term_term (uprens m ?ρ)) with (uprens (S m) ρ).
    change (S (m + k + l)) with (S m + k + l).
    eauto.
  - cbn in *. apply forallb_All in h. move h at top.
    eapply All_prod in h. 2: eassumption.
    apply All_forallb. apply All_map. eapply All_impl. 2: eassumption.
    clear.
    cbn. intros σ [h1 h2].
    apply onSomeb_onSome, onSomeT_onSome. apply onSomeT_map.
    apply onSomeb_onSome, onSome_onSomeT in h2.
    eapply onSomeT_prod in h1. 2: eassumption.
    eapply onSomeT_impl. 2: eassumption. clear.
    cbn. intros t [h1 h2]. eauto.
Qed.

Lemma scoped_lift k l t :
  scoped l t = true →
  scoped (k + l) (plus k ⋅ t) = true.
Proof.
  intros h.
  eapply scoped_lift_gen with (m := 0).
  assumption.
Qed.

Lemma scoped_inst k l ξ t :
  scoped_instance l ξ = true →
  scoped k t = true →
  scoped (k + l) (inst (liftn k ξ) t) = true.
Proof.
  intros hξ ht.
  induction t using term_rect in k, l, ξ, ht, hξ |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn in * ; rewrite Bool.andb_true_iff in * ;
    (* rewrite Nat.ltb_lt in * ; *)
    intuition eauto with arith
  ].
  - cbn - ["<=?"] in *.
    rewrite Nat.ltb_lt in *. eauto with arith.
  - cbn in *. rewrite Bool.andb_true_iff in *.
    intuition eauto.
    rewrite lift_liftn. change (S (k + l)) with (S k + l). eauto.
  - cbn in *. rewrite Bool.andb_true_iff in *.
    intuition eauto.
    rewrite lift_liftn. change (S (k + l)) with (S k + l). eauto.
  - cbn in *. apply forallb_All in ht. move ht at top.
    eapply All_prod in ht. 2: eassumption.
    apply All_forallb. apply All_map. eapply All_impl. 2: eassumption.
    clear - hξ.
    cbn. intros o [h1 h2].
    apply onSomeb_onSome, onSomeT_onSome. apply onSomeT_map.
    apply onSomeb_onSome, onSome_onSomeT in h2.
    eapply onSomeT_prod in h1. 2: eassumption.
    eapply onSomeT_impl. 2: eassumption. clear - hξ.
    cbn. intros t [h1 h2]. eauto.
  - cbn. rewrite iget_ren. unfold iget.
    destruct nth_error as [[t|] |] eqn: hx. 2,3: reflexivity.
    apply nth_error_In in hx.
    rewrite forallb_forall in hξ. specialize hξ with (1 := hx).
    eapply scoped_lift. assumption.
Qed.

Corollary scoped_inst_closed k ξ t :
  scoped_instance k ξ = true →
  closed t = true →
  scoped k (inst ξ t) = true.
Proof.
  intros hξ ht.
  eapply scoped_inst in hξ. 2: eassumption.
  cbn in hξ. rewrite ren_instance_id in hξ. assumption.
Qed.

Corollary closed_inst ξ t :
  closed_instance ξ = true →
  closed t = true →
  closed (inst ξ t) = true.
Proof.
  intros hξ ht.
  apply scoped_inst_closed. all: assumption.
Qed.

Lemma inst_typing_subst Σ Ξ Δ Γ σ ξ Ξ' :
  styping Σ Ξ Δ σ Γ →
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ Γ t A,
    ∀ Δ σ, styping Σ Ξ Δ σ Γ → Σ ;; Ξ | Δ ⊢ t <[ σ ] : A <[ σ ]
  ) Γ ξ Ξ' →
  inst_typing Σ Ξ Δ (subst_instance σ ξ) Ξ'.
Proof.
  intros hσ [h1 [h2 h3]] [ih1 [ih2 ih3]].
  split. 2: split.
  - eauto using inst_equations_subst_ih, inst_equations_prop, conv_subst.
  - intros x A hx. specialize (ih2 _ _ hx) as [? ih2].
    split. 1: assumption.
    rewrite iget_subst. eapply meta_conv.
    + eauto.
    + apply subst_inst_closed. assumption.
  - rewrite length_map. assumption.
Qed.

Lemma typing_subst Σ Ξ Γ Δ σ t A :
  styping Σ Ξ Δ σ Γ →
  Σ ;; Ξ | Γ ⊢ t : A →
  Σ ;; Ξ | Δ ⊢ t <[ σ ] : A <[ σ ].
Proof.
  intros hσ ht.
  induction ht using typing_ind in Δ, σ, hσ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto using styping_up ].
  - rasimpl.
    induction hσ in x, H |- *. 1: destruct x ; discriminate.
    destruct x.
    + cbn in H. inversion H. subst. assumption.
    + apply IHhσ. assumption.
  - rasimpl. eapply meta_conv.
    + cbn in *. econstructor ; eauto using styping_up.
    + rasimpl. reflexivity.
  - cbn. eapply meta_conv.
    + econstructor. 1,3: eassumption.
      eapply inst_typing_subst. all: eassumption.
    + symmetry. apply subst_inst_closed. assumption.
  - cbn. rewrite closed_subst. 2: assumption.
    econstructor. all: eassumption.
  - econstructor. 1,3: eauto.
    eapply conv_subst. eassumption.
Qed.

(** Instances preserve conversion and typing *)

Lemma nth_error_ctx_inst ξ Γ x :
  nth_error (ctx_inst ξ Γ) x =
  option_map (inst (ren_instance (plus (length Γ - S x)) ξ)) (nth_error Γ x).
Proof.
  induction Γ in ξ, x |- *.
  - cbn. rewrite nth_error_nil. reflexivity.
  - destruct x as [| x].
    + cbn. replace (length Γ - 0) with (length Γ) by lia.
      reflexivity.
    + cbn. eauto.
Qed.

Lemma ctx_inst_app ξ Γ Δ :
  ctx_inst ξ (Γ ,,, Δ) = ctx_inst ξ Γ ,,, ctx_inst (liftn (length Γ) ξ) Δ.
Proof.
  induction Δ as [| A Δ ih] in Γ |- *.
  - reflexivity.
  - cbn. f_equal. 2: eauto.
    rewrite liftn_liftn. rewrite length_app. reflexivity.
Qed.

Lemma inst_get ξ ξ' x :
  inst ξ (iget ξ' x) = iget (inst_instance ξ ξ') x.
Proof.
  unfold iget. rewrite nth_error_map.
  destruct nth_error as [[]|]. all: reflexivity.
Qed.

Lemma inst_inst ξ ξ' t :
  inst ξ (inst ξ' t) = inst (inst_instance ξ ξ') t.
Proof.
  induction t using term_rect in ξ, ξ' |- *.
  all: try solve [ cbn ; f_equal ; eauto ].
  - cbn. f_equal. 1: eauto.
    rewrite IHt2. f_equal.
    rewrite !map_map. apply map_ext. intro o.
    rewrite !option_map_option_map. apply option_map_ext. intro t.
    symmetry. apply ren_inst.
  - cbn. f_equal. 1: eauto.
    rewrite IHt2. f_equal.
    rewrite !map_map. apply map_ext. intro o.
    rewrite !option_map_option_map. apply option_map_ext. intro t.
    symmetry. apply ren_inst.
  - cbn. f_equal.
    rewrite !map_map. apply map_ext_All.
    eapply All_impl. 2: eassumption.
    intros o ho.
    rewrite !option_map_option_map. apply option_map_ext_onSomeT.
    eapply onSomeT_impl. 2: eassumption.
    auto.
  - cbn. apply inst_get.
Qed.

Lemma liftn_inst_instance n ξ ξ' :
  liftn n (inst_instance ξ ξ') = inst_instance (liftn n ξ) (liftn n ξ').
Proof.
  rewrite !map_map. apply map_ext. intro.
  rewrite !option_map_option_map. apply option_map_ext. intro.
  rewrite ren_inst. reflexivity.
Qed.

Lemma ctx_inst_comp ξ ξ' Γ :
  ctx_inst ξ (ctx_inst ξ' Γ) = ctx_inst (inst_instance ξ ξ') Γ.
Proof.
  induction Γ as [| A Γ ih].
  - reflexivity.
  - cbn. rewrite ih. f_equal. rewrite inst_inst. f_equal.
    rewrite length_ctx_inst.
    rewrite liftn_inst_instance. reflexivity.
Qed.

Lemma inst_equations_inst_ih Σ Ξ Ξ' Ξ'' k ξ ξ' :
  inst_equations Σ Ξ ξ Ξ' →
  inst_equations Σ Ξ' ξ' Ξ'' →
  inst_equations_ (λ u v,
    ∀ Ξ p ξ,
      inst_equations Σ Ξ ξ Ξ' →
      Σ ;; Ξ ⊢ inst (liftn p ξ) u ≡ inst (liftn p ξ) v
  ) ξ' Ξ'' →
  inst_equations Σ Ξ (inst_instance (liftn k ξ) ξ') Ξ''.
Proof.
  intros hξ h ih.
  intros x rl hx m. specialize (ih _ _ hx) as (e & hl & hr & ih).
  cbn in *. fold m in ih.
  specialize ih with (1 := hξ) (p := m + k).
  rewrite !inst_inst in ih.
  rewrite liftn_inst_instance.
  rewrite liftn_liftn.
  rewrite nth_error_map, e. cbn.
  intuition eauto.
Qed.

Lemma conv_inst Σ Ξ Ξ' k u v ξ :
  inst_equations Σ Ξ ξ Ξ' →
  Σ ;; Ξ' ⊢ u ≡ v →
  let rξ := liftn k ξ in
  Σ ;; Ξ ⊢ inst rξ u ≡ inst rξ v.
Proof.
  intros hξ h. cbn.
  induction h using conversion_ind in Ξ, k, ξ, hξ |- *.
  all: try solve [ cbn ; econstructor ; eauto ].
  - cbn. rewrite subst_inst with (m := S k). 2: auto.
    eapply meta_conv_trans_r. 1: constructor.
    cbn. rewrite lift_liftn. apply ext_term. intros []. all: reflexivity.
  - cbn. eapply meta_conv_trans_r.
    1:{
      eapply conv_unfold. 1,3: eassumption.
      eauto using inst_equations_inst_ih.
    }
    rewrite inst_inst. reflexivity.
  - erewrite ext_term_scoped. 3: eapply eq_subst_trunc. 2: eassumption.
    erewrite (ext_term_scoped _ rhs).
    3: eapply eq_subst_trunc. 2: eassumption.
    erewrite 2!subst_inst. 2,3: eapply trunc_bounds.
    eapply conv_subst. eapply hξ. eassumption.
  - cbn. constructor. 1: eauto.
    rewrite lift_liftn.
    apply IHh2. assumption.
  - cbn. constructor. 1: eauto.
    rewrite lift_liftn.
    apply IHh2. assumption.
  - cbn. constructor.
    apply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros l l' h.
    apply option_rel_map_l, option_rel_map_r.
    eapply option_rel_impl. 2: eassumption.
    cbn. auto.
Qed.

Corollary conv_inst_closed Σ Ξ Ξ' u v ξ :
  inst_equations Σ Ξ ξ Ξ' →
  Σ ;; Ξ' ⊢ u ≡ v →
  Σ ;; Ξ ⊢ inst ξ u ≡ inst ξ v.
Proof.
  intros hξ h.
  eapply conv_inst with (k := 0) in h. 2: eassumption.
  cbn in h. rewrite ren_instance_id_ext in h. 2: auto.
  assumption.
Qed.

Lemma typing_inst Σ Ξ Ξ' Γ Δ t A ξ :
  inst_typing Σ Ξ Δ ξ Ξ' →
  Σ ;; Ξ' | Γ ⊢ t : A →
  let rξ := liftn (length Γ) ξ in
  Σ ;; Ξ | Δ ,,, ctx_inst ξ Γ ⊢ inst rξ t : inst rξ A.
Proof.
  intros hξ ht rξ.
  induction ht using typing_ind in Ξ, Δ, ξ, rξ, hξ |- *.
  all: try solve [ cbn ; econstructor ; eauto ].
  - cbn. eapply meta_conv.
    + econstructor. rewrite nth_error_app1.
      2:{ rewrite length_ctx_inst. eapply nth_error_Some. congruence. }
      rewrite nth_error_ctx_inst.
      rewrite H. cbn. reflexivity.
    + rewrite ren_inst. f_equal.
      rewrite liftn_liftn.
      apply ren_instance_ext.
      cbn. intro.
      pose proof (nth_error_Some Γ x) as e%proj1.
      forward e by congruence.
      lia.
  - cbn. constructor. 1: eauto.
    subst rξ. rewrite ren_instance_comp. apply IHht2. assumption.
  - cbn. econstructor. 1: eauto.
    + subst rξ. rewrite ren_instance_comp. apply IHht2. assumption.
    + subst rξ. rewrite ren_instance_comp. apply IHht3. assumption.
  - cbn. eapply meta_conv.
    + cbn in *. econstructor. all: eauto.
      subst rξ. rewrite ren_instance_comp. apply IHht4. assumption.
    + rasimpl.
      subst rξ. erewrite subst_inst with (m := S (length Γ)).
      2:{ cbn. auto. }
      rewrite lift_liftn.
      apply ext_term. intros []. all: reflexivity.
  - cbn. eapply meta_conv.
    + econstructor. 1,3: eassumption.
      destruct H1 as [? [? ?]].
      split. 2: split.
      * destruct hξ as (? & ? & ?).
        eauto using inst_equations_inst_ih, inst_equations_prop, conv_inst.
      * rename H3 into ih2.
        intros x B hx. specialize (ih2 _ _ hx) as [? ih2].
        split. 1: assumption.
        rewrite <- inst_get. rewrite <- inst_inst.
        eauto.
      * rewrite length_map. assumption.
    + rewrite inst_inst. reflexivity.
  - cbn. subst rξ. rewrite iget_ren.
    eapply meta_conv.
    + eapply typing_ren.
      1:{ erewrite <- length_ctx_inst. eapply rtyping_add. }
      eapply hξ. eassumption.
    + rewrite ren_inst. f_equal.
      apply closed_ren. assumption.
  - econstructor. 1,3: eauto.
    eapply conv_inst. 2: eassumption.
    apply hξ.
Qed.

Corollary typing_inst_closed Σ Ξ Ξ' Γ t A ξ :
  inst_typing Σ Ξ Γ ξ Ξ' →
  Σ ;; Ξ' | ∙ ⊢ t : A →
  Σ ;; Ξ | Γ ⊢ inst ξ t : inst ξ A.
Proof.
  intros hξ h.
  eapply typing_inst in h. 2: eassumption.
  cbn in h.
  rewrite ren_instance_id_ext in h. 2: auto.
  assumption.
Qed.

Lemma conv_insts Σ Ξ t ξ ξ' :
  Forall2 (option_rel (conversion Σ Ξ)) ξ ξ' →
  Σ ;; Ξ ⊢ inst ξ t ≡ inst ξ' t.
Proof.
  intros hξ.
  induction t using term_rect in ξ, ξ', hξ |- *.
  all: try solve [ cbn ; ttconv ].
  - cbn. eapply cong_Pi. 1: eauto.
    eapply IHt2. eapply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros.
    eapply option_rel_map_l, option_rel_map_r.
    eapply option_rel_impl. 2: eassumption.
    intros. eapply conv_ren. eassumption.
  - cbn. eapply cong_lam. 1: eauto.
    eapply IHt2. eapply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros.
    eapply option_rel_map_l, option_rel_map_r.
    eapply option_rel_impl. 2: eassumption.
    intros. eapply conv_ren. eassumption.
  - cbn. eapply cong_const.
    eapply Forall2_map_l, Forall2_map_r.
    eapply Forall2_diag. eapply All_Forall.
    eapply All_impl. 2: eassumption.
    intros.
    eapply option_rel_map_l, option_rel_map_r.
    eapply option_rel_diag. rewrite OnSome_onSome. apply onSomeT_onSome.
    eapply onSomeT_impl. 2: eassumption.
    cbn. intros. eauto.
  - cbn. unfold iget. destruct (nth_error ξ _) as [o1 |] eqn:e1.
    2:{
      destruct (nth_error ξ' _) eqn:e2.
      1:{
        eapply nth_error_None in e1. eapply Forall2_length in hξ.
        rewrite hξ in e1. rewrite <- nth_error_None in e1. congruence.
      }
      ttconv.
    }
    eapply Forall2_nth_error_l in e1 as e2. 2: eassumption.
    destruct e2 as (o2 & e2 & h). rewrite e2.
    destruct h. 1: ttconv.
    assumption.
Qed.

Lemma cong_inst Σ Ξ u v ξ ξ' Ξ' :
  inst_equations Σ Ξ ξ Ξ' →
  Σ ;; Ξ' ⊢ u ≡ v →
  Forall2 (option_rel (conversion Σ Ξ)) ξ ξ' →
  Σ ;; Ξ ⊢ inst ξ u ≡ inst ξ' v.
Proof.
  intros hξ h hh.
  eapply conv_trans.
  - eapply conv_inst_closed. all: eassumption.
  - eapply conv_insts. assumption.
Qed.

(** Extension environement weakening *)

Lemma ictx_get_weak d Ξ M i :
  ictx_get Ξ M = Some i →
  ictx_get (d :: Ξ) M = Some i.
Proof.
  apply lvl_get_weak.
Qed.

Lemma conv_eweak Σ Ξ d u v :
  Σ ;; Ξ ⊢ u ≡ v →
  Σ ;; d :: Ξ ⊢ u ≡ v.
Proof.
  intros h. induction h using conversion_ind.
  all: try solve [ econstructor ; eauto ].
  econstructor. 2-3: eauto.
  apply ictx_get_weak. eassumption.
Qed.

Lemma inst_equations_eweak Σ Ξ d ξ Ξ' :
  inst_equations Σ Ξ ξ Ξ' →
  inst_equations Σ (d :: Ξ) ξ Ξ'.
Proof.
  intros h.
  intros x rl hx. specialize (h _ _ hx).
  cbn in *. intuition eauto using conv_eweak.
Qed.

Lemma inst_iget_eweak Σ Ξ d Γ ξ Ξ' :
  inst_iget Σ Ξ Γ ξ Ξ' →
  inst_iget_ (λ Γ t A, Σ ;; d :: Ξ | Γ ⊢ t : A) Γ ξ Ξ' →
  inst_iget Σ (d :: Ξ) Γ ξ Ξ'.
Proof.
  intros h ih.
  intros x A hx. specialize (ih _ _ hx) as [? ih].
  split. 1: assumption.
  eauto.
Qed.

Lemma inst_typing_eweak_ Σ Ξ d Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ Γ t A, Σ ;; d :: Ξ | Γ ⊢ t : A) Γ ξ Ξ' →
  inst_typing Σ (d :: Ξ) Γ ξ Ξ'.
Proof.
  intros [h1 [h2 h3]] [ih1 [ih2 ih3]].
  split. 2: split.
  - eapply inst_equations_eweak. all: eassumption.
  - eapply inst_iget_eweak. all: eassumption.
  - assumption.
Qed.

Lemma typing_eweak Σ Ξ d Γ t A :
  Σ ;; Ξ | Γ ⊢ t : A →
  Σ ;; d :: Ξ | Γ ⊢ t : A.
Proof.
  intros h. induction h using typing_ind.
  all: try solve [ econstructor ; eauto ].
  - econstructor. 1,3: eauto.
    eapply inst_typing_eweak_. all: eassumption.
  - econstructor. 2: assumption.
    eapply ictx_get_weak. assumption.
  - econstructor. 1,3: eassumption.
    eapply conv_eweak. assumption.
Qed.

Lemma inst_typing_eweak Σ Ξ d Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing Σ (d :: Ξ) Γ ξ Ξ'.
Proof.
  intros h.
  eapply inst_typing_eweak_. 1: eassumption.
  destruct h as [h1 [h2 h3]]. split. 2: split.
  - assumption.
  - intros x A hx. specialize (h2 _ _ hx) as [? ih].
    split. 1: assumption.
    eauto using typing_eweak.
  - assumption.
Qed.

Lemma wf_eweak Σ Ξ d Γ :
  wf Σ Ξ Γ →
  wf Σ (d :: Ξ) Γ.
Proof.
  intros h. induction h.
  - constructor.
  - econstructor.
    + assumption.
    + eapply typing_eweak. eassumption.
Qed.

Lemma equation_typing_eweak Σ Ξ d r :
  equation_typing Σ Ξ r →
  equation_typing Σ (d :: Ξ) r.
Proof.
  intros (hctx & [i hty] & hl & hr).
  unfold equation_typing.
  intuition eauto using typing_eweak, wf_eweak.
Qed.

(** Global environment weakening *)

Lemma inst_equations_gweak_ih Σ Σ' Ξ ξ Ξ' :
  Σ ⊑ Σ' →
  inst_equations_ (λ u v, Σ' ;; Ξ ⊢ u ≡ v) ξ Ξ' →
  inst_equations Σ' Ξ ξ Ξ'.
Proof.
  intros hle ih.
  intros x rl hx. specialize (ih _ _ hx).
  intuition eauto.
Qed.

Lemma conv_gweak Σ Σ' Ξ u v :
  Σ ;; Ξ ⊢ u ≡ v →
  Σ ⊑ Σ' →
  Σ' ;; Ξ ⊢ u ≡ v.
Proof.
  intros h hle. induction h using conversion_ind.
  all: solve [ econstructor ; eauto ].
Qed.

Lemma inst_equations_gweak Σ Σ' Ξ ξ Ξ' :
  inst_equations Σ Ξ ξ Ξ' →
  Σ ⊑ Σ' →
  inst_equations Σ' Ξ ξ Ξ'.
Proof.
  intros h hle.
  eauto using inst_equations_gweak_ih, inst_equations_prop, conv_gweak.
Qed.

Lemma inst_iget_gweak Σ Σ' Ξ Γ ξ Ξ' :
  inst_iget Σ Ξ Γ ξ Ξ' →
  inst_iget_ (λ Γ t A, Σ' ;; Ξ | Γ ⊢ t : A) Γ ξ Ξ' →
  Σ ⊑ Σ' →
  inst_iget Σ' Ξ Γ ξ Ξ'.
Proof.
  intros h ih hle. auto.
Qed.

Lemma inst_typing_gweak_ Σ Σ' Ξ Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ Γ t A, Σ' ;; Ξ | Γ ⊢ t : A) Γ ξ Ξ' →
  Σ ⊑ Σ' →
  inst_typing Σ' Ξ Γ ξ Ξ'.
Proof.
  intros [h1 [h2 h3]] [ih1 [ih2 ih3]] hle.
  split. 2: split.
  - eapply inst_equations_gweak. all: eassumption.
  - eapply inst_iget_gweak. 3: eassumption. all: eassumption.
  - assumption.
Qed.

Lemma typing_gweak Σ Σ' Ξ Γ t A :
  Σ ;; Ξ | Γ ⊢ t : A →
  Σ ⊑ Σ' →
  Σ' ;; Ξ | Γ ⊢ t : A.
Proof.
  intros h hle. induction h using typing_ind.
  all: try solve [ econstructor ; eauto ].
  - econstructor. 1,3: eauto.
    eapply inst_typing_gweak_. all: eassumption.
  - econstructor. 1,3: eassumption.
    eapply conv_gweak. all: eauto.
Qed.

Lemma inst_typing_gweak Σ Σ' Ξ Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  Σ ⊑ Σ' →
  inst_typing Σ' Ξ Γ ξ Ξ'.
Proof.
  intros h hle.
  eapply inst_typing_gweak_. 1,3: eassumption.
  destruct h as [h1 [h2 h3]]. split. 2: split.
  - assumption.
  - intros x A hx. specialize (h2 _ _ hx) as [? h2].
    split. 1: assumption.
    eauto using typing_gweak.
  - assumption.
Qed.

Lemma gscope_gweak Σ Σ' t :
  gscope Σ t →
  Σ ⊑ Σ' →
  gscope Σ' t.
Proof.
  intros h hle.
  induction h using gscope_ind.
  all: solve [ econstructor ; eauto ].
Qed.

Lemma gscope_crule_gweak Σ Σ' rl :
  gscope_crule Σ rl →
  Σ ⊑ Σ' →
  gscope_crule Σ' rl.
Proof.
  intros h hle.
  destruct h. split.
  all: intuition eauto using Forall_impl, gscope_gweak.
Qed.

Lemma wf_gweak Σ Σ' Ξ Γ :
  wf Σ Ξ Γ →
  Σ ⊑ Σ' →
  wf Σ' Ξ Γ.
Proof.
  intros h hle. induction h.
  - constructor.
  - econstructor.
    + assumption.
    + eapply typing_gweak. all: eassumption.
Qed.

Lemma equation_typing_gweak Σ Σ' Ξ r :
  equation_typing Σ Ξ r →
  Σ ⊑ Σ' →
  equation_typing Σ' Ξ r.
Proof.
  intros (hctx & [i hty] & hl & hr) hle.
  unfold equation_typing.
  intuition eauto using typing_gweak, wf_gweak.
Qed.

Lemma iwf_gweak Σ Σ' Ξ :
  iwf Σ Ξ →
  Σ ⊑ Σ' →
  iwf Σ' Ξ.
Proof.
  intros h hle. induction h.
  - constructor.
  - econstructor. 1: assumption.
    eapply typing_gweak. all: eassumption.
  - econstructor.
    + assumption.
    + eapply gscope_crule_gweak. all: eassumption.
    + eapply equation_typing_gweak. all: eassumption.
Qed.

Lemma wf_rules_gweak Σ Σ' Ξ R :
  Forall (equation_typing Σ Ξ) R →
  Σ ⊑ Σ' →
  Forall (equation_typing Σ' Ξ) R.
Proof.
  intros h hle.
  eapply Forall_impl. 2: eassumption.
  intros. eauto using equation_typing_gweak.
Qed.

(** Validity (or presupposition) *)

Lemma styping_ids Σ Ξ Γ :
  styping Σ Ξ Γ ids Γ.
Proof.
  induction Γ as [| A Γ ih].
  - constructor.
  - constructor.
    + eapply styping_weak with (A := A) in ih.
      assumption.
    + eapply meta_conv.
      * econstructor. cbn. reflexivity.
      * rasimpl. substify. reflexivity.
Qed.

Lemma styping_one Σ Ξ Γ A u :
    Σ ;; Ξ | Γ ⊢ u : A →
    styping Σ Ξ Γ u.. (Γ ,, A).
Proof.
  intros h.
  constructor. all: rasimpl. 2: auto.
  erewrite autosubst_simpl_styping. 2: exact _. (* Somehow rasimpl doesn't work *)
  apply styping_ids.
Qed.

Lemma valid_wf Σ Ξ Γ x A :
  wf Σ Ξ Γ →
  nth_error Γ x = Some A →
  ∃ i, Σ ;; Ξ | Γ ⊢ (plus (S x)) ⋅ A : Sort i.
Proof.
  intros hΓ h.
  induction hΓ as [| Γ i B hΓ ih hB] in x, h |- *.
  1: destruct x ; discriminate.
  destruct x.
  + cbn in *. inversion h. subst.
    exists i. rasimpl.
    eapply meta_conv.
    * eapply typing_ren. 1: eapply rtyping_S.
      eassumption.
    * reflexivity.
  + cbn in h. eapply ih in h as [j h]. exists j.
    eapply typing_ren in h. 2: eapply rtyping_S.
    rasimpl in h. eassumption.
Qed.

Lemma ictx_get_case d Ξ M i :
  ictx_get (d :: Ξ) M = Some i →
  (M = length Ξ ∧ d = i) ∨ (ictx_get Ξ M = Some i).
Proof.
  intro h.
  unfold ictx_get in h.
  destruct (_ <=? _) eqn: e. 1: discriminate.
  rewrite Nat.leb_gt in e. cbn in e.
  cbn in h.
  destruct (length Ξ - M) eqn: e'.
  - left. cbn in h. inversion h.
    intuition lia.
  - right. cbn in h.
    unfold ictx_get.
    destruct (_ <=? _) eqn: e2.
    1:{ rewrite Nat.leb_le in e2. lia. }
    rewrite <- h. f_equal. lia.
Qed.

Lemma valid_assm Σ Ξ x A :
  iwf Σ Ξ →
  ictx_get Ξ x = Some (Assm A) →
  ∃ i, Σ ;; Ξ | ∙ ⊢ A : Sort i.
Proof.
  intros hΞ e.
  induction hΞ as [| B Ξ i hΞ ih hB | rl Ξ hΞ ih hs ht ].
  - destruct x. all: discriminate.
  - eapply ictx_get_case in e as eh. destruct eh as [[-> eh] | eh].
    + inversion eh. subst.
      eexists. eapply typing_eweak. eassumption.
    + specialize (ih eh) as [].
      eexists. eapply typing_eweak. eassumption.
  - eapply ictx_get_case in e as eh. destruct eh as [[-> eh] | eh].
    1: discriminate.
    specialize (ih eh) as [].
    eexists. eapply typing_eweak. eassumption.
Qed.

Lemma valid_comp Σ Ξ x rl :
  iwf Σ Ξ →
  ictx_get Ξ x = Some (Comp rl) →
  gscope_crule Σ rl ∧ equation_typing Σ Ξ (crule_eq rl).
Proof.
  intros hΞ e.
  induction hΞ as [| B Ξ i hΞ ih hB | rl' Ξ hΞ ih hs ht ].
  - destruct x. all: discriminate.
  - eapply ictx_get_case in e as eh. destruct eh as [[-> eh] | eh].
    1: discriminate.
    intuition eauto using equation_typing_eweak.
  - eapply ictx_get_case in e as eh. destruct eh as [[-> eh] | eh].
    + inversion eh. subst.
      intuition eauto using equation_typing_eweak.
    + specialize (ih eh) as [].
      intuition eauto using equation_typing_eweak.
Qed.

Lemma extends_nil Σ :
  [] ⊑ Σ.
Proof.
  intros ?? e. discriminate.
Qed.

Lemma extends_gcons (Σ : gctx) c d :
  Σ c = None →
  Σ ⊑ (c, d) :: Σ.
Proof.
  intros h. intros c' d' e.
  cbn. destruct (_ =? _)%string eqn:ec.
  - apply eqb_eq in ec. subst. congruence.
  - assumption.
Qed.

Lemma valid_def Σ c Ξ A t :
  gwf Σ →
  Σ c = Some (Def Ξ A t) →
  iwf Σ Ξ ∧
  (∃ i, Σ ;; Ξ | ∙ ⊢ A : Sort i) ∧
  Σ ;; Ξ | ∙ ⊢ t : A.
Proof.
  intros hΣ hc.
  induction hΣ as [ | c' ??????? ih ] in c, Ξ, A, t, hc |- *.
  - discriminate.
  - cbn in hc. destruct (c =? c')%string.
    + inversion hc. subst.
      intuition eauto using iwf_gweak, typing_gweak, extends_gcons.
    + specialize ih with (1 := hc) as [? [[j ?] ?]].
      intuition eauto using iwf_gweak, typing_gweak, extends_gcons.
Qed.

Definition styping_alt Σ Ξ (Γ : ctx) (σ : nat → term) (Δ : ctx) :=
  ∀ x A,
    nth_error Δ x = Some A →
    Σ ;; Ξ | Γ ⊢ σ x : ((plus (S x)) ⋅ A) <[ σ ].

Lemma styping_alt_equiv Σ Ξ Γ σ Δ :
  styping Σ Ξ Γ σ Δ ↔ styping_alt Σ Ξ Γ σ Δ.
Proof.
  split.
  - intro h. induction h as [| ???? ih].
    + intros x A e. destruct x. all: discriminate.
    + intros [] B e.
      * rasimpl. cbn in e. inversion e. subst.
        assumption.
      * cbn in e. rasimpl. eapply ih in e. rasimpl in e.
        exact e.
  - intro h. induction Δ as [| A Δ ih] in σ, h |- *.
    1: constructor.
    econstructor.
    + eapply ih.
      intros x B e. rasimpl.
      core.unfold_funcomp.
      specialize (h (S x) _ e). rasimpl in h.
      assumption.
    + specialize (h 0 _ eq_refl). rasimpl in h.
      assumption.
Qed.

Lemma typing_lift_closed Σ Ξ Γ t A :
  Σ ;; Ξ | ∙ ⊢ t : A →
  closed A = true →
  Σ ;; Ξ | Γ ⊢ t : A.
Proof.
  intros h hA.
  eapply typing_scoped in h as ht. cbn in ht.
  eapply typing_ren in h. 2: eapply rtyping_add.
  rewrite !closed_ren in h. 2,3: assumption.
  rewrite app_nil_r in h.
  eassumption.
Qed.

Lemma validity Σ Ξ Γ t A :
  gwf Σ →
  iwf Σ Ξ →
  wf Σ Ξ Γ →
  Σ ;; Ξ | Γ ⊢ t : A →
  ∃ i, Σ ;; Ξ | Γ ⊢ A : Sort i.
Proof.
  intros hΣ hΞ hΓ h.
  induction h using typing_ind in hΓ |- *.
  all: try solve [ eexists ; econstructor ; eauto ].
  - apply valid_wf. all: assumption.
  - eexists. eapply meta_conv.
    + eapply typing_subst.
      * eapply styping_one. eassumption.
      * eassumption.
    + reflexivity.
  - eapply valid_def in hΣ as h. 2: eassumption.
    destruct h as [? [[i ?]]].
    exists i. eapply meta_conv.
    + eapply typing_inst_closed. all: eassumption.
    + reflexivity.
  - eapply valid_assm in hΞ as h. 2: eassumption.
    destruct h as [i hA].
    exists i. eapply typing_lift_closed. 2: reflexivity.
    assumption.
  - eexists. eassumption.
Qed.

(** Induction principle for [typing], threading [wf] *)

Lemma typing_ind_wf :
  ∀ Σ Ξ (P : ctx → term → term → Prop),
    (∀ Γ x A,
      wf Σ Ξ Γ →
      nth_error Γ x = Some A →
      P Γ (var x) (Nat.add (S x) ⋅ A)
    ) →
    (∀ Γ i, wf Σ Ξ Γ → P Γ (Sort i) (Sort (S i))) →
    (∀ Γ i j A B,
      wf Σ Ξ Γ →
      Σ ;; Ξ | Γ ⊢ A : Sort i →
      P Γ A (Sort i) →
      Σ ;; Ξ | Γ,, A ⊢ B : Sort j →
      P (Γ,, A) B (Sort j) →
      P Γ (Pi A B) (Sort (Nat.max i j))
    ) →
    (∀ Γ i j A B t,
      wf Σ Ξ Γ →
      Σ ;; Ξ | Γ ⊢ A : Sort i →
      P Γ A (Sort i) →
      Σ ;; Ξ | Γ,, A ⊢ B : Sort j →
      P (Γ,, A) B (Sort j) →
      Σ ;; Ξ | Γ,, A ⊢ t : B →
      P (Γ,, A) t B → P Γ (lam A t) (Pi A B)
    ) →
    (∀ Γ i j A B t u,
      wf Σ Ξ Γ →
      Σ ;; Ξ | Γ ⊢ t : Pi A B →
      P Γ t (Pi A B) →
      Σ ;; Ξ | Γ ⊢ u : A →
      P Γ u A → Σ ;; Ξ | Γ ⊢ A : Sort i →
      P Γ A (Sort i) → Σ ;; Ξ | Γ,, A ⊢ B : Sort j →
      P (Γ,, A) B (Sort j) →
      P Γ (app t u) (B <[ u..])
    ) →
    (∀ Γ c ξ Ξ' A t,
      wf Σ Ξ Γ →
      Σ c = Some (Def Ξ' A t) →
      inst_typing Σ Ξ Γ ξ Ξ' →
      inst_typing_ Σ Ξ (λ Γ t A, wf Σ Ξ Γ → P Γ t A) Γ ξ Ξ' →
      closed A = true →
      P Γ (const c ξ) (inst ξ A)
    ) →
    (∀ Γ x A,
      wf Σ Ξ Γ →
      ictx_get Ξ x = Some (Assm A) →
      closed A = true →
      P Γ (assm x) A
    ) →
    (∀ Γ i A B t,
      wf Σ Ξ Γ →
      Σ ;; Ξ | Γ ⊢ t : A →
      P Γ t A →
      Σ ;; Ξ ⊢ A ≡ B →
      Σ ;; Ξ | Γ ⊢ B : Sort i →
      P Γ B (Sort i) →
      P Γ t B
    ) →
    ∀ Γ t A, wf Σ Ξ Γ → Σ ;; Ξ | Γ ⊢ t : A → P Γ t A.
Proof.
  intros Σ Ξ P hvar hsort hpi hlam happ hconst hassm hconv.
  intros Γ t A hΓ h.
  induction h using typing_ind.
  all: try solve [ eauto using wf_cons ].
  - assert (hΓA : wf Σ Ξ (Γ ,, A)).
    { econstructor. all: eassumption. }
    eauto.
  - assert (hΓA : wf Σ Ξ (Γ ,, A)).
    { econstructor. all: eassumption. }
    eapply happ. all: eauto.
Qed.

(** * Context conversion *)

Notation ctx_conv Σ Ξ Γ Δ := (Forall2 (conversion Σ Ξ) Γ Δ).

Lemma ctx_conv_cons_same Σ Ξ Γ Δ A :
  ctx_conv Σ Ξ Γ Δ →
  ctx_conv Σ Ξ (Γ ,, A) (Δ ,, A).
Proof.
  intros h.
  constructor.
  - apply conv_refl.
  - assumption.
Qed.

Lemma ctx_conv_refl Σ Ξ Γ :
  ctx_conv Σ Ξ Γ Γ.
Proof.
  apply Forall2_diag. apply Forall_forall.
  auto using conv_refl.
Qed.

Lemma ctx_conv_cons_same_ctx Σ Ξ Γ A B :
  Σ ;; Ξ ⊢ A ≡ B →
  ctx_conv Σ Ξ (Γ ,, A) (Γ ,, B).
Proof.
  intros h.
  constructor.
  - assumption.
  - apply ctx_conv_refl.
Qed.

Inductive wf_ctx_conv Σ Ξ : ctx → ctx → Prop :=
| wf_conv_nil : wf_ctx_conv Σ Ξ ∙ ∙
| wf_conv_cons Γ Δ i A B :
    wf_ctx_conv Σ Ξ Γ Δ →
    Σ ;; Ξ | Δ ⊢ A : Sort i →
    Σ ;; Ξ ⊢ A ≡ B →
    wf_ctx_conv Σ Ξ (Γ ,, A) (Δ ,, B).

Lemma wf_ctx_conv_nth_error_l Σ Ξ Γ Δ x A :
  wf_ctx_conv Σ Ξ Γ Δ →
  nth_error Γ x = Some A →
  ∃ i B,
    nth_error Δ x = Some B ∧
    Σ ;; Ξ ⊢ A ≡ B ∧
    Σ ;; Ξ | Δ ⊢ (plus (S x)) ⋅ A : Sort i.
Proof.
  intros hctx h.
  induction hctx as [| Γ Δ i B C hctx ih hB he] in x, h |- *.
  1: destruct x ; discriminate.
  destruct x.
  - cbn in *. inversion h. subst.
    exists i, C. rasimpl. intuition auto.
    eapply meta_conv.
    + eapply typing_ren. 1: eapply rtyping_S.
      eassumption.
    + reflexivity.
  - cbn in h. eapply ih in h as (j & D & ? & ? & h).
    exists j, D. cbn. intuition auto.
    eapply typing_ren in h. 2: eapply rtyping_S.
    rasimpl in h. eassumption.
Qed.

Lemma inst_typing_ctx_conv_ih Σ Ξ Ξ' (Γ Δ : ctx) ξ :
  wf_ctx_conv Σ Ξ Γ Δ →
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ Γ t A, ∀ Δ, wf_ctx_conv Σ Ξ Γ Δ → Σ ;; Ξ | Δ ⊢ t : A) Γ ξ Ξ' →
  inst_typing Σ Ξ Δ ξ Ξ'.
Proof.
  intros hctx [h1 [h2 h3]] [ih1 [ih2 ih3]].
  split. 2: split. 1,3: assumption.
  intros x A hx. specialize (ih2 _ _ hx) as [? ih2].
  split. 1: assumption.
  eapply ih2. assumption.
Qed.

Lemma typing_ctx_conv_gen Σ Ξ (Γ Δ : ctx) t A :
  wf_ctx_conv Σ Ξ Γ Δ →
  Σ ;; Ξ | Γ ⊢ t : A →
  Σ ;; Ξ | Δ ⊢ t : A.
Proof.
  intros hctx h.
  induction h in Δ, hctx |- * using typing_ind.
  all: try solve [ econstructor ; eauto using wf_conv_cons, conv_refl ].
  - eapply wf_ctx_conv_nth_error_l in hctx as h. 2: eassumption.
    destruct h as (i & B & e & hc & h).
    eapply type_conv.
    + econstructor. eassumption.
    + apply conv_sym. apply conv_ren. assumption.
    + eassumption.
  - econstructor. 1,3: eassumption.
    eauto using inst_typing_ctx_conv_ih.
Qed.

Lemma typing_ctx_conv Σ Ξ (Γ Δ : ctx) t A :
  Σ ;; Ξ | Γ ⊢ t : A →
  wf Σ Ξ Γ →
  ctx_conv Σ Ξ Γ Δ →
  Σ ;; Ξ | Δ ⊢ t : A.
Proof.
  intros ht hΓ hctx.
  eapply typing_ctx_conv_gen. 2: eassumption.
  clear ht. induction hΓ in Δ, hctx |- *.
  - inversion hctx. constructor.
  - inversion hctx. subst.
    econstructor. 1,3: eauto.
    eauto using typing_ctx_conv_gen.
Qed.
