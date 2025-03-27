(** Basic meta-theory **)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

(** Better induction principle for [term] **)

Lemma term_rect :
   ∀ (P : term → Type),
    (∀ n, P (var n)) →
    (∀ i, P (Sort i)) →
    (∀ A, P A → ∀ B, P B → P (Pi A B)) →
    (∀ A, P A → ∀ t, P t → P (lam A t)) →
    (∀ u, P u → ∀ v, P v → P (app u v)) →
    (∀ (c : gref) (ξ : eargs), All (All P) ξ → P (const c ξ)) →
    (∀ (M : eref) (x : aref), P (assm M x)) →
    ∀ t, P t.
Proof.
  intros P hvar hsort hpi hlam happ hconst hassm.
  fix aux 1. move aux at top.
  intro t. destruct t.
  6:{
    eapply hconst.
    revert l. fix aux1 1.
    intro ξ. destruct ξ as [| σ ξ]. 1: constructor.
    constructor. 2: eauto.
    revert σ. fix aux2 1.
    intro σ. destruct σ. 1: constructor.
    constructor. all: eauto.
  }
  all: match goal with h : _ |- _ => eapply h end.
  all: eauto.
Defined.

(** Better induction principle for [conversion] **)

Lemma conversion_ind :
  ∀ Σ Ξ (P : ctx → term → term → Prop),
    (∀ Γ A t u, P Γ (app (lam A t) u) (t <[ u.. ])) →
    (∀ Γ c ξ Ξ' A t,
      Σ c = Some (Def Ξ' A t) →
      closed t = true →
      P Γ (const c ξ) (einst ξ t)
    ) →
    (∀ Γ E Ξ' Δ R M ξ' n rule σ,
      Σ E = Some (Ext Ξ' Δ R) →
      ectx_get Ξ M = Some (E, ξ') →
      nth_error R n = Some rule →
      P Γ ((plinst M (cr_pat rule)) <[ σ]) ((delocal M (cr_rep rule)) <[ σ])
    ) →
    (∀ Γ A A' B B',
      Σ ;; Ξ | Γ ⊢ A ≡ A' →
      P Γ A A' →
      Σ ;; Ξ | Γ,, A ⊢ B ≡ B' →
      P (Γ,, A) B B' →
      P Γ (Pi A B) (Pi A' B')
    ) →
    (∀ Γ A A' t t',
      Σ ;; Ξ | Γ ⊢ A ≡ A' →
      P Γ A A' →
      Σ ;; Ξ | Γ,, A ⊢ t ≡ t' →
      P (Γ,, A) t t' →
      P Γ (lam A t) (lam A' t')
    ) →
    (∀ Γ u u' v v',
      Σ ;; Ξ | Γ ⊢ u ≡ u' →
      P Γ u u' →
      Σ ;; Ξ | Γ ⊢ v ≡ v' →
      P Γ v v' →
      P Γ (app u v) (app u' v')
    ) →
    (∀ Γ c ξ ξ',
      Forall2 (Forall2 (conversion Σ Ξ Γ)) ξ ξ' →
      Forall2 (Forall2 (P Γ)) ξ ξ' →
      P Γ (const c ξ) (const c ξ')
    ) →
    (∀ Γ u, P Γ u u) →
    (∀ Γ u v, Σ ;; Ξ | Γ ⊢ u ≡ v → P Γ u v → P Γ v u) →
    (∀ Γ u v w,
      Σ ;; Ξ | Γ ⊢ u ≡ v →
      P Γ u v →
      Σ ;; Ξ | Γ ⊢ v ≡ w →
      P Γ v w →
      P Γ u w
    ) →
    ∀ Γ u v, Σ ;; Ξ | Γ ⊢ u ≡ v → P Γ u v.
Proof.
  intros Σ Ξ P hbeta hunfold hred hpi hlam happ hconst hrefl hsym htrans.
  fix aux 4. move aux at top.
  intros Γ u v h. destruct h.
  7:{
    eapply hconst. 1: assumption.
    revert ξ ξ' H.
    fix aux1 3.
    intros ξ ξ' h. destruct h as [| σ σ' ξ ξ' hσ hξ].
    - constructor.
    - constructor. 2: eauto.
      revert σ σ' hσ. fix aux2 3. intros σ σ' hσ.
      destruct hσ as [| t t' σ σ' ht hσ]. 1: constructor.
      constructor. all: eauto.
  }
  all: match goal with h : _ |- _ => solve [ eapply h ; eauto ] end.
Qed.

(** Better induction principle for [typing] **)

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
      P Γ (const c ξ) (einst ξ A)
    ) →
    (∀ Γ M x E ξ Ξ' Δ R A,
      ectx_get Ξ M = Some (E, ξ) →
      Σ E = Some (Ext Ξ' Δ R) →
      nth_error Δ x = Some A →
      closed_eargs ξ = true →
      P Γ (assm M x) (einst ξ (delocal M ((plus (S x)) ⋅ A)))
    ) →
    (∀ Γ i A B t,
      Σ ;; Ξ | Γ ⊢ t : A →
      P Γ t A →
      Σ ;; Ξ | Γ ⊢ A ≡ B →
      Σ ;; Ξ | Γ ⊢ B : Sort i →
      P Γ B (Sort i) →
      P Γ t B
    ) →
    ∀ Γ t A, Σ ;; Ξ | Γ ⊢ t : A → P Γ t A.
Proof.
  intros Σ Ξ P hvar hsort hpi hlam happ hconst hassm hconv.
  fix aux 4. move aux at top.
  intros Γ t A h. destruct h.
  6:{
    eapply hconst. 1,2,4: eassumption.
    destruct H0.
    split. 1: assumption.
    red. eauto.
  }
  all: match goal with h : _ |- _ => solve [ eapply h ; eauto ] end.
Qed.

(** Renaming preserves typing **)

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

Lemma ren_eargs_comp :
  ∀ ρ ρ' ξ,
    ren_eargs ρ (ren_eargs ρ' ξ) = ren_eargs (ρ' >> ρ) ξ.
Proof.
  intros ρ ρ' ξ.
  rewrite map_map.
  apply map_ext. intro σ.
  rewrite map_map.
  apply map_ext. intro t.
  rasimpl. reflexivity.
Qed.

Lemma lift_ren_eargs :
  ∀ ρ ξ,
    lift_eargs (ren_eargs ρ ξ) = ren_eargs (upRen_term_term ρ) (lift_eargs ξ).
Proof.
  intros ρ ξ.
  rewrite !ren_eargs_comp. reflexivity.
Qed.

Lemma ren_inst :
  ∀ ρ ξ t,
    ρ ⋅ (einst ξ t) = einst (ren_eargs ρ ξ) (ρ ⋅ t).
Proof.
  intros ρ ξ t.
  induction t using term_rect in ρ, ξ |- *.
  all: try solve [ cbn ; rewrite ?lift_ren_eargs ; f_equal ; eauto ].
  - cbn. f_equal.
    rewrite !map_map. apply map_ext_All.
    eapply All_impl. 2: eassumption.
    intros σ h.
    rewrite !map_map. apply map_ext_All.
    eapply All_impl. 2: eassumption.
    cbn. intros t ht. auto.
  - cbn. unfold eget.
    rewrite nth_error_map.
    destruct (nth_error ξ _) as [σ |]. 2: reflexivity.
    cbn. rewrite nth_error_map.
    destruct (nth_error σ _) as [t |]. 2: reflexivity.
    cbn. reflexivity.
Qed.

Fixpoint uprens k (ρ : nat → nat) :=
  match k with
  | 0 => ρ
  | S k => upRen_term_term (uprens k ρ)
  end.

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
    cbn. intros σ [h1 h2].
    rewrite <- map_id. apply map_ext_All.
    apply forallb_All in h2.
    eapply All_prod in h1. 2: eassumption.
    eapply All_impl. 2: eassumption. clear.
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

Lemma ren_eargs_ext ρ ζ ξ :
  (∀ n, ρ n = ζ n) →
  ren_eargs ρ ξ = ren_eargs ζ ξ.
Proof.
  intros h.
  apply map_ext. intro.
  apply map_ext. intro.
  apply extRen_term. assumption.
Qed.

Lemma ren_eargs_id ξ :
  ren_eargs id ξ = ξ .
Proof.
  rewrite <- map_id. apply map_ext. intro.
  rewrite <- map_id. apply map_ext. intro.
  rasimpl. reflexivity.
Qed.

Lemma ren_eargs_id_ext ρ ξ :
  (∀ n, ρ n = n) →
  ren_eargs ρ ξ = ξ.
Proof.
  intro h.
  etransitivity. 2: eapply ren_eargs_id.
  apply ren_eargs_ext. assumption.
Qed.

Corollary closed_ren_eargs ρ ξ :
  closed_eargs ξ = true →
  ren_eargs ρ ξ = ξ.
Proof.
  intros h.
  etransitivity. 2: apply ren_eargs_id.
  unfold closed_eargs in h.
  apply map_ext_All. eapply All_impl.
  2:{ apply forallb_All. eassumption. }
  cbn. intros σ hσ%forallb_All.
  apply map_ext_All. eapply All_impl. 2: eassumption.
  cbn. rasimpl. apply closed_ren.
Qed.

Lemma conv_ren :
  ∀ Σ Ξ Γ Δ ρ u v,
    rtyping Γ ρ Δ →
    Σ ;; Ξ | Δ ⊢ u ≡ v →
    Σ ;; Ξ | Γ ⊢ ρ ⋅ u ≡ ρ ⋅ v.
Proof.
  intros Σ Ξ Γ Δ ρ u v hρ h.
  induction h using conversion_ind in Γ, ρ, hρ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto using rtyping_up ].
  - rasimpl. eapply meta_conv_trans_r. 1: econstructor.
    rasimpl. reflexivity.
  - rasimpl. eapply conv_trans. 1: econstructor. 1,2: eassumption.
    rewrite ren_inst. rewrite closed_ren. 2: assumption.
    ttconv.
  - cbn. constructor.
    rewrite Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros σ σ' h.
    rewrite Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    cbn. intros u v ih. eauto.
Qed.

Fixpoint ren_ctx ρ Γ {struct Γ} :=
  match Γ with
  | [] => ∙
  | A :: Γ => (ren_ctx ρ Γ) ,, (uprens (length Γ) ρ ⋅ A)
  end.

Lemma rtyping_uprens :
  ∀ Γ Δ Θ ρ,
    rtyping Δ ρ Γ →
    rtyping (Δ ,,, ren_ctx ρ Θ) (uprens (length Θ) ρ) (Γ ,,, Θ).
Proof.
  intros Γ Δ Θ ρ h.
  induction Θ as [| A Θ ih].
  - cbn. assumption.
  - cbn. rewrite app_comm_cons. cbn. eapply rtyping_up. assumption.
Qed.

Lemma slist_ren σ ρ :
  pointwise_relation _ eq (slist (map (ren_term ρ) σ)) (slist σ >> ren_term ρ).
Proof.
  intro n.
  induction σ in ρ, n |- *.
  - cbn. reflexivity.
  - cbn. destruct n.
    + cbn. reflexivity.
    + cbn. rewrite IHσ. reflexivity.
Qed.

Lemma eget_ren ξ M x ρ :
  eget (ren_eargs ρ ξ) M x = ρ ⋅ (eget ξ M x).
Proof.
  unfold eget.
  rewrite nth_error_map.
  destruct (nth_error ξ M). 2: reflexivity.
  cbn. rewrite nth_error_map.
  destruct (nth_error _ x). 2: reflexivity.
  cbn. reflexivity.
Qed.

Lemma inst_typing_ren Σ Ξ Δ Γ ρ ξ Ξ' :
  rtyping Δ ρ Γ →
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ Γ t A,
    ∀ Δ ρ, rtyping Δ ρ Γ → Σ ;; Ξ | Δ ⊢ ρ ⋅ t : ρ ⋅ A
  ) Γ ξ Ξ' →
  inst_typing Σ Ξ Δ (ren_eargs ρ ξ) Ξ'.
Proof.
  intros hρ [h1 h2] [ih1 ih2].
  split.
  - admit.
  - intros M x E ξ' Ξ'' Θ R A hM hE hx hξ'.
    rewrite eget_ren. eapply meta_conv.
    + eauto.
    + rewrite !ren_inst. f_equal. f_equal.
      * apply closed_ren_eargs. assumption.
      * unfold delocal. rasimpl.
        apply ext_term. cbn. auto.
Admitted.

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
  - rasimpl. eapply meta_conv.
    1:{ econstructor. all: eassumption. }
    rewrite ren_inst.
    f_equal.
    + symmetry. apply closed_ren_eargs. assumption.
    + unfold delocal. rasimpl.
      apply ext_term. cbn. auto.
  - rasimpl. rasimpl in IHht2.
    econstructor. all: eauto.
    eapply conv_ren. all: eassumption.
Qed.

(** Substitution preserves typing **)

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
  lift_eargs (liftn n ξ) = liftn (S n) ξ.
Proof.
  rewrite ren_eargs_comp. reflexivity.
Qed.

Lemma subst_inst σ ξ t n m :
  (∀ k, σ (m + k) = var (n + k)) →
  einst (liftn n ξ) (t <[ σ ]) =
  (einst (liftn m ξ) t) <[ σ >> einst (liftn n ξ) ].
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
    intros l hl.
    rewrite !map_map. apply map_ext_All.
    eapply All_impl. 2: eassumption.
    eauto.
  - cbn. rewrite !eget_ren. rasimpl.
    rewrite rinstInst'_term.
    apply ext_term. intro k.
    unfold core.funcomp.
    rewrite hσ. cbn. reflexivity.
Qed.

Notation subst_eargs σ ξ :=
  (map (map (subst_term σ)) ξ).

Lemma eget_subst σ ξ M x :
  eget (subst_eargs σ ξ) M x = (eget ξ M x) <[ σ ].
Proof.
  unfold eget.
  rewrite nth_error_map. destruct nth_error. 2: reflexivity.
  cbn. rewrite nth_error_map. destruct nth_error. 2: reflexivity.
  cbn. reflexivity.
Qed.

Lemma subst_inst_scoped σ ξ t k :
  scoped k t = true →
  (∀ n, n < k → σ n = var n) →
  (einst ξ t) <[ σ ] = einst (subst_eargs σ ξ) t.
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
    rewrite !map_map. apply map_ext. intro t.
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
    rewrite !map_map. apply map_ext. intro t.
    rasimpl. reflexivity.
  - cbn in *. apply andb_prop in h as [].
    f_equal. all: eauto.
  - cbn in *. f_equal.
    rewrite map_map. apply map_ext_All.
    apply forallb_All in h. move h at top.
    eapply All_prod in h. 2: eassumption.
    eapply All_impl. 2: eassumption. clear - hσ.
    cbn. intros l [h1 h2].
    rewrite map_map. apply map_ext_All.
    apply forallb_All in h2.
    eapply All_prod in h1. 2: eassumption.
    eapply All_impl. 2: eassumption. clear - hσ.
    cbn. intros t [h1 h2]. eauto.
  - cbn. symmetry. apply eget_subst.
Qed.

Corollary subst_inst_closed σ ξ t :
  closed t = true →
  (einst ξ t) <[ σ ] = einst (subst_eargs σ ξ) t.
Proof.
  intro h.
  eapply subst_inst_scoped.
  - eassumption.
  - lia.
Qed.

Lemma conv_subst Σ Ξ Γ Δ σ u v :
  Σ ;; Ξ | Δ ⊢ u ≡ v →
  Σ ;; Ξ | Γ ⊢ u <[ σ ] ≡ v <[ σ ].
Proof.
  intros h.
  induction h using conversion_ind in Γ, σ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto ].
  - rasimpl. eapply meta_conv_trans_r. 1: econstructor.
    rasimpl. reflexivity.
  - cbn. eapply meta_conv_trans_r.
    1:{ econstructor. all: eassumption. }
    symmetry. apply subst_inst_closed. assumption.
  - cbn. constructor.
    apply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros l l' h.
    apply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    cbn. auto.
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

Lemma scoped_delocal M t k :
  scoped k (t <[ ups k (λ x, assm M x) ]) = true.
Proof.
  induction t using term_rect in k |- *.
  all: try solve [ cbn ; eauto using andb_true_intro ].
  - cbn. destruct (lt_dec n k).
    + rewrite ups_below. 2: assumption.
      cbn - ["<?"]. apply Nat.ltb_lt. assumption.
    + pose (m := n - k). replace n with (k + m) by lia.
      rewrite ups_above. reflexivity.
  - cbn. apply All_forallb. apply All_map.
    eapply All_impl. 2: eassumption.
    intros. apply All_forallb. apply All_map.
    eapply All_impl. 2: eassumption.
    auto.
Qed.

Lemma closed_delocal M t :
  closed (delocal M t) = true.
Proof.
  apply scoped_delocal with (k := 0).
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
    rewrite <- map_id. apply map_ext_All.
    apply forallb_All in h2.
    eapply All_prod in h1. 2: eassumption.
    eapply All_impl. 2: eassumption. clear.
    cbn. intros t [h1 h2]. eauto.
Qed.

Corollary closed_subst σ t :
  closed t = true →
  t <[ σ ] = t.
Proof.
  intros h.
  eapply scoped_subst in h. eauto.
Qed.

Lemma subst_eargs_id ξ :
  subst_eargs ids ξ = ξ.
Proof.
  rewrite <- map_id. apply map_ext. intro.
  rewrite <- map_id. apply map_ext. intro.
  rasimpl. reflexivity.
Qed.

Lemma closed_subst_eargs σ ξ :
  closed_eargs ξ = true →
  subst_eargs σ ξ = ξ.
Proof.
  intros h.
  etransitivity. 2: apply subst_eargs_id.
  unfold closed_eargs in h.
  apply map_ext_All. eapply All_impl.
  2:{ apply forallb_All. eassumption. }
  cbn. intros ? hσ%forallb_All.
  apply map_ext_All. eapply All_impl. 2: eassumption.
  cbn. rasimpl. apply closed_subst.
Qed.

Lemma closed_lift_eargs ξ :
  closed_eargs ξ = true →
  closed_eargs (lift_eargs ξ) = true.
Proof.
  intro h.
  rewrite closed_ren_eargs. all: assumption.
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
    cbn. intros ? [h1 h2]. apply All_forallb. apply forallb_All in h2.
    eapply All_prod in h1. 2: eassumption.
    eapply All_impl. 2: eassumption.
    cbn. intros ? []. eauto.
Qed.

Lemma scoped_einst k ξ t :
  closed_eargs ξ = true →
  scoped k t = true →
  scoped k (einst ξ t) = true.
Proof.
  intros hξ ht.
  induction t using term_rect in k, ξ, ht, hξ |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn in * ; apply andb_prop in ht as [] ;
    apply andb_true_intro ; eauto using closed_lift_eargs
  ].
  - cbn in *. apply forallb_All in ht. move ht at top.
    eapply All_prod in ht. 2: eassumption.
    apply All_forallb. apply All_map. eapply All_impl. 2: eassumption.
    clear - hξ.
    cbn. intros σ [h1 h2].
    apply All_forallb. apply All_map.
    apply forallb_All in h2.
    eapply All_prod in h1. 2: eassumption.
    eapply All_impl. 2: eassumption. clear - hξ.
    cbn. intros t [h1 h2]. eauto.
  - cbn. unfold closed_eargs in hξ. unfold eget.
    destruct nth_error as [l |] eqn: eM. 2: reflexivity.
    destruct (nth_error l _) eqn: ex. 2: reflexivity.
    apply nth_error_In in eM, ex.
    rewrite forallb_forall in hξ. specialize hξ with (1 := eM).
    rewrite forallb_forall in hξ. specialize hξ with (1 := ex).
    eapply scoped_upwards. 1: eassumption.
    lia.
Qed.

Corollary closed_einst ξ t :
  closed_eargs ξ = true →
  closed t = true →
  closed (einst ξ t) = true.
Proof.
  intros hξ ht.
  apply scoped_einst. all: assumption.
Qed.

Lemma inst_typing_subst Σ Ξ Δ Γ σ ξ Ξ' :
  styping Σ Ξ Δ σ Γ →
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ Γ t A,
    ∀ Δ σ, styping Σ Ξ Δ σ Γ → Σ ;; Ξ | Δ ⊢ t <[ σ ] : A <[ σ ]
  ) Γ ξ Ξ' →
  inst_typing Σ Ξ Δ (subst_eargs σ ξ) Ξ'.
Proof.
  intros hσ [h1 h2] [ih1 ih2].
  split.
  - admit.
  - intros M x E ξ' Ξ'' Θ R A hM hE hx hξ'.
    rewrite eget_subst. eapply meta_conv.
    + eauto.
    + apply subst_inst_closed. apply closed_einst.
      * assumption.
      * apply closed_delocal.
Admitted.

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
  - cbn. eapply meta_conv.
    + econstructor. all: eassumption.
    + rewrite subst_inst_closed. 2: apply closed_delocal.
      rewrite closed_subst_eargs. 2: assumption.
      reflexivity.
  - econstructor. 1,3: eauto.
    eapply conv_subst. eassumption.
Qed.

(** Instances preserve conversion and typing **)

Lemma nth_error_ctx_einst ξ Γ x :
  nth_error (ctx_einst ξ Γ) x =
  option_map (einst (ren_eargs (plus (length Γ - S x)) ξ)) (nth_error Γ x).
Proof.
  induction Γ in ξ, x |- *.
  - cbn. rewrite nth_error_nil. reflexivity.
  - destruct x as [| x].
    + cbn. replace (length Γ - 0) with (length Γ) by lia.
      reflexivity.
    + cbn. eauto.
Qed.

Lemma length_ctx_einst ξ Γ :
  length (ctx_einst ξ Γ) = length Γ.
Proof.
  induction Γ in ξ |- *.
  - reflexivity.
  - cbn. eauto.
Qed.

Lemma einst_eget ξ ξ' M x :
  einst ξ (eget ξ' M x) = eget (map (map (einst ξ)) ξ') M x.
Proof.
  unfold eget. rewrite nth_error_map.
  destruct nth_error. 2: reflexivity.
  cbn. rewrite nth_error_map.
  destruct nth_error. 2: reflexivity.
  reflexivity.
Qed.

Lemma einst_einst ξ ξ' t :
  einst ξ (einst ξ' t) = einst (map (map (einst ξ)) ξ') t.
Proof.
  induction t using term_rect in ξ, ξ' |- *.
  all: try solve [ cbn ; f_equal ; eauto ].
  - cbn. f_equal. 1: eauto.
    rewrite IHt2. f_equal.
    rewrite !map_map. apply map_ext. intro σ.
    rewrite !map_map. apply map_ext. intro t.
    symmetry. apply ren_inst.
  - cbn. f_equal. 1: eauto.
    rewrite IHt2. f_equal.
    rewrite !map_map. apply map_ext. intro σ.
    rewrite !map_map. apply map_ext. intro t.
    symmetry. apply ren_inst.
  - cbn. f_equal.
    rewrite !map_map. apply map_ext_All.
    eapply All_impl. 2: eassumption.
    intros σ hσ.
    rewrite !map_map. apply map_ext_All.
    eapply All_impl. 2: eassumption.
    auto.
  - cbn. apply einst_eget.
Qed.

Lemma conv_einst Σ Ξ Ξ' Γ Δ u v ξ :
  inst_equations Σ Ξ Δ ξ Ξ' →
  Σ ;; Ξ' | Γ ⊢ u ≡ v →
  let rξ := liftn (length Γ) ξ in
  Σ ;; Ξ | Δ ,,, ctx_einst ξ Γ ⊢ einst rξ u ≡ einst rξ v.
Proof.
  intros hξ h. cbn.
  induction h using conversion_ind in Ξ, Δ, ξ, hξ |- *.
  all: try solve [ cbn ; econstructor ; eauto ].
  - cbn. rewrite subst_inst with (m := S (length Γ)). 2: auto.
    eapply meta_conv_trans_r. 1: constructor.
    cbn. rewrite lift_liftn. apply ext_term. intros []. all: reflexivity.
  - cbn. eapply meta_conv_trans_r. 1:{ eapply conv_unfold. all: eassumption. }
    rewrite einst_einst. reflexivity.
  - red in hξ.
    (* Here we need the constraint that says we can do this! *)
    admit.
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
    apply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    cbn. auto.
Admitted.

Lemma typing_einst Σ Ξ Ξ' Γ Δ t A ξ :
  inst_typing Σ Ξ Δ ξ Ξ' →
  Σ ;; Ξ' | Γ ⊢ t : A →
  let rξ := liftn (length Γ) ξ in
  Σ ;; Ξ | Δ ,,, ctx_einst ξ Γ ⊢ einst rξ t : einst rξ A.
Proof.
  intros hξ ht rξ.
  induction ht using typing_ind in Ξ, Δ, ξ, rξ, hξ |- *.
  all: try solve [ cbn ; econstructor ; eauto ].
  - cbn. eapply meta_conv.
    + econstructor. rewrite nth_error_app1.
      2:{ rewrite length_ctx_einst. eapply nth_error_Some. congruence. }
      rewrite nth_error_ctx_einst.
      rewrite H. cbn. reflexivity.
    + rewrite ren_inst. f_equal.
      rewrite ren_eargs_comp.
      apply ren_eargs_ext.
      cbn. intro.
      pose proof (nth_error_Some Γ x) as e%proj1.
      forward e by congruence.
      lia.
  - cbn. constructor. 1: eauto.
    subst rξ. rewrite ren_eargs_comp. apply IHht2. assumption.
  - cbn. econstructor. 1: eauto.
    + subst rξ. rewrite ren_eargs_comp. apply IHht2. assumption.
    + subst rξ. rewrite ren_eargs_comp. apply IHht3. assumption.
  - cbn. eapply meta_conv.
    + cbn in *. econstructor. all: eauto.
      subst rξ. rewrite ren_eargs_comp. apply IHht4. assumption.
    + rasimpl.
      subst rξ. erewrite subst_inst with (m := S (length Γ)).
      2:{ cbn. auto. }
      rewrite lift_liftn.
      apply ext_term. intros []. all: reflexivity.
  - cbn. eapply meta_conv.
    + econstructor. 1,3: eassumption.
      destruct H1.
      split.
      * intros E Ξ'' Θ R M ξ' σ n rule hE hM hξM hn. cbn.
        rewrite <- einst_einst.
        admit.
      * intros M x E ξ' Ξ'' Θ R B hM hE hx.
        rewrite <- einst_eget. rewrite <- einst_einst.
        eauto.
    + rewrite einst_einst. reflexivity.
  - cbn. subst rξ. rewrite eget_ren.
    eapply meta_conv.
    + eapply typing_ren.
      1:{ erewrite <- length_ctx_einst. eapply rtyping_add. }
      eapply hξ. all: eassumption.
    + rewrite ren_inst. f_equal.
      rewrite ren_inst. f_equal.
      * apply closed_ren_eargs. assumption.
      * unfold delocal. rasimpl.
        apply ext_term. cbn. unfold core.funcomp.
        admit.
  - econstructor. 1,3: eauto.
    eapply conv_einst. 2: eassumption.
    apply hξ.
Admitted.

Corollary typing_einst_closed Σ Ξ Ξ' Γ t A ξ :
  inst_typing Σ Ξ Γ ξ Ξ' →
  Σ ;; Ξ' | ∙ ⊢ t : A →
  Σ ;; Ξ | Γ ⊢ einst ξ t : einst ξ A.
Proof.
  intros hξ h.
  eapply typing_einst in h. 2: eassumption.
  cbn in h.
  rewrite ren_eargs_id_ext in h. 2: auto.
  assumption.
Qed.

(** Extension environement weakening **)

Lemma ectx_get_weak d Ξ M i :
  ectx_get Ξ M = Some i →
  ectx_get (d :: Ξ) M = Some i.
Proof.
  unfold ectx_get. cbn - ["<=?"].
  destruct (_ <=? _) eqn: e. 1: congruence.
  rewrite Nat.leb_gt in e.
  intro h.
  destruct (_ <=? _) eqn: e'. 1:{ rewrite Nat.leb_le in e'. lia. }
  replace (length Ξ - M) with (S (length Ξ - (S M))) by lia.
  cbn. assumption.
Qed.

Lemma conv_eweak Σ Ξ d Γ u v :
  Σ ;; Ξ | Γ ⊢ u ≡ v →
  Σ ;; d :: Ξ | Γ ⊢ u ≡ v.
Proof.
  intros h. induction h using conversion_ind.
  all: try solve [ econstructor ; eauto ].
  econstructor. 1,3: eauto.
  apply ectx_get_weak. eassumption.
Qed.

(** Global environment weakening **)

Lemma conv_gweak Σ Σ' Ξ Γ u v :
  Σ ;; Ξ | Γ ⊢ u ≡ v →
  Σ ⊑ Σ' →
  Σ' ;; Ξ | Γ ⊢ u ≡ v.
Proof.
  intros h hle. induction h using conversion_ind.
  all: solve [ econstructor ; eauto ].
Qed.

Lemma inst_equations_gweak Σ Σ' Ξ Γ ξ Ξ' :
  inst_equations Σ Ξ Γ ξ Ξ' →
  Σ ⊑ Σ' →
  inst_equations Σ' Ξ Γ ξ Ξ'.
Proof.
Admitted.

Lemma inst_eget_gweak Σ Σ' Ξ Γ ξ Ξ' :
  inst_eget Σ Ξ Γ ξ Ξ' →
  inst_eget_ Σ (λ Γ t A, Σ' ;; Ξ | Γ ⊢ t : A) Γ ξ Ξ' →
  Σ ⊑ Σ' →
  inst_eget Σ' Ξ Γ ξ Ξ'.
Proof.
  intros h ih hle.
  intros M x E ξ' Ξ'' Δ R A hM hE hx hc.
  eapply ih. all: eauto.
  (* I guess we need some guarantee that M and Ξ' weren't pointing into the
    future *)
Admitted.

Lemma inst_typing_gweak_ Σ Σ' Ξ Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ Γ t A, Σ' ;; Ξ | Γ ⊢ t : A) Γ ξ Ξ' →
  Σ ⊑ Σ' →
  inst_typing Σ' Ξ Γ ξ Ξ'.
Proof.
  intros [h1 h2] [ih1 ih2] hle.
  split.
  - eapply inst_equations_gweak. all: eassumption.
  - eapply inst_eget_gweak. all: eassumption.
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
  destruct h as [h1 h2]. split.
  - assumption.
  - intros M x E ξ' Ξ'' Δ R A hM hE hx hc.
    eapply typing_gweak. all: eauto.
Qed.

Lemma ewf_gweak Σ Σ' Ξ :
  ewf Σ Ξ →
  Σ ⊑ Σ' →
  ewf Σ' Ξ.
Proof.
  intros h hle. induction h.
  - constructor.
  - econstructor. 1,2: eauto.
    eapply inst_typing_gweak. all: eauto.
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

(** Validity (or presupposition) **)

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

Lemma extends_gcons Σ c d :
  Σ c = None →
  Σ ⊑ gcons c d Σ.
Proof.
  intros h. intros c' d' e.
  unfold gcons. destruct (_ =? _)%string eqn:ec.
  - apply eqb_eq in ec. subst. congruence.
  - assumption.
Qed.

Lemma valid_def Σ c Ξ A t :
  gwf Σ →
  Σ c = Some (Def Ξ A t) →
  ewf Σ Ξ ∧
  (∃ i, Σ ;; Ξ | ∙ ⊢ A : Sort i) ∧
  Σ ;; Ξ | ∙ ⊢ t : A.
Proof.
  intros hΣ hc.
  induction hΣ as [ | c' ?????? ih | c' ??????? ih ] in c, Ξ, A, t, hc |- *.
  - discriminate.
  - unfold gcons in hc. destruct (c =? c')%string. 1: discriminate.
    specialize ih with (1 := hc) as [? [[i ?] ?]].
    split. 2: split.
    + eapply ewf_gweak. all: eauto using extends_gcons.
    + eexists. eapply typing_gweak. all: eauto using extends_gcons.
    + eapply typing_gweak. all: eauto using extends_gcons.
  - unfold gcons in hc. destruct (c =? c')%string.
    + inversion hc. subst.
      intuition eauto using ewf_gweak, typing_gweak, extends_gcons.
    + specialize ih with (1 := hc) as [? [[j ?] ?]].
      intuition eauto using ewf_gweak, typing_gweak, extends_gcons.
Qed.

Lemma valid_ext Σ c Ξ Δ R :
  gwf Σ →
  Σ c = Some (Ext Ξ Δ R) →
  ewf Σ Ξ ∧ wf Σ Ξ Δ.
Proof.
  intros hΣ hc.
  induction hΣ as [ | c' ?????? ih | c' ??????? ih ] in c, Ξ, Δ, R, hc |- *.
  - discriminate.
  - unfold gcons in hc. destruct (c =? c')%string.
    + inversion hc. subst.
      intuition eauto using wf_gweak, ewf_gweak, typing_gweak, extends_gcons.
    + specialize ih with (1 := hc) as [? ?].
      intuition eauto using wf_gweak, ewf_gweak, typing_gweak, extends_gcons.
  - unfold gcons in hc. destruct (c =? c')%string. 1: discriminate.
    specialize ih with (1 := hc) as [? ?].
    intuition eauto using wf_gweak, ewf_gweak, typing_gweak, extends_gcons.
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

Lemma styping_delocal Σ Ξ M Γ E ξ Ξ' R :
  ectx_get Ξ M = Some (E, ξ) →
  Σ E = Some (Ext Ξ' Γ R) →
  closed_eargs ξ = true →
  styping Σ Ξ' ∙ (λ n, assm M n) Γ.
Proof.
  intros hM hE hξ.
  rewrite styping_alt_equiv. intros x A e.
  rasimpl. eapply meta_conv.
  - econstructor. all: eauto.
    (* Not good *)
    admit.
  - (* Something's off here too! So I must have messed something up in the
    typing rules. *)
Abort.

Lemma type_delocal Σ Ξ Γ M A i E ξ Ξ' R :
  ectx_get Ξ M = Some (E, ξ) →
  Σ E = Some (Ext Ξ' Γ R) →
  closed_eargs ξ = true →
  Σ ;; Ξ' | Γ ⊢ A : Sort i →
  Σ ;; Ξ' | ∙ ⊢ delocal M A : Sort i.
Proof.
  intros hM hE hξ h.
  eapply meta_conv.
  - unfold delocal. eapply typing_subst. 2: eassumption.
    (* When is it correct? *)
    admit.
  - reflexivity.
Admitted.

Lemma validity Σ Ξ Γ t A :
  gwf Σ →
  ewf Σ Ξ →
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
    + eapply typing_einst_closed. all: eassumption.
    + reflexivity.
  - eapply valid_ext in hΣ as h. 2: eassumption.
    destruct h as [hΞ' hΔ].
    eapply valid_wf in hΔ as hA. 2: eassumption.
    destruct hA as [i hA].
    exists i. eapply meta_conv.
    + eapply typing_einst_closed.
      * admit. (* See how to get it *)
      * eapply type_delocal. all: eauto.
    + reflexivity.
  - eexists. eassumption.
Admitted.
