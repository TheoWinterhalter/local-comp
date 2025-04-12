(** Basic meta-theory **)

From Stdlib Require Import Utf8 String List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".

(** Induction principle for [parg] **)

Lemma parg_ind :
  ∀ (P : parg → Prop),
    P pvar →
    (∀ t, P (pforce t)) →
    (∀ x l,
      Forall P l →
      P (psymb x l)
    ) →
    ∀ p, P p.
Proof.
  intros P hvar hforce hsymb.
  fix aux 1. move aux at top.
  intro p. destruct p.
  3:{
    eapply hsymb.
    revert l. fix auxl 1.
    intro l. destruct l.
    - constructor.
    - econstructor. all: eauto.
  }
  all: match goal with h : _ |- _ => eapply h end.
Qed.

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
  ∀ (Σ : gctx) Ξ (P : ctx → term → term → Prop),
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
      let δ := length Δ in
      let lhs := rule_lhs M ξ' δ rule in
      let rhs := rule_rhs M ξ' δ rule in
      let k := length rule.(cr_env) in
      scoped k lhs = true →
      scoped k rhs = true →
      P Γ (lhs <[ σ ]) (rhs <[ σ ])
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
      P Γ (assm M x) (delocal M (einst ξ ((plus (S x)) ⋅ A)))
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
  intros Γ t A h. destruct h as [| | | | | ????? hc h hA | |].
  6:{
    eapply hconst. 1,2,4: eassumption.
    destruct h as [h1 [h2 h3]].
    split. 1: assumption.
    split. 2: assumption.
    intros M E ξ' hM. specialize (h2 _ _ _ hM).
    destruct h2 as [? [? [? [? h2]]]]. split. 1: assumption.
    eexists _,_,_. intuition eauto.
  }
  all: match goal with h : _ |- _ => solve [ eapply h ; eauto ] end.
Qed.

(** Typing implies scoping **)

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
  - cbn. eapply forallb_forall. intros σ hσ.
    eapply forallb_forall. intros u hu.
    eapply In_nth_error in hσ as [M hM].
    eapply In_nth_error in hu as [x hx].
    destruct H1 as [_ [ih e]]. red in ih. specialize (ih M).
    destruct (ectx_get Ξ' M) as [[E ξ'] |] eqn:e'.
    2:{
      unfold ectx_get in e'. destruct (_ <=? _) eqn: e1.
      - rewrite Nat.leb_le in e1. rewrite <- e in e1.
        rewrite <- nth_error_None in e1. congruence.
      - rewrite nth_error_None in e'.
        rewrite Nat.leb_gt in e1. lia.
    }
    specialize ih with (1 := eq_refl).
    destruct ih as (hξ' & Ξ'' & Δ & R & hE & eM & ih).
    rewrite hM in eM. cbn in eM.
    destruct (nth_error Δ x) eqn: eΔ.
    2:{
      rewrite nth_error_None in eΔ. rewrite <- eM in eΔ.
      rewrite <- nth_error_None in eΔ. congruence.
    }
    specialize ih with (1 := eΔ).
    unfold eget in ih. rewrite hM, hx in ih.
    assumption.
Qed.

Lemma typing_closed Σ Ξ t A :
  Σ ;; Ξ | ∙ ⊢ t : A →
  closed t = true.
Proof.
  intros h.
  eapply typing_scoped with (Γ := ∙).
  eassumption.
Qed.

(** Context is irrelevant for conversion

  A bit silly, but it might be better to stick to it in case we want to add more
  data.

**)

Lemma conv_ctx_irr Σ Ξ Γ Δ u v :
  Σ ;; Ξ | Γ ⊢ u ≡ v →
  Σ ;; Ξ | Δ ⊢ u ≡ v.
Proof.
  induction 1 using conversion_ind in Δ |- *.
  all: try solve [ ttconv ].
  all: try solve [ econstructor ; eauto ].
  econstructor. eapply Forall2_impl. 2: eassumption.
  intros. eapply Forall2_impl. 2: eassumption.
  auto.
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

Lemma ren_eargs_ext ρ ζ ξ :
  (∀ n, ρ n = ζ n) →
  ren_eargs ρ ξ = ren_eargs ζ ξ.
Proof.
  intros h.
  apply map_ext. intro.
  apply map_ext. intro.
  apply extRen_term. assumption.
Qed.

Lemma liftn_liftn n m ξ :
  liftn n (liftn m ξ) = liftn (n + m) ξ.
Proof.
  rewrite ren_eargs_comp.
  apply ren_eargs_ext. unfold core.funcomp. intro. lia.
Qed.

Fixpoint uprens k (ρ : nat → nat) :=
  match k with
  | 0 => ρ
  | S k => upRen_term_term (uprens k ρ)
  end.

Lemma liftn_ren_eargs n ρ ξ :
  liftn n (ren_eargs ρ ξ) = ren_eargs (uprens n ρ) (liftn n ξ).
Proof.
  rewrite 2!ren_eargs_comp. apply ren_eargs_ext.
  intros m. unfold core.funcomp.
  induction n as [| n ih] in m, ρ |- *.
  - reflexivity.
  - cbn. unfold core.funcomp. rewrite <- ih.
    reflexivity.
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

Lemma conv_ren Σ Ξ Γ Δ ρ u v :
  (* rtyping Γ ρ Δ → *)
  Σ ;; Ξ | Δ ⊢ u ≡ v →
  Σ ;; Ξ | Γ ⊢ ρ ⋅ u ≡ ρ ⋅ v.
Proof.
  intros (* hρ *) h.
  induction h using conversion_ind in Γ, ρ (* , hρ *) |- *.
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

Corollary rtyping_uprens_eq Γ Δ Θ ρ k :
  rtyping Δ ρ Γ →
  k = length Θ →
  rtyping (Δ ,,, ren_ctx ρ Θ) (uprens k ρ) (Γ ,,, Θ).
Proof.
  intros h ->.
  eapply rtyping_uprens. assumption.
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

Lemma length_ctx_einst ξ Γ :
  length (ctx_einst ξ Γ) = length Γ.
Proof.
  induction Γ in ξ |- *.
  - reflexivity.
  - cbn. eauto.
Qed.

Lemma ren_ctx_einst ρ ξ Γ :
  ren_ctx ρ (ctx_einst ξ Γ) = ctx_einst (ren_eargs ρ ξ) Γ.
Proof.
  induction Γ as [| A Γ ih] in ρ, ξ |- *.
  - reflexivity.
  - cbn. rewrite ih. f_equal.
    rewrite length_ctx_einst.
    rewrite ren_inst.
    rewrite <- liftn_ren_eargs. f_equal.
    apply scoped_ren.
    (* Would need the context to be closed *)
Abort.

Lemma inst_typing_ren Σ Ξ Δ Γ ρ ξ Ξ' :
  rtyping Δ ρ Γ →
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ Γ t A,
    ∀ Δ ρ, rtyping Δ ρ Γ → Σ ;; Ξ | Δ ⊢ ρ ⋅ t : ρ ⋅ A
  ) Γ ξ Ξ' →
  inst_typing Σ Ξ Δ (ren_eargs ρ ξ) Ξ'.
Proof.
  intros hρ [h1 [h2 h3]] [ih1 [ih2 ih3]].
  split. 2: split.
  - intros E M ξ' hM.
    specialize (h1 _ _ _ hM) as (Ξ'' & Δ' & R & e & h).
    eexists _,_,_. split. 1: eauto.
    intros n rule hn m δ Θ lhs0 rhs0 hl hr. cbn.
    (* forward *)
    specialize h with (1 := hn) (2 := hl) (3 := hr). cbn in h.
    fold m δ lhs0 rhs0 in h.
    eapply conv_ren with (ρ := uprens m ρ) in h.
    (* 2:{
      eapply rtyping_uprens_eq. 1: eassumption.
      rewrite 2!length_ctx_einst. reflexivity.
    } *)
    rewrite 2!ren_inst in h.
    rewrite 2!scoped_ren in h. 2,3: eassumption.
    rewrite liftn_ren_eargs.
    eassumption.
  - intros M E ξ' e. specialize (ih2 _ _ _ e) as [? [? [? [? [? [? ih2]]]]]].
    split. 1: assumption.
    eexists _,_,_. split. 1: eassumption.
    split.
    1:{
      rewrite nth_error_map, onSome_map. setoid_rewrite length_map. assumption.
    }
    intros ?? h.
    rewrite eget_ren. eapply meta_conv.
    + eauto.
    + rewrite !ren_inst. f_equal.
      apply closed_ren. apply closed_delocal.
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
  - rasimpl. rewrite closed_ren. 2: eapply closed_delocal.
    econstructor. all: eassumption.
  - rasimpl. rasimpl in IHht2.
    econstructor. all: eauto.
    eapply conv_ren. all: eassumption.
Qed.

(** Reproving [ext_term] but with scoping assumption **)

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
    cbn. intros l [h1 h2].
    apply map_ext_All.
    apply forallb_All in h2.
    eapply All_prod in h1. 2: eassumption.
    eapply All_impl. 2: eassumption. clear - e.
    cbn. intros t [h1 h2]. eauto.
Qed.

(** Corollary: every substitution acts like a list of terms

  We present two versions: one with actual lists, and one where we truncate
  a substitution directly, behaving as a shift outside.
  The latter has the advantage that it verifies the condition for
  [subst_inst] later.

**)

Fixpoint listify k (σ : nat → term) :=
  match k with
  | 0 => []
  | S k => σ 0 :: listify k (S >> σ)
  end.

Lemma eq_subst_slist k σ :
  eq_subst_on k σ (slist (listify k σ)).
Proof.
  intros x h.
  induction k as [| k ih] in x, h, σ |- *. 1: lia.
  cbn. destruct x as [| x].
  - reflexivity.
  - cbn. apply (ih (S >> σ)). lia.
Qed.

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

(**

  Note: the condition is weird, because we can just use [trunc] to make it work
  for any [m]. The fact that we're free to choose [m] suggests there is a better
  lemma to be had.

**)

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

Corollary subst_inst_ups σ ξ t k :
  scoped k t = true →
  (einst ξ t) <[ ups k σ ] = einst (subst_eargs (ups k σ) ξ) t.
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

(** Note:

  It is a bit silly because the context is ignored for conversion (for now).

**)
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

Lemma subst_eargs_ext σ θ ξ :
  (∀ n, σ n = θ n) →
  subst_eargs σ ξ = subst_eargs θ ξ.
Proof.
  intros h.
  apply map_ext. intro.
  apply map_ext. intro.
  apply ext_term. assumption.
Qed.

Lemma ren_subst_eargs ρ σ ξ :
  ren_eargs ρ (subst_eargs σ ξ) = subst_eargs (σ >> (ren_term ρ)) ξ.
Proof.
  rewrite map_map. apply map_ext. intro.
  rewrite map_map. apply map_ext. intro.
  rasimpl. reflexivity.
Qed.

Lemma subst_ren_eargs ρ σ ξ :
  subst_eargs σ (ren_eargs ρ ξ) = subst_eargs (ρ >> σ) ξ.
Proof.
  rewrite map_map. apply map_ext. intro.
  rewrite map_map. apply map_ext. intro.
  rasimpl. reflexivity.
Qed.

Corollary liftn_subst_eargs n σ ξ :
  liftn n (subst_eargs σ ξ) = subst_eargs (ups n σ) (liftn n ξ).
Proof.
  rewrite subst_ren_eargs. rewrite ren_subst_eargs.
  apply subst_eargs_ext. intro m.
  unfold core.funcomp.
  induction n as [| n ih] in m, σ |- *.
  - cbn. rasimpl. reflexivity.
  - cbn. unfold core.funcomp. rewrite <- ih.
    rasimpl. reflexivity.
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
    apply All_forallb. apply All_map.
    apply forallb_All in h2.
    eapply All_prod in h1. 2: eassumption.
    eapply All_impl. 2: eassumption. clear.
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

Lemma scoped_einst k l ξ t :
  scoped_eargs l ξ = true →
  scoped k t = true →
  scoped (k + l) (einst (liftn k ξ) t) = true.
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
    cbn. intros σ [h1 h2].
    apply All_forallb. apply All_map.
    apply forallb_All in h2.
    eapply All_prod in h1. 2: eassumption.
    eapply All_impl. 2: eassumption. clear - hξ.
    cbn. intros t [h1 h2]. eauto.
  - cbn. rewrite eget_ren. unfold eget.
    destruct nth_error as [σ |] eqn: eM. 2: reflexivity.
    destruct (nth_error σ _) eqn: ex. 2: reflexivity.
    apply nth_error_In in eM, ex.
    rewrite forallb_forall in hξ. specialize hξ with (1 := eM).
    rewrite forallb_forall in hξ. specialize hξ with (1 := ex).
    eapply scoped_lift. assumption.
Qed.

Corollary scoped_einst_closed k ξ t :
  scoped_eargs k ξ = true →
  closed t = true →
  scoped k (einst ξ t) = true.
Proof.
  intros hξ ht.
  eapply scoped_einst in hξ. 2: eassumption.
  cbn in hξ. rewrite ren_eargs_id in hξ. assumption.
Qed.

Corollary closed_einst ξ t :
  closed_eargs ξ = true →
  closed t = true →
  closed (einst ξ t) = true.
Proof.
  intros hξ ht.
  apply scoped_einst_closed. all: assumption.
Qed.

Lemma inst_typing_subst Σ Ξ Δ Γ σ ξ Ξ' :
  styping Σ Ξ Δ σ Γ →
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing_ Σ Ξ (λ Γ t A,
    ∀ Δ σ, styping Σ Ξ Δ σ Γ → Σ ;; Ξ | Δ ⊢ t <[ σ ] : A <[ σ ]
  ) Γ ξ Ξ' →
  inst_typing Σ Ξ Δ (subst_eargs σ ξ) Ξ'.
Proof.
  intros hσ [h1 [h2 h3]] [ih1 [ih2 ih3]].
  split. 2: split.
  - intros E M ξ' hM.
    specialize (h1 _ _ _ hM) as (Ξ'' & Δ' & R & e & h).
    eexists _,_,_. split. 1: eauto.
    intros n rule hn m δ Θ lhs0 rhs0 hl hr. cbn.
    rewrite liftn_subst_eargs.
    (* forward *)
    specialize h with (1 := hn) (2 := hl) (3 := hr). cbn in h.
    fold m δ lhs0 rhs0 in h.
    eapply conv_subst with (σ := ups m σ) in h.
    erewrite 2!subst_inst_ups in h. 2,3: eassumption.
    eassumption.
  - intros M E ξ' e. specialize (ih2 _ _ _ e) as [? [? [? [? [? [? ih2]]]]]].
    split. 1: assumption.
    eexists _,_,_. split. 1: eassumption.
    split.
    1:{
      rewrite nth_error_map, onSome_map. setoid_rewrite length_map. assumption.
    }
    intros ?? h.
    rewrite eget_subst. eapply meta_conv.
    + eauto.
    + apply subst_inst_closed. apply closed_delocal.
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
  - cbn. rewrite closed_subst. 2: eapply closed_delocal.
    econstructor. all: eassumption.
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

Lemma ctx_einst_app ξ Γ Δ :
  ctx_einst ξ (Γ ,,, Δ) = ctx_einst ξ Γ ,,, ctx_einst (liftn (length Γ) ξ) Δ.
Proof.
  induction Δ as [| A Δ ih] in Γ |- *.
  - reflexivity.
  - cbn. f_equal. 2: eauto.
    rewrite liftn_liftn. rewrite length_app. reflexivity.
Qed.

Lemma einst_eget ξ ξ' M x :
  einst ξ (eget ξ' M x) = eget (einst_eargs ξ ξ') M x.
Proof.
  unfold eget. rewrite nth_error_map.
  destruct nth_error. 2: reflexivity.
  cbn. rewrite nth_error_map.
  destruct nth_error. 2: reflexivity.
  reflexivity.
Qed.

Lemma einst_einst ξ ξ' t :
  einst ξ (einst ξ' t) = einst (einst_eargs ξ ξ') t.
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

Lemma liftn_map_map n ξ ξ' :
  liftn n (einst_eargs ξ ξ') = einst_eargs (liftn n ξ) (liftn n ξ').
Proof.
  rewrite !map_map. apply map_ext. intro.
  rewrite !map_map. apply map_ext. intro.
  rewrite ren_inst. reflexivity.
Qed.

Lemma ctx_einst_comp ξ ξ' Γ :
  ctx_einst ξ (ctx_einst ξ' Γ) = ctx_einst (einst_eargs ξ ξ') Γ.
Proof.
  induction Γ as [| A Γ ih].
  - reflexivity.
  - cbn. rewrite ih. f_equal. rewrite einst_einst. f_equal.
    rewrite length_ctx_einst.
    rewrite liftn_map_map. reflexivity.
Qed.

Lemma conv_equations Σ Ξ Ξ' Γ ξ M E ξ' Ξ'' Δ R n rule :
  inst_equations Σ Ξ Γ ξ Ξ' →
  ectx_get Ξ' M = Some (E, ξ') →
  Σ E = Some (Ext Ξ'' Δ R) →
  nth_error R n = Some rule →
  let m := length rule.(cr_env) in
  let δ := length Δ in
  let Θ := ctx_einst ξ (ctx_einst ξ' rule.(cr_env)) in
  let lhs0 := rule_lhs M ξ' δ rule in
  let rhs0 := rule_rhs M ξ' δ rule in
  scoped m lhs0 = true →
  scoped m rhs0 = true →
  let lhs := einst (liftn m ξ) lhs0 in
  let rhs := einst (liftn m ξ) rhs0 in
  Σ ;; Ξ | Γ ,,, Θ ⊢ lhs ≡ rhs.
Proof.
  intros hξ hM hE hn m δ Θ lhs0 rhs0 hl hr.
  specialize (hξ _ _ _ hM) as [? [? [? [e h]]]].
  rewrite e in hE. inversion hE. subst.
  eauto.
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
  - erewrite ext_term_scoped. 3: eapply eq_subst_trunc. 2: eassumption.
    erewrite (ext_term_scoped _ rhs).
    3: eapply eq_subst_trunc. 2: eassumption.
    erewrite 2!subst_inst. 2,3: eapply trunc_bounds.
    eapply conv_subst.
    eapply conv_equations. all: eassumption.
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
Qed.

Corollary conv_einst_closed Σ Ξ Ξ' Δ u v ξ :
  inst_equations Σ Ξ Δ ξ Ξ' →
  Σ ;; Ξ' | ∙ ⊢ u ≡ v →
  Σ ;; Ξ | Δ ⊢ einst ξ u ≡ einst ξ v.
Proof.
  intros hξ h.
  eapply conv_einst in h. 2: eassumption.
  cbn in h. rewrite ren_eargs_id_ext in h. 2: auto.
  assumption.
Qed.

Lemma type_eget Σ Ξ Ξ' Γ ξ M x E ξ' Ξ'' Δ R A :
  inst_eget Σ Ξ Γ ξ Ξ' →
  ectx_get Ξ' M = Some (E, ξ') →
  Σ E = Some (Ext Ξ'' Δ R) →
  nth_error Δ x = Some A →
  Σ ;; Ξ | Γ ⊢ eget ξ M x : einst ξ (delocal M (einst ξ' (plus (S x) ⋅ A))).
Proof.
  intros hξ hM hE hx.
  specialize (hξ _ _ _ hM) as [? [? [? [? [e hξ]]]]].
  rewrite e in hE. inversion hE. subst.
  intuition eauto.
Qed.

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
      rewrite liftn_liftn.
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
      destruct H1 as [? [? ?]].
      split. 2: split.
      * intros E M ξ' hM.
        specialize (H1 _ _ _ hM) as (Ξ'' & Δ' & R & e & h).
        eexists _,_,_. split. 1: eauto.
        intros n rule hn m δ ??? hl hr. cbn.
        (* forward for now *)
        specialize h with (1 := hn) (2 := hl) (3 := hr).
        eapply conv_einst in h. 2: apply hξ.
        rewrite ctx_einst_app in h. rewrite <- app_assoc in h.
        rewrite ctx_einst_comp in h.
        rewrite !length_app in h. rewrite !length_ctx_einst in h.
        fold δ m rξ in h.
        rewrite !einst_einst in h.
        rewrite liftn_map_map. subst rξ.
        rewrite liftn_liftn.
        assumption.
      * rename H3 into ih2.
        intros M E ξ' e.
        specialize (ih2 _ _ _ e) as [? [? [? [? [? [? ih2]]]]]].
        split. 1: assumption.
        eexists _,_,_. split. 1: eassumption.
        split.
        1:{
          rewrite nth_error_map, onSome_map. setoid_rewrite length_map.
          assumption.
        }
        intros ?? h.
        rewrite <- einst_eget. rewrite <- einst_einst.
        eauto.
      * rewrite length_map. assumption.
    + rewrite einst_einst. reflexivity.
  - cbn. subst rξ. rewrite eget_ren.
    eapply meta_conv.
    + eapply typing_ren.
      1:{ erewrite <- length_ctx_einst. eapply rtyping_add. }
      eapply type_eget. 2-4: eassumption.
      apply hξ.
    + rewrite ren_inst. f_equal.
      apply closed_ren. apply closed_delocal.
  - econstructor. 1,3: eauto.
    eapply conv_einst. 2: eassumption.
    apply hξ.
Qed.

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

Lemma conv_einsts Σ Ξ Γ t ξ ξ' :
  Forall2 (Forall2 (conversion Σ Ξ Γ)) ξ ξ' →
  Σ ;; Ξ | Γ ⊢ einst ξ t ≡ einst ξ' t.
Proof.
  intros hξ.
  induction t using term_rect in Γ, ξ, ξ', hξ |- *.
  all: try solve [ cbn ; ttconv ].
  - cbn. eapply cong_Pi. 1: eauto.
    eapply IHt2. eapply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros.
    eapply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros. eapply conv_ren. eassumption.
  - cbn. eapply cong_lam. 1: eauto.
    eapply IHt2. eapply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros.
    eapply Forall2_map_l, Forall2_map_r.
    eapply Forall2_impl. 2: eassumption.
    intros. eapply conv_ren. eassumption.
  - cbn. eapply cong_const.
    eapply Forall2_map_l, Forall2_map_r.
    eapply Forall2_diag. eapply All_Forall.
    eapply All_impl. 2: eassumption.
    intros.
    eapply Forall2_map_l, Forall2_map_r.
    eapply Forall2_diag. eapply All_Forall.
    eapply All_impl. 2: eassumption.
    cbn. intros. eauto.
  - cbn. unfold eget. destruct (nth_error ξ _) as [σ1 |] eqn:e1.
    2:{
      destruct (nth_error ξ' _) eqn:e2.
      1:{
        eapply nth_error_None in e1. eapply Forall2_length in hξ.
        rewrite hξ in e1. rewrite <- nth_error_None in e1. congruence.
      }
      ttconv.
    }
    eapply Forall2_nth_error_l in e1 as e2. 2: eassumption.
    destruct e2 as (σ2 & e2 & h). rewrite e2.
    destruct (nth_error σ1 _) as [u1 |] eqn:e3.
    2:{
      destruct (nth_error σ2 _) eqn:e4.
      1:{
        eapply nth_error_None in e3. eapply Forall2_length in h.
        rewrite h in e3. rewrite <- nth_error_None in e3. congruence.
      }
      ttconv.
    }
    eapply Forall2_nth_error_l in e3 as e4. 2: eassumption.
    destruct e4 as (u2 & e4 & h'). rewrite e4.
    assumption.
Qed.

Lemma cong_einst Σ Ξ Γ u v ξ ξ' Ξ' :
  inst_equations Σ Ξ Γ ξ Ξ' →
  Σ ;; Ξ' | ∙ ⊢ u ≡ v →
  Forall2 (Forall2 (conversion Σ Ξ Γ)) ξ ξ' →
  Σ ;; Ξ | Γ ⊢ einst ξ u ≡ einst ξ' v.
Proof.
  intros hξ h hh.
  eapply conv_trans.
  - eapply conv_einst_closed. all: eassumption.
  - eapply conv_einsts. assumption.
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
  econstructor. 1,3-5: eauto.
  apply ectx_get_weak. eassumption.
Qed.

Lemma inst_equations_eweak Σ Ξ d Γ ξ Ξ' :
  inst_equations Σ Ξ Γ ξ Ξ' →
  inst_equations Σ (d :: Ξ) Γ ξ Ξ'.
Proof.
  intros h.
  intros E M ξ' hM.
  specialize (h _ _ _ hM) as (Ξ'' & Δ & R & e & h).
  eexists _,_,_. split. 1: eauto.
  intros n rule hn m δ θ lhs0 rhs0 hl hr.
  eapply conv_eweak. eauto.
Qed.

Lemma inst_eget_eweak Σ Ξ d Γ ξ Ξ' :
  inst_eget Σ Ξ Γ ξ Ξ' →
  inst_eget_ Σ (λ Γ t A, Σ ;; d :: Ξ | Γ ⊢ t : A) Γ ξ Ξ' →
  inst_eget Σ (d :: Ξ) Γ ξ Ξ'.
Proof.
  intros h ih.
  intros M E ξ' e. specialize (ih _ _ _ e) as [? [? [? [? [? ih]]]]].
  split. 1: assumption.
  eexists _,_,_. split. 1: eassumption.
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
  - eapply inst_eget_eweak. all: eassumption.
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
  - econstructor. 2-4: eauto.
    eapply ectx_get_weak. assumption.
  - econstructor. 1,3: eassumption.
    eapply conv_eweak. all: eauto.
Qed.

Lemma inst_typing_eweak Σ Ξ d Γ ξ Ξ' :
  inst_typing Σ Ξ Γ ξ Ξ' →
  inst_typing Σ (d :: Ξ) Γ ξ Ξ'.
Proof.
  intros h.
  eapply inst_typing_eweak_. 1: eassumption.
  destruct h as [h1 [h2 h3]]. split. 2: split.
  - assumption.
  - intros M E ξ' e. specialize (h2 _ _ _ e) as [? [? [? [? [? [? ih]]]]]].
    split. 1: assumption.
    eexists _,_,_. split. 1: eassumption.
    split. 1: assumption.
    eauto using typing_eweak.
  - assumption.
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
  intros h hle.
  intros E M ξ' hM.
  specialize (h _ _ _ hM) as (Ξ'' & Δ & R & e & h).
  eexists _,_,_. split. 1: eauto.
  intros n rule hn m δ θ lhs0 rhs0 hl hr.
  eapply conv_gweak. 2: eassumption.
  eapply h. all: eassumption.
Qed.

Lemma inst_eget_gweak Σ Σ' Ξ Γ ξ Ξ' :
  inst_eget Σ Ξ Γ ξ Ξ' →
  inst_eget_ Σ (λ Γ t A, Σ' ;; Ξ | Γ ⊢ t : A) Γ ξ Ξ' →
  Σ ⊑ Σ' →
  inst_eget Σ' Ξ Γ ξ Ξ'.
Proof.
  intros h ih hle.
  intros M E ξ' e. specialize (ih _ _ _ e) as [? [? [? [? [? ih]]]]].
  split. 1: assumption.
  eexists _,_,_. split.
  - eapply hle. eassumption.
  - eapply ih.
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
  - eapply inst_eget_gweak. all: eassumption.
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
  - intros M E ξ' e. specialize (h2 _ _ _ e) as [? [? [? [? [? [? h2]]]]]].
    split. 1: assumption.
    eexists _,_,_. split. 1: eassumption. split. 1: assumption.
    eauto using typing_gweak.
  - assumption.
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

Lemma rule_typing_gweak Σ Σ' Ξ Δ r :
  rule_typing Σ Ξ Δ r →
  Σ ⊑ Σ' →
  rule_typing Σ' Ξ Δ r.
Proof.
  intros (hctx & [i hty] & hl & hr) hle.
  unfold rule_typing.
  intuition eauto using typing_gweak, wf_gweak.
Qed.

Lemma wf_rules_gweak Σ Σ' Ξ Δ R :
  Forall (rule_typing Σ Ξ Δ) R →
  Σ ⊑ Σ' →
  Forall (rule_typing Σ' Ξ Δ) R.
Proof.
  intros h hle.
  eapply Forall_impl. 2: eassumption.
  intros. eauto using rule_typing_gweak.
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

Lemma ectx_get_case d Ξ M i :
  ectx_get (d :: Ξ) M = Some i →
  (M = length Ξ ∧ d = i) ∨ (ectx_get Ξ M = Some i).
Proof.
  intro h.
  unfold ectx_get in h.
  destruct (_ <=? _) eqn: e. 1: discriminate.
  rewrite Nat.leb_gt in e. cbn in e.
  cbn in h.
  destruct (length Ξ - M) eqn: e'.
  - left. cbn in h. inversion h.
    intuition lia.
  - right. cbn in h.
    unfold ectx_get.
    destruct (_ <=? _) eqn: e2.
    1:{ rewrite Nat.leb_le in e2. lia. }
    rewrite <- h. f_equal. lia.
Qed.

Lemma valid_ewf Σ Ξ M E ξ :
  ewf Σ Ξ →
  ectx_get Ξ M = Some (E, ξ) →
  ∃ Ξ' Δ R,
    Σ E = Some (Ext Ξ' Δ R) ∧
    inst_typing Σ Ξ ∙ ξ Ξ'.
Proof.
  intros hΞ e.
  induction hΞ as [ | Ξ E' ξ' Ξ' Δ R h ih he hξ ].
  1:{ destruct M. all: discriminate. }
  eapply ectx_get_case in e as eh. destruct eh as [[-> eh] | eh].
  - inversion eh. subst.
    eexists _,_,_. split. 1: eassumption.
    eapply inst_typing_eweak. assumption.
  - specialize (ih eh) as [? [? [? []]]].
    eexists _,_,_. split. 1: eassumption.
    eapply inst_typing_eweak. assumption.
Qed.

Corollary valid_ewf_alt Σ Ξ M E ξ Ξ' Δ R :
  ewf Σ Ξ →
  ectx_get Ξ M = Some (E, ξ) →
  Σ E = Some (Ext Ξ' Δ R) →
  inst_typing Σ Ξ ∙ ξ Ξ'.
Proof.
  intros hΞ hM hE.
  eapply valid_ewf in hM. 2: eassumption.
  destruct hM as [? [? [? [e ?]]]].
  rewrite e in hE. inversion hE. subst.
  assumption.
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
  ewf Σ Ξ ∧
  (∃ i, Σ ;; Ξ | ∙ ⊢ A : Sort i) ∧
  Σ ;; Ξ | ∙ ⊢ t : A.
Proof.
  intros hΣ hc.
  induction hΣ as [ | c' ?????? ih | c' ??????? ih ] in c, Ξ, A, t, hc |- *.
  - discriminate.
  - cbn in hc. destruct (c =? c')%string. 1: discriminate.
    specialize ih with (1 := hc) as [? [[i ?] ?]].
    split. 2: split.
    + eapply ewf_gweak. all: eauto using extends_gcons.
    + eexists. eapply typing_gweak. all: eauto using extends_gcons.
    + eapply typing_gweak. all: eauto using extends_gcons.
  - cbn in hc. destruct (c =? c')%string.
    + inversion hc. subst.
      intuition eauto using ewf_gweak, typing_gweak, extends_gcons.
    + specialize ih with (1 := hc) as [? [[j ?] ?]].
      intuition eauto using ewf_gweak, typing_gweak, extends_gcons.
Qed.

Lemma valid_ext Σ c Ξ Δ R :
  gwf Σ →
  Σ c = Some (Ext Ξ Δ R) →
  ewf Σ Ξ ∧ wf Σ Ξ Δ ∧ Forall (rule_typing Σ Ξ Δ) R.
Proof.
  intros hΣ hc.
  induction hΣ as [ | c' ?????? ih | c' ??????? ih ] in c, Ξ, Δ, R, hc |- *.
  - discriminate.
  - cbn in hc. destruct (c =? c')%string.
    + inversion hc. subst.
      intuition eauto
      using wf_gweak, ewf_gweak, typing_gweak, extends_gcons, wf_rules_gweak.
    + specialize ih with (1 := hc) as [? ?].
      intuition eauto
      using wf_gweak, ewf_gweak, typing_gweak, extends_gcons, wf_rules_gweak.
  - cbn in hc. destruct (c =? c')%string. 1: discriminate.
    specialize ih with (1 := hc) as [? ?].
    intuition eauto
    using wf_gweak, ewf_gweak, typing_gweak, extends_gcons, wf_rules_gweak.
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
    destruct h as (hΞ' & hΔ & hR).
    eapply valid_wf in hΔ as hA. 2: eassumption.
    destruct hA as [i hA].
    exists i. eapply typing_lift_closed.
    2: reflexivity.
    eapply valid_ewf_alt in hΞ as hξ. 2,3: eassumption.
    eapply typing_einst in hA. 2: eassumption.
    cbn in hA. rewrite app_nil_r in hA.
    rewrite closed_ren_eargs in hA. 2: assumption.
    unfold delocal. eapply meta_conv.
    + eapply typing_subst. 2: eassumption.
      rewrite styping_alt_equiv. intros y B e.
      rewrite nth_error_ctx_einst in e.
      destruct (nth_error Δ y) eqn:e2. 2: discriminate.
      cbn in e. inversion e. subst. clear e.
      eapply meta_conv.
      * econstructor. all: eassumption.
      * rewrite closed_ren_eargs. 2: assumption.
        rewrite ren_inst.
        rewrite closed_ren_eargs. 2: assumption.
        reflexivity.
    + reflexivity.
  - eexists. eassumption.
Qed.

(** Induction principle for [typing], threading [wf] **)

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
      P Γ (const c ξ) (einst ξ A)
    ) →
    (∀ Γ M x E ξ Ξ' Δ R A,
      wf Σ Ξ Γ →
      ectx_get Ξ M = Some (E, ξ) →
      Σ E = Some (Ext Ξ' Δ R) →
      nth_error Δ x = Some A →
      closed_eargs ξ = true →
      P Γ (assm M x) (delocal M (einst ξ ((plus (S x)) ⋅ A)))
    ) →
    (∀ Γ i A B t,
      wf Σ Ξ Γ →
      Σ ;; Ξ | Γ ⊢ t : A →
      P Γ t A →
      Σ ;; Ξ | Γ ⊢ A ≡ B →
      Σ ;; Ξ | Γ ⊢ B : Sort i →
      P Γ B (Sort i) →
      P Γ t B
    ) →
    ∀ Γ t A, wf Σ Ξ Γ → Σ ;; Ξ | Γ ⊢ t : A → P Γ t A.
Proof.
  intros Σ Ξ P hvar hsort hpi hlam happ hconst hassm hconv.
  intros Γ t A hΓ h.
  induction h using typing_ind.
  all: try solve [ eauto ].
  - assert (hΓA : wf Σ Ξ (Γ ,, A)).
    { econstructor. all: eassumption. }
    eauto.
  - assert (hΓA : wf Σ Ξ (Γ ,, A)).
    { econstructor. all: eassumption. }
    eauto.
  - assert (hΓA : wf Σ Ξ (Γ ,, A)).
    { econstructor. all: eassumption. }
    eapply happ. all: eauto.
Qed.
