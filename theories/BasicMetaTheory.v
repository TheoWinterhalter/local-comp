(** Basic meta-theory **)

From Coq Require Import Utf8 List Arith Lia.
From LocalComp.autosubst Require Import unscoped AST SubstNotations RAsimpl
  AST_rasimpl.
From LocalComp Require Import Util BasicAST Env Inst Typing.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

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
      nth_error Σ c = Some (Def Ξ' A t) →
      closed t = true →
      P Γ (const c ξ) (einst ξ t)
    ) →
    (∀ Γ E Ξ' Δ R M ξ' n rule σ,
      nth_error Σ E = Some (Ext Ξ' Δ R) →
      nth_error Ξ M = Some (E, ξ') →
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
      nth_error Σ c = Some (Def Ξ' A t) →
      inst_typing Σ Ξ (typing Σ Ξ) Γ ξ Ξ' →
      inst_typing Σ Ξ P Γ ξ Ξ' →
      P Γ (const c ξ) (einst ξ A)
    ) →
    (∀ Γ M x E ξ Ξ' Δ R A,
      nth_error Ξ M = Some (E, ξ) →
      nth_error Σ E = Some (Ext Ξ' Δ R) →
      nth_error Δ x = Some A → P Γ (assm M x) (einst ξ (delocal M A))
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
    eapply hconst. 1,2: eassumption.
    clear H. revert ξ Ξ' H0. fix aux1 3. intros ξ Ξ' h.
    destruct h as [| σ ξ E ξ' Ξ' Ξ'' Δ R hE h ht heq]. 1: constructor.
    econstructor. 1,4: eassumption. 1: eauto.
    clear - aux aux1 ht.
    remember (map (einst _ >> _) _) as A eqn: e. clear e.
    remember (slist σ) as θ eqn: e. clear e.
    revert θ A ht. fix aux2 3. intros θ A ht.
    destruct ht. 1: constructor.
    constructor. all: eauto.
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

Lemma ren_eargs_comp :
  ∀ ρ ρ' ξ,
    ren_eargs ρ (ren_eargs ρ' ξ) = ren_eargs (ρ' >> ρ) ξ.
Proof.
  intros ρ ρ' ξ.
  unfold ren_eargs. rewrite map_map.
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
  - cbn. unfold eget. unfold ren_eargs.
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

(* Lemma typings_ren Σ Ξ Δ Γ ρ σ Θ :
  rtyping Δ ρ Γ →
  typings (λ Δ t A,
    Σ ;; Ξ | Δ ⊢ t : A ∧ ∀ Θ ρ, rtyping Θ ρ Δ → Σ ;; Ξ | Θ ⊢ ρ ⋅ t : ρ ⋅ A
  ) Γ σ Θ →
  typings (typing Σ Ξ) Δ (map (ren_term ρ) σ) Θ.
Proof.
  intros hi h.
  induction h as [| Θ σ t A h1 h2 h3 ]. 1: constructor.
  cbn. constructor. 1: eauto.
  rasimpl in h3. rasimpl.
  (* Should we somehow exploit closedness or something? *)
Abort. *)

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

Lemma styping_comp_ren Σ Ξ Γ Δ Θ σ ρ :
  styping Σ Ξ Δ σ Θ →
  rtyping Γ ρ Δ →
  styping Σ Ξ Γ (σ >> ren1 ρ) Θ.
Proof.
  intros hσ hρ.
  induction hσ as [| σ Θ A hσ ih h ] in ρ, hρ |- *. 1: constructor.
  constructor. 1: eauto.
  core.unfold_funcomp.
  asimpl.
  admit. (* Only after typing_ren, we can prove the generalised version instead *)
Admitted. (* Admitted for testing *)

Lemma slist_ren σ ρ :
  pointwise_relation _ eq (slist (map (ren_term ρ) σ)) (slist σ >> ren1 ρ).
Proof.
  intro n.
  induction σ in ρ, n |- *.
  - cbn. reflexivity.
  - cbn. destruct n.
    + cbn. reflexivity.
    + cbn. rewrite IHσ. reflexivity.
Qed.

Lemma inst_typing_ren Σ Ξ Δ Γ ρ ξ Ξ' :
  rtyping Δ ρ Γ →
  inst_typing Σ Ξ (typing Σ Ξ) Γ ξ Ξ' →
  inst_typing Σ Ξ (λ Γ t A,
    ∀ Δ ρ, rtyping Δ ρ Γ → Σ ;; Ξ | Δ ⊢ ρ ⋅ t : ρ ⋅ A
  ) Γ ξ Ξ' →
  inst_typing Σ Ξ (typing Σ Ξ) Δ (map (map (ren_term ρ)) ξ) Ξ'.
Proof.
  intros hρ hξ ih.
  eapply inst_typing_and in ih. 2: eapply hξ. clear hξ.
  induction ih as [| σ ξ E ξ' Ξ' Ξ'' Θ R hE h1 h2 h3 h4 ]. 1: constructor.
  cbn. econstructor. all: eauto.
  - setoid_rewrite slist_ren. eapply styping_comp_ren. 2: eassumption.
    (* I guess we need first something to say ρ does nothing on Θ?
      But this isn't really what's happening right?
     *)
    admit.
  - intros n rule hr. cbn. (* m Θ' lhs rhs. *)
    specialize (h4 n rule hr). cbn in h4.
    eapply conv_ren in h4.
Abort.

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
    + admit.
    + rewrite ren_inst. f_equal.
      (* TODO: We need closedness here too right? *)
      admit.
  - rasimpl. eapply meta_conv.
    1:{ econstructor. all: eassumption. }
    rewrite ren_inst.
    admit.
  - rasimpl. rasimpl in IHht2.
    econstructor. all: eauto.
    eapply conv_ren. all: eassumption.
Admitted.
