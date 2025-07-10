From LocalComp.autosubst Require Import core unscoped.
From LocalComp Require Import BasicAST.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Module Core.

Inductive term : Type :=
  | var : nat -> term
  | Sort : level -> term
  | Pi : term -> term -> term
  | lam : term -> term -> term
  | app : term -> term -> term
  | const : gref -> list (option (term)) -> term
  | assm : aref -> term.

Lemma congr_Sort {s0 : level} {t0 : level} (H0 : s0 = t0) : Sort s0 = Sort t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => Sort x) H0)).
Qed.

Lemma congr_Pi {s0 : term} {s1 : term} {t0 : term} {t1 : term} (H0 : s0 = t0)
  (H1 : s1 = t1) : Pi s0 s1 = Pi t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Pi x s1) H0))
         (ap (fun x => Pi t0 x) H1)).
Qed.

Lemma congr_lam {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : lam s0 s1 = lam t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lam x s1) H0))
         (ap (fun x => lam t0 x) H1)).
Qed.

Lemma congr_app {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : app s0 s1 = app t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app x s1) H0))
         (ap (fun x => app t0 x) H1)).
Qed.

Lemma congr_const {s0 : gref} {s1 : list (option (term))} {t0 : gref}
  {t1 : list (option (term))} (H0 : s0 = t0) (H1 : s1 = t1) :
  const s0 s1 = const t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => const x s1) H0))
         (ap (fun x => const t0 x) H1)).
Qed.

Lemma congr_assm {s0 : aref} {t0 : aref} (H0 : s0 = t0) : assm s0 = assm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => assm x) H0)).
Qed.

Lemma upRen_term_term (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_term (xi_term : nat -> nat) (s : term) {struct s} : term :=
  match s with
  | var s0 => var (xi_term s0)
  | Sort s0 => Sort s0
  | Pi s0 s1 =>
      Pi (ren_term xi_term s0) (ren_term (upRen_term_term xi_term) s1)
  | lam s0 s1 =>
      lam (ren_term xi_term s0) (ren_term (upRen_term_term xi_term) s1)
  | app s0 s1 => app (ren_term xi_term s0) (ren_term xi_term s1)
  | const s0 s1 => const s0 (list_map (option_map (ren_term xi_term)) s1)
  | assm s0 => assm s0
  end.

Lemma up_term_term (sigma : nat -> term) : nat -> term.
Proof.
exact (scons (var var_zero) (funcomp (ren_term shift) sigma)).
Defined.

Fixpoint subst_term (sigma_term : nat -> term) (s : term) {struct s} : 
term :=
  match s with
  | var s0 => sigma_term s0
  | Sort s0 => Sort s0
  | Pi s0 s1 =>
      Pi (subst_term sigma_term s0) (subst_term (up_term_term sigma_term) s1)
  | lam s0 s1 =>
      lam (subst_term sigma_term s0)
        (subst_term (up_term_term sigma_term) s1)
  | app s0 s1 => app (subst_term sigma_term s0) (subst_term sigma_term s1)
  | const s0 s1 =>
      const s0 (list_map (option_map (subst_term sigma_term)) s1)
  | assm s0 => assm s0
  end.

Lemma upId_term_term (sigma : nat -> term) (Eq : forall x, sigma x = var x) :
  forall x, up_term_term sigma x = var x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_term (sigma_term : nat -> term)
(Eq_term : forall x, sigma_term x = var x) (s : term) {struct s} :
subst_term sigma_term s = s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 => congr_Sort (eq_refl s0)
  | Pi s0 s1 =>
      congr_Pi (idSubst_term sigma_term Eq_term s0)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
  | lam s0 s1 =>
      congr_lam (idSubst_term sigma_term Eq_term s0)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
  | app s0 s1 =>
      congr_app (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
  | const s0 s1 =>
      congr_const (eq_refl s0)
        (list_id (option_id (idSubst_term sigma_term Eq_term)) s1)
  | assm s0 => congr_assm (eq_refl s0)
  end.

Lemma upExtRen_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_term_term xi x = upRen_term_term zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(Eq_term : forall x, xi_term x = zeta_term x) (s : term) {struct s} :
ren_term xi_term s = ren_term zeta_term s :=
  match s with
  | var s0 => ap (var) (Eq_term s0)
  | Sort s0 => congr_Sort (eq_refl s0)
  | Pi s0 s1 =>
      congr_Pi (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
  | lam s0 s1 =>
      congr_lam (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
  | app s0 s1 =>
      congr_app (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  | const s0 s1 =>
      congr_const (eq_refl s0)
        (list_ext (option_ext (extRen_term xi_term zeta_term Eq_term)) s1)
  | assm s0 => congr_assm (eq_refl s0)
  end.

Lemma upExt_term_term (sigma : nat -> term) (tau : nat -> term)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_term_term sigma x = up_term_term tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_term (sigma_term : nat -> term) (tau_term : nat -> term)
(Eq_term : forall x, sigma_term x = tau_term x) (s : term) {struct s} :
subst_term sigma_term s = subst_term tau_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 => congr_Sort (eq_refl s0)
  | Pi s0 s1 =>
      congr_Pi (ext_term sigma_term tau_term Eq_term s0)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
  | lam s0 s1 =>
      congr_lam (ext_term sigma_term tau_term Eq_term s0)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
  | app s0 s1 =>
      congr_app (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
  | const s0 s1 =>
      congr_const (eq_refl s0)
        (list_ext (option_ext (ext_term sigma_term tau_term Eq_term)) s1)
  | assm s0 => congr_assm (eq_refl s0)
  end.

Lemma up_ren_ren_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_term_term zeta) (upRen_term_term xi) x =
  upRen_term_term rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(rho_term : nat -> nat)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : term)
{struct s} : ren_term zeta_term (ren_term xi_term s) = ren_term rho_term s :=
  match s with
  | var s0 => ap (var) (Eq_term s0)
  | Sort s0 => congr_Sort (eq_refl s0)
  | Pi s0 s1 =>
      congr_Pi (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s1)
  | lam s0 s1 =>
      congr_lam (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s1)
  | app s0 s1 =>
      congr_app (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | const s0 s1 =>
      congr_const (eq_refl s0)
        (list_comp
           (option_comp (compRenRen_term xi_term zeta_term rho_term Eq_term))
           s1)
  | assm s0 => congr_assm (eq_refl s0)
  end.

Lemma up_ren_subst_term_term (xi : nat -> nat) (tau : nat -> term)
  (theta : nat -> term) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_term_term tau) (upRen_term_term xi) x = up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : term)
{struct s} :
subst_term tau_term (ren_term xi_term s) = subst_term theta_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 => congr_Sort (eq_refl s0)
  | Pi s0 s1 =>
      congr_Pi (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
  | lam s0 s1 =>
      congr_lam (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
  | app s0 s1 =>
      congr_app (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | const s0 s1 =>
      congr_const (eq_refl s0)
        (list_comp
           (option_comp
              (compRenSubst_term xi_term tau_term theta_term Eq_term))
           s1)
  | assm s0 => congr_assm (eq_refl s0)
  end.

Lemma up_subst_ren_term_term (sigma : nat -> term) (zeta_term : nat -> nat)
  (theta : nat -> term)
  (Eq : forall x, funcomp (ren_term zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_term (upRen_term_term zeta_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_term shift (upRen_term_term zeta_term)
                (funcomp shift zeta_term) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_term zeta_term shift (funcomp shift zeta_term)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_term (sigma_term : nat -> term)
(zeta_term : nat -> nat) (theta_term : nat -> term)
(Eq_term : forall x, funcomp (ren_term zeta_term) sigma_term x = theta_term x)
(s : term) {struct s} :
ren_term zeta_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 => congr_Sort (eq_refl s0)
  | Pi s0 s1 =>
      congr_Pi (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
  | lam s0 s1 =>
      congr_lam
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
  | app s0 s1 =>
      congr_app
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | const s0 s1 =>
      congr_const (eq_refl s0)
        (list_comp
           (option_comp
              (compSubstRen_term sigma_term zeta_term theta_term Eq_term))
           s1)
  | assm s0 => congr_assm (eq_refl s0)
  end.

Lemma up_subst_subst_term_term (sigma : nat -> term) (tau_term : nat -> term)
  (theta : nat -> term)
  (Eq : forall x, funcomp (subst_term tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_term shift (up_term_term tau_term)
                (funcomp (up_term_term tau_term) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_term tau_term shift
                      (funcomp (ren_term shift) tau_term) (fun x => eq_refl)
                      (sigma n')))
                (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_term (sigma_term : nat -> term)
(tau_term : nat -> term) (theta_term : nat -> term)
(Eq_term : forall x,
           funcomp (subst_term tau_term) sigma_term x = theta_term x)
(s : term) {struct s} :
subst_term tau_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 => congr_Sort (eq_refl s0)
  | Pi s0 s1 =>
      congr_Pi
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
  | lam s0 s1 =>
      congr_lam
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
  | app s0 s1 =>
      congr_app
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | const s0 s1 =>
      congr_const (eq_refl s0)
        (list_comp
           (option_comp
              (compSubstSubst_term sigma_term tau_term theta_term Eq_term))
           s1)
  | assm s0 => congr_assm (eq_refl s0)
  end.

Lemma renRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat) (s : term)
  :
  ren_term zeta_term (ren_term xi_term s) =
  ren_term (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_term_pointwise (xi_term : nat -> nat) (zeta_term : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_term zeta_term) (ren_term xi_term))
    (ren_term (funcomp zeta_term xi_term)).
Proof.
exact (fun s => compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (ren_term xi_term s) =
  subst_term (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term_pointwise (xi_term : nat -> nat) (tau_term : nat -> term)
  :
  pointwise_relation _ eq (funcomp (subst_term tau_term) (ren_term xi_term))
    (subst_term (funcomp tau_term xi_term)).
Proof.
exact (fun s => compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term (sigma_term : nat -> term) (zeta_term : nat -> nat)
  (s : term) :
  ren_term zeta_term (subst_term sigma_term s) =
  subst_term (funcomp (ren_term zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term_pointwise (sigma_term : nat -> term)
  (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_term zeta_term) (subst_term sigma_term))
    (subst_term (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (fun s => compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term (sigma_term : nat -> term) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (subst_term sigma_term s) =
  subst_term (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term_pointwise (sigma_term : nat -> term)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_term tau_term) (subst_term sigma_term))
    (subst_term (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_term_term (xi : nat -> nat) (sigma : nat -> term)
  (Eq : forall x, funcomp (var) xi x = sigma x) :
  forall x, funcomp (var) (upRen_term_term xi) x = up_term_term sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_term (xi_term : nat -> nat) (sigma_term : nat -> term)
(Eq_term : forall x, funcomp (var) xi_term x = sigma_term x) (s : term)
{struct s} : ren_term xi_term s = subst_term sigma_term s :=
  match s with
  | var s0 => Eq_term s0
  | Sort s0 => congr_Sort (eq_refl s0)
  | Pi s0 s1 =>
      congr_Pi (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
  | lam s0 s1 =>
      congr_lam (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
  | app s0 s1 =>
      congr_app (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | const s0 s1 =>
      congr_const (eq_refl s0)
        (list_ext (option_ext (rinst_inst_term xi_term sigma_term Eq_term))
           s1)
  | assm s0 => congr_assm (eq_refl s0)
  end.

Lemma rinstInst'_term (xi_term : nat -> nat) (s : term) :
  ren_term xi_term s = subst_term (funcomp (var) xi_term) s.
Proof.
exact (rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_term xi_term)
    (subst_term (funcomp (var) xi_term)).
Proof.
exact (fun s => rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma instId'_term (s : term) : subst_term (var) s = s.
Proof.
exact (idSubst_term (var) (fun n => eq_refl) s).
Qed.

Lemma instId'_term_pointwise : pointwise_relation _ eq (subst_term (var)) id.
Proof.
exact (fun s => idSubst_term (var) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_term (s : term) : ren_term id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma rinstId'_term_pointwise : pointwise_relation _ eq (@ren_term id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma varL'_term (sigma_term : nat -> term) (x : nat) :
  subst_term sigma_term (var x) = sigma_term x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_term_pointwise (sigma_term : nat -> term) :
  pointwise_relation _ eq (funcomp (subst_term sigma_term) (var)) sigma_term.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_term (xi_term : nat -> nat) (x : nat) :
  ren_term xi_term (var x) = var (xi_term x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_term xi_term) (var))
    (funcomp (var) xi_term).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_term X Y :=
    up_term : X -> Y.

#[global] Instance Subst_term : (Subst1 _ _ _) := @subst_term.

#[global] Instance Up_term_term : (Up_term _ _) := @up_term_term.

#[global] Instance Ren_term : (Ren1 _ _ _) := @ren_term.

#[global]
Instance VarInstance_term : (Var _ _) := @var.

Notation "s [ sigma_term ]" := (subst_term sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__term" := up_term (only printing)  : subst_scope.

Notation "↑__term" := up_term_term (only printing)  : subst_scope.

Notation "s ⟨ xi_term ⟩" := (ren_term xi_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var ( at level 1, only printing)  : subst_scope.

Notation "x '__term'" := (@ids _ _ VarInstance_term x)
( at level 5, format "x __term", only printing)  : subst_scope.

Notation "x '__term'" := (var x) ( at level 5, format "x __term")  :
subst_scope.

#[global]
Instance subst_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_term f_term s = subst_term g_term t')
         (ext_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_term)).
Proof.
exact (fun f_term g_term Eq_term s => ext_term f_term g_term Eq_term s).
Qed.

#[global]
Instance ren_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_term f_term s = ren_term g_term t')
         (extRen_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_term)).
Proof.
exact (fun f_term g_term Eq_term s => extRen_term f_term g_term Eq_term s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                      Up_term_term, Up_term, up_term, Subst_term, Subst1,
                      subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_term, Var, ids,
                                            Ren_term, Ren1, ren1,
                                            Up_term_term, Up_term, up_term,
                                            Subst_term, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_term_pointwise
                 | progress setoid_rewrite substSubst_term
                 | progress setoid_rewrite substRen_term_pointwise
                 | progress setoid_rewrite substRen_term
                 | progress setoid_rewrite renSubst_term_pointwise
                 | progress setoid_rewrite renSubst_term
                 | progress setoid_rewrite renRen'_term_pointwise
                 | progress setoid_rewrite renRen_term
                 | progress setoid_rewrite varLRen'_term_pointwise
                 | progress setoid_rewrite varLRen'_term
                 | progress setoid_rewrite varL'_term_pointwise
                 | progress setoid_rewrite varL'_term
                 | progress setoid_rewrite rinstId'_term_pointwise
                 | progress setoid_rewrite rinstId'_term
                 | progress setoid_rewrite instId'_term_pointwise
                 | progress setoid_rewrite instId'_term
                 | progress unfold up_term_term, upRen_term_term, up_ren
                 | progress cbn[subst_term ren_term]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_term, Subst1, subst1
                  in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_term_pointwise;
                  try setoid_rewrite rinstInst'_term.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_term_pointwise;
                  try setoid_rewrite_left rinstInst'_term.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_term: rewrite.

#[global] Hint Opaque ren_term: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

