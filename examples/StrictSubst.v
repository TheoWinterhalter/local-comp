From Stdlib Require List.

Inductive level := lvl (n : nat).
Inductive gref := glob (id : nat).
Inductive aref := arefC (id : nat).

Definition bind (A : Type) := A. (* annotation from Autosubst *)

Inductive term :=
| Var (i : nat)
| Sort (l : level)
| App (f a : term)
| Lambda (A : term) (t : bind term)
| Pi (A : term) (B : bind term)
| Const : gref -> list (option (term)) -> term
| Assm : aref -> term.

Definition map_term {A : Type} on_var up :=
  fix map_term (σ : A) t :=
    match t with
    | Var i => on_var σ i
    | Sort l => Sort l
    | App f a => App (map_term σ f) (map_term σ a)
    | Lambda A t => Lambda (map_term σ A) (map_term (up σ) t)
    | Pi A B => Pi (map_term σ A) (map_term (up σ) B)
    | Const gref inst => Const gref (List.map (option_map (map_term σ)) inst)
    | Assm assm => Assm assm
    end.

Module Type Renaming.

Parameter renaming : Type.

Symbol ren_var : renaming -> nat -> nat.
Symbol up_ren : renaming -> renaming.
Symbol shift_ren : renaming.

Symbol comp_ren : renaming -> renaming -> renaming.
Symbol id_ren : renaming.

Rewrite Rules ren_rew :=
| ren_var (up_ren ?σ) 0 => 0
| ren_var (up_ren ?σ) (S ?n) => S (ren_var ?σ ?n)
| ren_var shift_ren ?n => S ?n
| ren_var (comp_ren ?σ ?τ) ?n => ren_var ?σ (ren_var ?τ ?n)
| ren_var id_ren ?n => ?n
| comp_ren id_ren ?σ => ?σ
| comp_ren ?σ id_ren => ?σ
| comp_ren (comp_ren ?σ ?σ') ?σ'' => comp_ren ?σ (comp_ren ?σ' ?σ'').

End Renaming.


Module Import RenamingFunc : Renaming.

Definition renaming := nat -> nat.
Definition ren_var (ρ : nat -> nat) := ρ.
Definition up_ren ρ n := match n with 0 => 0 | S n => S (ρ n) end.
Definition comp_ren (ρ ρ' : renaming) := fun n => ρ (ρ' n).
Definition id_ren : renaming := fun n => n.
Definition shift_ren := S.

End RenamingFunc.


Definition ren_term := map_term (fun ρ i => Var (ren_var ρ i)) up_ren.

Module Type Substitution.

Parameter substitution : Type.

Symbol subst_var : substitution -> nat -> term.
Symbol up_subst : substitution -> substitution.

Symbol subst_cons : term -> substitution -> substitution.

Symbol comp_subst : (substitution -> term -> term) -> substitution -> substitution -> substitution.
Symbol id_subst : substitution.

Rewrite Rules subst_rew :=
| subst_var (up_subst ?σ) 0 => Var 0
| subst_var (up_subst ?σ) (S ?n) => ren_term shift_ren (subst_var ?σ ?n)
| subst_var (comp_subst ?subst ?σ ?τ) ?n => ?subst ?σ (subst_var ?τ ?n)
| subst_var id_subst ?n => Var ?n.

End Substitution.

Module Import SubstitutionFunc : Substitution.

Definition substitution := nat -> term.
Definition subst_var (ρ : nat -> term) := ρ.
Definition up_subst ρ n := match n with 0 => Var 0 | S n => ren_term shift_ren (ρ n) end.
Definition comp_subst subst (ρ ρ' : substitution) : substitution := fun n => subst ρ (ρ' n).
Definition id_subst : substitution := fun n => Var n.
Definition subst_cons t σ : substitution := fun n => match n with 0 => t | S n => σ n end.

End SubstitutionFunc.

Definition subst_term := map_term subst_var up_subst.
Definition comp_subst := comp_subst subst_term.


Lemma ren_ext ρ ρ' :
  (forall n, ren_var ρ n = ren_var ρ' n) ->
  forall t, ren_term ρ t = ren_term ρ' t.
Proof.
  revert ρ ρ'.
  fix aux 4. destruct t; cbn.
  all: try solve [ try f_equal ; auto ].
  - f_equal; auto.
    apply aux.
    { intros [|n]; cbn; auto. }
  - f_equal; auto.
    apply aux.
    { intros [|n]; cbn; auto. }
  - f_equal.
    induction l; cbn; auto.
    f_equal; auto.
    destruct a; cbn; auto.
    f_equal; auto.
Qed.

Lemma ren_id t : ren_term id_ren t = t.
Proof.
  revert t. fix aux 1. destruct t; cbn.
  all: try solve [ f_equal; eauto ].
  - f_equal; auto.
    erewrite ren_ext.
    1: apply aux.
    { intros [|n]; cbn; auto. }
  - f_equal; auto.
    erewrite ren_ext.
    1: apply aux.
    { intros [|n]; cbn; auto. }
  - f_equal.
    induction l; cbn; auto.
    f_equal; auto.
    destruct a; cbn; auto.
    f_equal; auto.
Qed.




