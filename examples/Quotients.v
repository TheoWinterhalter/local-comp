Module Type QuotientInput.

Parameter A : Type.
Parameter eq : A -> A -> Prop.

End QuotientInput.


Module Type Quotient (QI : QuotientInput).
Import QI.

Parameter T : Type.

Symbol mk : A -> T.
Symbol lift : forall {B : Type} (f : A -> B) (p : forall a b, eq a b -> f a = f b), T -> B.

Rewrite Rule lift_mk :=
| lift ?f _ (mk ?x) => ?f ?x.

Parameter rec : forall {B : T -> Type} (f : forall (a : A), B (mk a)) (t : T), B t.
Parameter sound : forall a b, eq a b -> mk a = mk b.

End Quotient.

(* Implements the same interface as Lean *)


Module QuotientImpl (QI : QuotientInput) : Quotient QI.
Import QI.

Definition T := A.

Definition mk (x : A) := x.
Definition lift {B} (f : A -> B) (p : forall a b, eq a b -> f a = f b) x := f x.

Definition rec {B} (f : forall (a : A), B a) t := f t.

Axiom sound : forall a b, eq a b -> mk a = mk b.

End QuotientImpl.

