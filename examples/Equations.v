From Stdlib Require Import List.
Import ListNotations.

#[universes(polymorphic)]
Lemma in_eq {A : Type} {a : A} {l} : In a (a :: l).
Proof. left. reflexivity. Defined.

#[universes(polymorphic)]
Lemma in_tl {A : Type} {a b : A} {l} :  In a l -> In a (b :: l).
Proof. right. assumption. Defined.

Module Type Map_In.

Symbol map_In : forall [A B] (l : list A) (f : forall x, In x l -> B), list B.

Rewrite Rules map_In_r :=
| map_In (B := ?B) [] ?f => []
| map_In (A := ?A) (B := ?B) (?a :: ?l) ?f =>
    ?f ?a in_eq :: map_In ?l (fun x H => ?f x (in_tl H)).

End Map_In.

From Equations Require Equations.

Module Import map_In_impl : Map_In.

Equations map_In [A B] (l : list A) (f : forall x, In x l -> B) : list B :=
map_In [] f := [];
map_In (a :: l) f := f a _ :: map_In l (fun x H => f x _).

Import Equations.

Theorem map_In_map [A B] (f : A -> B) l : map_In l (fun x _ => f x) = map f l.
Proof.
  induction l.
  - cbn. simp map_In. reflexivity.
  - cbn. simp map_In. now f_equal.
Qed.

End map_In_impl.


Theorem map_In_map [A B] (f : A -> B) l : map_In l (fun x _ => f x) = map f l.
Proof.
  induction l.
  - cbn. reflexivity.
  - cbn. f_equal. assumption.
Qed.
