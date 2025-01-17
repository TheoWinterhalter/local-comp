From Coq Require Import Utf8 List Bool.
From Equations Require Import Equations.

Import ListNotations.

Set Default Goal Selector "!".

Notation "'∑' x .. y , p" := (sigT (λ x, .. (sigT (λ y, p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Create HintDb shelvedb.

Hint Extern 10000 => shelve : shelvedb.
