Module Type Plus.
  Symbol plus : nat -> nat -> nat.
  Rewrite Rules plus_r :=
  | plus 0 ?n => ?n
  | plus (S ?m) ?n => S (plus ?m ?n).
End Plus.

Module Import PlusImpl : Plus. Definition plus := Nat.add. End PlusImpl.

Compute plus 25 17. (* = 42 *)
Compute plus.