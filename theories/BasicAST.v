From Coq Require Import Utf8.

Set Primitive Projections.

(** Reference in the global environment **)
Definition gref := nat.

(** Reference in the extension environment **)
Definition eref := nat.

(** Reference in an extension instance **)
Definition aref := nat.

(** Universe level **)
Definition level := nat.
