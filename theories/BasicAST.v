From Coq Require Import Utf8 String.

Set Primitive Projections.

(** Reference in the global environment **)
Definition gref := string.

(** Reference in the extension environment **)
Definition eref := nat.

(** Reference in an extension instance **)
Definition aref := nat.

(** Universe level **)
Definition level := nat.
