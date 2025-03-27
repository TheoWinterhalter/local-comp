From Stdlib Require Import Utf8 String.

Set Primitive Projections.

(** Reference in the global environment **)
Definition gref := string.

(** Reference in the extension environment (de Bruijn level) **)
Definition eref := nat.

(** Reference in an extension instance (de Bruijn index) **)
Definition aref := nat.

(** Universe level **)
Definition level := nat.
