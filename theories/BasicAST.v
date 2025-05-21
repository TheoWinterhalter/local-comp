From Stdlib Require Import Utf8 String.

Set Primitive Projections.

(** Reference in the global environment *)
Definition gref := string.

(** Reference to an assumption (de Bruijn level) *)
Definition aref := nat.

(** Universe level *)
Definition level := nat.
