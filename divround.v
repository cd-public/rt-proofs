Require Import ssrnat div.

Definition div_floor (x y: nat) : nat := x %/ y.
Definition div_ceil (x y: nat) : nat := ((x + y - 1) %/ y).