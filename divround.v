Require Import Arith NPeano.

Definition div_floor (x y: nat) : nat := x / y.
Definition div_ceil (x y: nat) : nat := if beq_nat (x mod y) 0 then x/y else x / y + 1.