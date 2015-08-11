(* Assume decidable equality for tasks, so that it can be
   used in computations. *)

Require Import eqtype.

Parameter task_eq_dec: sporadic_task -> sporadic_task -> bool.
Axiom eqn_task : Equality.axiom task_eq_dec.

Canonical task_eqMixin := EqMixin eqn_task.
Canonical task_eqType := Eval hnf in EqType sporadic_task task_eqMixin.


(*Definition task_eq_dec (x y: sporadic_task) : {x = y} + {x <> y}.
  destruct x, y.
  destruct (eq_op task_id0 task_id1) eqn:Eid;
  destruct (eq_op task_cost0 task_cost1) eqn:Ecost;
  destruct (eq_op task_period0 task_period1) eqn:Eperiod;
  destruct (eq_op task_deadline0 task_deadline1) eqn:Edl;
  move: Eid Ecost Eperiod Edl => /eqP Eid /eqP Ecost /eqP Eperiod /eqP Edl; subst;
  try (by left; ins);
  try (by right; unfold not; intro EQ; inversion EQ; intuition).
Qed.*)