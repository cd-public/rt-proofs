Require Import Vbase List Arith Bool.Sumbool.

Section Task.

(* Sporadic Task Model *)
Record sporadic_task : Type :=
{
  task_id: nat; (* allows multiple tasks with same parameters *)
  task_cost: nat; (* worst-case cost *)
  task_period : nat; (* inter-arrival time *)
  task_deadline: nat; (* relative deadline *)

  (* Properties of a task *)
  task_properties: << task_cost_positive: task_cost > 0 >> /\
                   << task_period_positive: task_period > 0 >> /\
                   << task_deadline_positive: task_deadline > 0 >> /\
                   << task_cost_le_deadline: task_cost <= task_deadline >>
}.

(* Define decidable equality for tasks, so that it can be
   used in computations. *)
Definition task_eq_dec (x y: sporadic_task) : {x = y} + {x <> y}.
  destruct x, y.
  destruct (beq_nat task_id0 task_id1) eqn:Eid;
  destruct (beq_nat task_cost0 task_cost1) eqn:Ecost;
  destruct (beq_nat task_period0 task_period1) eqn:Eperiod;
  destruct (beq_nat task_deadline0 task_deadline1) eqn:Edl;
  try rewrite beq_nat_true_iff in *; try rewrite beq_nat_false_iff in *; subst;
  try (by left; apply f_equal, proof_irrelevance);
  try (by right; unfold not; intro EQ; inversion EQ; intuition).
Defined.
Definition beq_task (x y: sporadic_task) := if task_eq_dec x y then true else false.

Lemma beq_task_true_iff : forall x y, beq_task x y = true <-> x = y.
Proof.
  unfold beq_task; ins; destruct (task_eq_dec x y); split; ins.
Qed.

Lemma beq_task_false_iff : forall x y, beq_task x y = false <-> x <> y.
Proof.
  unfold beq_task; ins; destruct (task_eq_dec x y); split; ins.
Qed.

Definition taskset := list sporadic_task.

(* Models for task deadlines *)
Definition implicit_deadline_model (ts: taskset) :=
  forall tsk, In tsk ts -> task_deadline tsk = task_period tsk.

Definition restricted_deadline_model (ts: taskset) :=
  forall tsk, In tsk ts -> task_deadline tsk <= task_period tsk.

Definition arbitrary_deadline_model (ts: taskset) := True.

End Task.