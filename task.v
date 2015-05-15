Require Import List.

Section Task.

(* Sporadic Task Model *)
Record sporadic_task : Type :=
  { task_id: nat; (* allows multiple tasks with same parameters *)
    task_cost: nat;
    task_period : nat;
    task_deadline: nat; (* relative deadline *)

    (* Properties of a task *)
    task_cost_positive: task_cost > 0;
    task_cost_le_deadline: task_cost <= task_deadline;
    task_deadline_positive: task_deadline > 0
  }.

Definition taskset := list sporadic_task.

(* Models for task deadlines *)
Definition implicit_deadline_model (ts: taskset) : Prop :=
    forall (tsk: sporadic_task), In tsk ts -> task_deadline tsk = task_period tsk.

Definition restricted_deadline_model (ts: taskset) : Prop :=
    forall (tsk: sporadic_task), In tsk ts -> task_deadline tsk <= task_period tsk.

Definition arbitrary_deadline_model (ts: taskset) : Prop := True.

End Task.
