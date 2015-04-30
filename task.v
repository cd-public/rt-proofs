Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import List.

Section Task.

(* Sporadic Task Model *)
Record sporadic_task : Type :=
  { task_id: nat; (* allows multiple tasks with same parameters *)
    task_cost: nat;
    task_period : nat;
    task_deadline: nat (* relative deadline *)
  }.

Definition taskset := list sporadic_task.

(* Models for task deadlines *)
Definition implicit_deadline_model (ts: taskset) : Prop :=
    forall (tsk: sporadic_task), In tsk ts -> task_deadline tsk = task_period tsk.

Definition restricted_deadline_model (ts: taskset) : Prop :=
    forall (tsk: sporadic_task), In tsk ts -> task_deadline tsk <= task_period tsk.

Definition arbitrary_deadline_model (ts: taskset) : Prop := True.

End Task.