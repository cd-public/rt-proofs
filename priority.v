Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import job.
Require Import schedule.



Axiom task_id : task -> nat.

Definition prio_order := task -> task -> Prop.

Definition break_ties (tsk1: task) (tsk2: task) : Prop :=
    task_id tsk1 < task_id tsk2.

Definition hp (prio_higher: prio_order) (tsk1: task) (tsk2: task) : Prop :=
    prio_higher tsk1 tsk2 \/ break_ties tsk1 tsk2.

Definition RM (tsk1: sporadic_task) (tsk2: sporadic_task) : Prop :=
    task_period tsk1 < task_period tsk2.

Definition enforce_prio_ident_mp (s: schedule) : Prop :=
    forall (num_cpus: nat) (t: time) (l: list (option task)) (backlogged_task: task),
        ident_mp num_cpus s ->
        length l = num_cpus ->
        (forall (tsk: task), List.In (Some tsk) l <-> s tsk t)) ->
        forall (backlogged_task: task), ~ s tsk t <->
List.In