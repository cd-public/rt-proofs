Require Import task.
Require Import job.
Require Import schedule.
Require Import Coq.Lists.List.

(* Whether the arrival sequence of a schedule is induced by a task set *)
Definition ts_arrival_sequence (ts: taskset) (sched: schedule) : Prop :=
    forall (j: job) (t: time),
        arrives_at sched j t -> (exists tsk: sporadic_task, job_of j = Some tsk /\ In tsk ts).

(* Sporadic arrival times for every task in a taskset.
   We enforce -> only because the first arrival may be at any point. *)
Definition periodic_task_model (ts: taskset) (sched: schedule) : Prop :=
    ts_arrival_sequence ts sched ->
    forall (tsk: sporadic_task) (j: job) (t: time),
            job_of j = Some tsk /\ arrives_at sched j t ->
            exists (j': job) (t': time),
                job_of j' = Some tsk
                /\ (arrives_at sched) j' t'
                /\ t' = t + task_period tsk.

(* Periodic arrival times *)
Definition sporadic_task_model (ts: taskset) (sched: schedule) : Prop :=
    ts_arrival_sequence ts sched ->
    forall (tsk: sporadic_task) (j: job) (t: time),
            job_of j = Some tsk /\ arrives_at sched j t ->
            exists (j': job) (t': time),
                job_of j' = Some tsk
                /\ arrives_at sched j' t'
                /\ t' >= t + task_period tsk.

(* Synchronous release at time t *)
Definition sync_release (ts: taskset) (sched: schedule) (t: time) :=
    forall (tsk: sporadic_task),
        In tsk ts ->
        (exists (j: job), job_of j = Some tsk /\ arrives_at sched j t).
