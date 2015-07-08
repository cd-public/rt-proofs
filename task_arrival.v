Require Import task.
Require Import job.
Require Import schedule.
Require Import Coq.Lists.List.

(* Whether the arrival sequence of a schedule is induced by a task set *)
Definition ts_arrival_sequence (ts: taskset) (sched: schedule) :=
  forall j t (ARR: arrives_at sched j t), In (job_task j) ts.

(* Since the number of tasks is finite, and each task does not
   spawn more than one job per time instant, the number of jobs
   released in a bounded interval is finite. *)
Lemma finite_arrival_sequence (ts: taskset) (sched: schedule) :
  forall (ARRts: ts_arrival_sequence ts sched)
         j arr (ARR: arrives_at sched j arr),
    exists (l: list job), In j l <-> arrives_at sched j arr.


(* Sporadic arrival times for every task in a taskset.
   We enforce -> only because the first arrival may be at any point. *)
Definition periodic_task_model (ts: taskset) (sched: schedule) :=
  forall (ARRts: ts_arrival_sequence ts sched) j t (ARRj: arrives_at sched j t),
  exists (j': job) (t': time), job_task j' = job_task j /\
                               arrives_at sched j' t' /\
                               t' = t + task_period (job_task j).

(* Periodic arrival times *)
Definition sporadic_task_model (ts: taskset) (sched: schedule) :=
  forall (ARRts: ts_arrival_sequence ts sched) j t (ARRj: arrives_at sched j t),
  exists (j': job) (t': time), job_task j' = job_task j /\
                               arrives_at sched j' t' /\
                               t' >= t + task_period (job_task j).

(* Synchronous release at time t *)
Definition sync_release (ts: taskset) (sched: schedule) (t: time) :=
  forall (tsk: sporadic_task) (IN: In tsk ts),
    exists (j: job), job_task j = tsk /\ arrives_at sched j t.