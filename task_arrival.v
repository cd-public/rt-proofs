Require Import List Vbase task job schedule.

(* Whether the arrival sequence of a schedule is induced by a task set *)
Definition ts_arrival_sequence (ts: taskset) (sched: schedule) :=
  forall j t (ARR: arrives_at sched j t), In (job_task j) ts.

(* Since the number of tasks is finite, and each task does not
   spawn more than one job per time instant, the number of jobs
   released in a bounded interval is finite. *)
Definition arrival_list (sched: schedule) (l: list job) (t: time) :=
  forall j, << IN: In j l >> <->
            << ARRIVED: (arrived sched j t) >>.
    
Lemma ts_finite_arrival_sequence:
  forall ts sched (ARRts: ts_arrival_sequence ts sched) (t: time),
    exists (l: list job), arrival_list sched l t.
Proof.
Admitted.

(* Sporadic arrival times for every task in a taskset.
   We use only '->' because the first arrival may be at any point. *)
Definition periodic_task_model (ts: taskset) (sched: schedule) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall j arr (ARRj: arrives_at sched j arr),
    exists (j': job) (arr': time), job_task j' = job_task j /\
                                   arrives_at sched j' arr' /\
                                   arr' = arr + task_period (job_task j).

(* Periodic arrival times *)
Definition sporadic_task_model (ts: taskset) (sched: schedule) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall j arr (ARRj: arrives_at sched j arr),
    exists (j': job) (arr': time), job_task j' = job_task j /\
                                   arrives_at sched j' arr' /\
                                   arr' >= arr + task_period (job_task j).

(* Synchronous release at time t *)
Definition sync_release (ts: taskset) (sched: schedule) (t: time) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall (tsk: sporadic_task) (IN: In tsk ts),
    exists (j: job), job_task j = tsk /\ arrives_at sched j t.