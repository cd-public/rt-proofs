Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import job.
Require Import Coq.Lists.List.
Require Import helper.

(* Integer time *)
Definition time := nat.

(* Set of all possible job arrival sequences *)
Definition arrival_seq := job -> time -> Prop.

(* Whether a particular arrival sequence is induced by a task set *)
Record ts_arrival_seq (ts: taskset) (arr: arrival_seq) : Prop :=
  { job_of_task_arrives: forall (j: job) (tsk: sporadic_task) (t: time),
        arr j t /\ job_of j tsk <-> List.In tsk ts;
    inter_arrival_times:
        forall (j1: job) (j2: job) (tsk: sporadic_task) (t: time) (t': time),
            (arr j1 t /\ arr j2 t' /\ t < t'
            /\ job_of j1 tsk /\ job_of j2 tsk)
            -> t < t' + task_period tsk 
  }.

(* Whether a job arrives at time t *)
Definition arrived (j: job) (arr: arrival_seq) (t: time) : Prop :=
    exists (t_0: time), t_0 <= t /\ arr j t_0.

(* Set of all possible job schedules *)
Definition schedule := job -> time -> nat.

(* Service received by a job in a schedule, up to time t (inclusive) *)
Fixpoint service (sched: schedule) (j: job) (t: time) : nat:=
  match t with
  | 0 => sched j 0
  | S t => service sched j t + sched j (S t)
  end.

(* Whether a job has completed at time t *)
Definition completed (j: job) (sched: schedule) (t: time) : Prop :=
    service sched j t = job_cost j.

(* Whether a job is pending and not scheduled at time t *)
Definition backlogged (j: job) (sched: schedule) (t: time) : Prop :=
    sched j t = 0 /\ ~ completed j sched t.

(* A job can only be scheduled if it arrived *)
Axiom task_must_arrive_to_exec :
    forall (j: job) (sched: schedule) (arr: arrival_seq) (t: time),
        sched j t > 0 -> arrived j arr t.

(* A job cannot execute anymore after it completed *)
Axiom completed_task_does_not_exec :
    forall (j: job) (sched: schedule) (t_comp: time),
        completed j sched t_comp ->
            forall (t: time), t >= t_comp -> sched j t = 0.

(* Absolute time of completion for a job in a particular schedule *)
Definition job_response_time (j: job) (sched: schedule) (arr: arrival_seq) (t: time) :=
    least_nat t (completed j sched).

(* Worst-case response time of any job of a task, in any schedule *)
Definition task_response_time (tsk: sporadic_task) (t: time) :=
    forall (j: job) (sched: schedule) (arr: arrival_seq) (t: time),
        job_of j tsk /\ greatest_nat t (job_response_time j sched arr).

(* Arrival time that generates the worst-case response time *)
Definition critical_instant (tsk: sporadic_task) (sched: schedule) (arr: arrival_seq) (t: time) :=
    exists (j: job), job_response_time j sched arr t = task_response_time tsk t.

(* Whether a schedule only contains jobs of a task set *)
Definition schedule_of (sched: schedule) (ts: taskset) : Prop :=
    forall (j: job) (t: time), sched j t > 0 -> (exists tsk, In tsk ts /\ job_of j tsk).