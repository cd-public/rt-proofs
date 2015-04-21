Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import job.
Require Import Coq.Lists.List.
Require Import helper.

Definition time := nat.

Definition arrival_seq := job -> time -> Prop.

Record ts_arrival_seq (ts: taskset) (arr: arrival_seq) : Prop :=
  { job_of_task_arrives: forall (j: job) (tsk: sporadic_task) (t: time),
        arr j t /\ job_of j tsk <-> List.In tsk ts;
    inter_arrival_times:
        forall (j1: job) (j2: job) (tsk: sporadic_task) (t: time) (t': time),
            (arr j1 t /\ arr j2 t' /\ t < t'
            /\ job_of j1 tsk /\ job_of j2 tsk)
            -> t < t' + task_period tsk 
  }.

Definition arrived (j: job) (arr: arrival_seq) (t: time) : Prop :=
    exists (t_0: time), t_0 <= t /\ arr j t_0.

Definition schedule := job -> time -> nat.

Fixpoint service (sched: schedule) (j: job) (t: time) : nat:=
  match t with
  | 0 => sched j 0
  | S t => service sched j t + sched j (S t)
  end.

Definition completed (j: job) (sched: schedule) (t: time) : Prop :=
    service sched j t = job_cost j.

Definition backlogged (j: job) (sched: schedule) (t: time) : Prop :=
    sched j t = 0 /\ ~ completed j sched t.

Axiom task_must_arrive_to_exec :
    forall (j: job) (sched: schedule) (arr: arrival_seq) (t: time),
        sched j t > 0 -> arrived j arr t.

Axiom completed_task_does_not_exec :
    forall (j: job) (sched: schedule) (t_comp: time),
        completed j sched t_comp ->
            forall (t: time), t >= t_comp -> sched j t = 0.

Definition job_response_time (j: job) (sched: schedule) (arr: arrival_seq) (t: time) :=
    least_nat t (completed j sched).

Definition task_response_time (tsk: sporadic_task) (t: time) :=
    forall (j: job) (sched: schedule) (arr: arrival_seq) (t: time),
        job_of j tsk /\ greatest_nat t (job_response_time j sched arr).

Definition critical_instant (tsk: sporadic_task) (sched: schedule) (arr: arrival_seq) (t: time) :=
    exists (j: job), job_response_time j sched arr t = task_response_time tsk t.

Definition schedule_of (sched: schedule) (ts: taskset) : Prop :=
    forall (j: job) (t: time), sched j t > 0 -> (exists tsk, In tsk ts /\ job_of j tsk).