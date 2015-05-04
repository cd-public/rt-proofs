Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import job.
Require Import task.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Gt.
Require Import helper.

(* Integer time *)
Definition time := nat.

(* Set of all possible job arrival sequences *)
Record arrival_sequence : Type :=
  {
    arr :> job -> time -> Prop;
    no_multiple_arrivals: forall (j: job) (t1: time) (t2: time),
                              arr j t1 -> arr j t2 -> t1 = t2
  }.
(*Definition arrival_sequence := job -> time -> Prop.*)

Record schedule_data : Type :=
  {
    (* service provided to a job at time t *)
    service_at: job -> time -> nat; 
    (* arrival sequence of the schedule *)
    arrives_at: arrival_sequence
  }.

(* Service received by a job in a schedule, up to time t (inclusive) *)
Fixpoint service (sched: schedule_data) (j: job) (t: time) : nat:=
  match t with
      | 0 => service_at sched j 0
      | S t => service sched j t + service_at sched j (S t)
  end.

(* Whether a job arrived at time t *)
Definition arrived (sched: schedule_data) (j: job)  (t: time) : Prop :=
    exists (t_0: time), t_0 <= t /\ (arrives_at sched) j t_0.

(* Whether a job is scheduled at time t *)
Definition scheduled (sched: schedule_data) (j: job) (t: time) : Prop :=
    service_at sched j t > 0.

(* Whether a job has completed at time t *)
Definition completed (sched: schedule_data) (j: job) (t: time) : Prop :=
    t > 0 /\ service sched j (t-1) = job_cost j.

(* Whether a job is pending and not scheduled at time t *)
Definition backlogged (sched: schedule_data) (j: job) (t: time) : Prop :=
    ~scheduled sched j t /\ ~completed sched j t.

Record schedule : Type :=
  {
    sd:> schedule_data;

    (* Additional properties that a schedule must satisfy *)

    (* 1) A job can only be scheduled if it arrived *)
    task_must_arrive_to_exec :
        forall (j: job) (t: time),
            scheduled sd j t -> arrived sd j t;

    (* 2) A job cannot execute anymore after it completed *)
    completed_task_does_not_exec :
        forall (j: job) (t_comp: time),
            completed sd j t_comp ->
                forall (t: time), t >= t_comp -> ~ scheduled sd j t
  }.

(* Whether the arrival sequence of a schedule is induced by a task set *)
Definition ts_arrival_sequence (ts: taskset) (sched: schedule) : Prop :=
    forall (j: job) (t: time),
        (arrives_at sched) j t -> (exists tsk: sporadic_task, job_of j = Some tsk /\ In tsk ts).

(* Sporadic arrival times *)
Definition periodic_task_model (ts: taskset) (sched: schedule) : Prop :=
    ts_arrival_sequence ts sched ->
    forall (j1: job) (j2: job) (tsk: sporadic_task) (t: time) (t': time),
            (arrives_at sched) j1 t /\ (arrives_at sched) j2 t' /\ t < t'
            /\ job_of j1 = Some tsk /\ job_of j2 = Some tsk
            -> t' = t + task_period tsk.

(* Periodic arrival times *)
Definition sporadic_task_model (ts: taskset) (sched: schedule) : Prop :=
    ts_arrival_sequence ts sched ->
    forall (j1: job) (j2: job) (tsk: sporadic_task) (t: time) (t': time),
            (arrives_at sched) j1 t /\ (arrives_at sched) j2 t' /\ t < t'
            /\ job_of j1 = Some tsk /\ job_of j2 = Some tsk
            -> t' >= t + task_period tsk.

Lemma backlogged_no_service : forall (sched: schedule_data) (j: job) (t: time),
    backlogged sched j t -> service_at sched j t = 0.
Proof.
    intros sched j t j_backlogged.
    unfold backlogged in j_backlogged.
    inversion j_backlogged as [not_scheduled _].
    unfold scheduled in not_scheduled.
    assert (H := gt_0_eq (service_at sched j t)).
    inversion H as [case1 | case2].
        contradiction.
        rewrite case2. reflexivity.
Qed.

(* Response time of a job in a particular schedule *)
Definition job_response_time (sched: schedule) (j: job) (r: time) : Prop :=
    forall (t_a: time),
        arrives_at sched j t_a ->
        least_nat r (fun r => completed sched j (t_a + r)).

(* Worst-case response time of any job of a task, in any schedule *)
Definition task_response_time (tsk: sporadic_task) (ts: taskset) (r: time) : Prop :=
    In tsk ts /\
    forall (sched: schedule) (j: job),
        ts_arrival_sequence ts sched ->
        job_of j = Some tsk ->
        greatest_nat r (job_response_time sched j).

(* Arrival time that generates the worst-case response time *)
Definition critical_instant (tsk: sporadic_task) (ts: taskset) (sched: schedule) (t: time) :=
    exists (j: job),
        job_of j = Some tsk
        /\ arrives_at sched j t
        /\ exists (r: time), (job_response_time sched j r
                              /\ task_response_time tsk ts r).

Lemma no_completed_tasks_at_time_zero : forall (sched: schedule) (j: job) , ~completed sched j 0.
Proof.
    unfold not. intros.
    inversion H. inversion H0.
Qed.