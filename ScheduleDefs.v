Require Import Classical Vbase JobDefs helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ArrivalSequence.

Import Job.

(* Integer time *)
Definition time := nat.

Parameter arrival_sequence: Set.
Parameter arriving_jobs: arrival_sequence -> time -> seq job.

Definition valid_arrival_sequence (arr: arrival_sequence) :=
  << no_multiple_jobs:
       forall j t1 t2 (INj1: j \in (arriving_jobs arr t1))
                      (INj2: j \in (arriving_jobs arr t2)), t1 = t2 >> /\
  << arrival_times_match:
       forall j t (INj: j \in (arriving_jobs arr t)), job_arrival j = t >> /\
  << arrival_seq_unique: forall t, uniq (arriving_jobs arr t) >>.

Section ArrivingJobs.

Variable arr: arrival_sequence.
Variable j: job.
  
Definition arrives_at (t: time) :=  j \in arriving_jobs arr t.

(* A job has arrived at time t iff it arrives at some time t_0, with 0 <= t_0 <= t. *)
Definition has_arrived (t: nat) := [exists t_0 in 'I_(t.+1), arrives_at t_0].

(* A job arrived before t iff it arrives at some time t_0, with 0 <= t_0 < t. *)
Definition arrived_before (t: nat) := [exists t_0 in 'I_(t), arrives_at t_0].

(* A job arrives between t1 and t2 iff it arrives at some time t with t1 <= t < t2. *)
Definition arrived_between (t1 t2: nat) := [exists t in 'I_(t2), ((t1 <= t) && arrives_at t)].

End ArrivingJobs.

End ArrivalSequence.

(* 1) This definition of arrival sequence allows retrieving the finite set of
      jobs that arrive at time t. So we can define things like the "Cumulative
      execution time of task T_5 during [3, 8)".
   2) Although it is a bit redundant to have the job arrival time both in the job
      and in the arrival sequence, it has some advantages. In case of the job,
      this allows retrieving the arrival time if we want to sort a sequence of jobs,
      for example. For the arrival sequence, it makes it easy to return a prefix.
*)

Module Schedule.

Import Job.
Export ArrivalSequence.

(* Schedule is defined as the amount of service given to jobs during
   discrete time [t, t+1). *)
Definition schedule := job -> time -> nat.

(* Every schedule has an arrival sequence. We add a coercion to
   make it easily accessible. *)
Parameter arr_seq_of_schedule :> schedule -> arrival_sequence.

Section ScheduledJobs.

Variable sched: schedule.
Variable j: job.

(* Service received by a job during [t, t+1) -- just an alias to schedule. *)
Definition service_at (t: time) := sched j t.

(* Cumulative service received during [0, t') *)
Definition service (t': time) := \sum_(0 <= t < t') (service_at t).

(* Cumulative service received during [t1, t2) *)
Definition service_during (t1 t2: time) := \sum_(t1 <= t < t2) (service_at t).

(* Whether a job is scheduled at time t *)
Definition scheduled (t: time) := service_at t != 0.

(* Whether a job has completed at time t (assumes costs are non-zero!) *)
Definition completed (t: time) := (service t == job_cost j).

Definition pending (t: time) := has_arrived sched j t && ~~completed t.

(* Whether a job is pending and not scheduled at time t *)
Definition backlogged (t: time) := pending t && ~~scheduled t.

(* A carried-in job in [t1,t2) arrives before t1 and is not completed at time t1 *)
Definition carried_in (t1: time) := arrived_before sched j t1 && ~~ completed t1.

(* A carried-out job in [t1,t2) arrives after t1 and is not completed at time t2 *)
Definition carried_out (t1 t2: time) := arrived_between sched j t1 t2 && ~~ completed t2.

End ScheduledJobs.

Definition valid_schedule (sched: schedule) :=
  (* A job can only be scheduled if it has arrived *)
  << task_must_arrive_to_exec:
    forall j t, scheduled sched j t -> has_arrived sched j t >> /\

  (* A job cannot be scheduled after it completed, i.e., it cannot accumulate
     more service than its execution cost. *)
  << comp_task_no_exec: forall j t, service sched j t <= job_cost j >>.

Section ServiceProperties.

Variable sched: schedule.
Hypothesis sched_valid: valid_schedule sched.  

Hypothesis max_service_one: forall j' t, service_at sched j' t <= 1.

Variable j: job.

Lemma service_interval_max_cost :
  forall t t', service_during sched j t t' <= job_cost j.
Proof.
  unfold service_during; rename sched_valid into schedPROP; red in schedPROP; des; ins.
  destruct (t > t') eqn:GT.
    by rewrite big_geq // -ltnS; apply ltn_trans with (n := t); ins.
    apply leq_trans with (n := \sum_(0 <= t0 < t') service_at sched j t0);
      last by apply comp_task_no_exec.
    rewrite -> big_cat_nat with (m := 0) (n := t);
      [by apply leq_addl | by ins | by rewrite leqNgt negbT //].
Qed.

Hypothesis valid_arr_seq: valid_arrival_sequence sched.

Lemma service_before_arrival :
  forall t0 (LT: t0 < job_arrival j), service_at sched j t0 = 0.
Proof.
  rename valid_arr_seq into arrPROP; red in arrPROP; des;
  rename sched_valid into schedPROP; red in schedPROP; des; ins.
  rename task_must_arrive_to_exec into EXEC; specialize (EXEC j t0).
  apply contra with (c := scheduled sched j t0) (b := has_arrived sched j t0) in EXEC;
    first by rewrite -/scheduled negbK in EXEC; apply/eqP.
  {
    destruct (classic (exists arr_j, arrives_at sched j arr_j)) as [ARRIVAL|NOARRIVAL]; des;
    last by apply/negP; move => /exists_inP_nat ARRIVED; des; apply NOARRIVAL; exists x.
    {
      generalize ARRIVAL; apply arrival_times_match in ARRIVAL; ins.
      rewrite -> ARRIVAL in *.
      apply/negP; unfold not, has_arrived; move => /exists_inP_nat ARRIVED; des.
      apply leq_trans with (p := arr_j) in ARRIVED; last by ins.
      apply no_multiple_jobs with (t1 := x) in ARRIVAL0; last by ins.
      by subst; rewrite ltnn in ARRIVED.
    }
  }
Qed.

Lemma sum_service_before_arrival :
  forall t1 t2 (LT: t2 <= job_arrival j),
    \sum_(t1 <= i < t2) service_at sched j i = 0.
Proof.
  ins; apply/eqP; rewrite -leqn0.
  apply leq_trans with (n := \sum_(t1 <= i < t2) 0);
    last by rewrite big_const_nat iter_addn mul0n addn0.
  rewrite big_nat_cond [\sum_(_ <= _ < _) 0]big_nat_cond.
  apply leq_sum; intro i; rewrite andbT; move => /andP LTi; des.
  rewrite service_before_arrival; first by ins.
  by apply leq_trans with (n := t2); ins.
Qed.

End ServiceProperties.

End Schedule.


(* Specific definitions for schedules of sporadic tasks *)
Module ScheduleOfSporadicTask.

Import SporadicTaskJob.
Export Schedule.

(* Whether job j1 arrives earlier than j2 (both are from the same task) *)
Definition earlier_job (sched: schedule) (j1 j2: job) :=
  << EQtsk: job_task j1 = job_task j2 >> /\
  exists arr1 arr2, << ARR1: arrives_at sched j1 arr1 >> /\
                    << ARR2: arrives_at sched j2 arr2 >> /\
                    << LT: arr1 < arr2 >>.

End ScheduleOfSporadicTask.