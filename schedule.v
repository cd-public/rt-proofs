Require Import Vbase job task util_lemmas
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Definition time := nat.

Module ArrivalSequence.

  (*We define an arrival sequence as a mapping from natural number t to a sequence of jobs*)
  Section ArrivalSequenceDef.

    Variable Job: eqType. (* Assume any job type with decidable equality *)

    Definition arrival_sequence := time -> seq Job.

  End ArrivalSequenceDef.

  Section JobInArrivalSequence.

    Context {Job: eqType}.

    (* Whether a job arrives in a sequence at time t *)
    Definition arrives_at (j: Job) (arr: arrival_sequence Job) (t: time) := j \in arr t.

    (* Define a job that arrives in a specific arrival sequence.
       It holds an arrival time and a proof that it arrives at that
       particular instant. *)
    Record JobIn (arr_seq: arrival_sequence Job) : Type :=
    {
      _job_in: Job;
      _arrival_time: time;
      _: arrives_at _job_in arr_seq _arrival_time
    }.

    (* Define a coercion that stating that every JobIn is a Job. *)
    Coercion JobIn_is_Job {arr_seq: arrival_sequence Job} (j: JobIn arr_seq) :=
      _job_in arr_seq j.

    (* Define job arrival time as that time that the job arrives. *)
    Definition job_arrival {arr_seq: arrival_sequence Job} (j: JobIn arr_seq) :=
      _arrival_time arr_seq j.

    (* Assume a decidable equality for JobIn. *)
    Definition f (arr_seq: arrival_sequence Job) :=
      (fun j1 j2: JobIn arr_seq => (JobIn_is_Job j1) == (JobIn_is_Job j2)).
    Axiom eqn_jobin : forall arr_seq, Equality.axiom (f arr_seq).
    Canonical jobin_eqMixin arr_seq := EqMixin (eqn_jobin arr_seq).
    Canonical jobin_eqType arr_seq := Eval hnf in EqType (JobIn arr_seq) (jobin_eqMixin arr_seq).

  End JobInArrivalSequence.

  Section ArrivalSequenceProperties.

    Context {Job: eqType}.
    Variable arr_seq: arrival_sequence Job.
    
    (* A job j cannot arrives at two different times. *)
    Definition no_multiple_arrivals :=
      forall (j: Job) t1 t2,
        arrives_at j arr_seq t1 -> arrives_at j arr_seq t2 -> t1 = t2.

    (* The sequence of arrivals at a particular time has no duplicates. *)
    Definition arrival_sequence_is_a_set := forall t, uniq (arr_seq t).

    (* A valid arrival sequence satisfies the three properties above. *)
    Definition valid_arrival_sequence :=
      no_multiple_arrivals /\ arrival_sequence_is_a_set.

  End ArrivalSequenceProperties.
  
  Section ArrivingJobs.

    Context {Job: eqType}. (* Assume any job type with decidable equality *)
    Context {arr_seq: arrival_sequence Job}.
    Variable j: JobIn arr_seq.

    (* A job has arrived at time t iff it arrives at some time t_0, with 0 <= t_0 <= t. *)
    Definition has_arrived (t: nat) := job_arrival j <= t.

    (* A job arrived before t iff it arrives at some time t_0, with 0 <= t_0 < t. *)
    Definition arrived_before (t: nat) := job_arrival j < t.

    (* A job arrives between t1 and t2 iff it arrives at some time t with t1 <= t < t2. *)
    Definition arrived_between (t1 t2: nat) := t1 <= job_arrival j < t2.

  End ArrivingJobs.

End ArrivalSequence.

Module Schedule.

  Export ArrivalSequence.

  (* Processor is defined as a bounded natural number. *)
  Definition processor num_cpus := 'I_num_cpus.
  
  Section ScheduleDef.

    Context {Job: eqType}.
    
    Variable num_cpus: nat.
    Variable arr_seq: arrival_sequence Job.

    (* We define a schedule of an arrival sequence as a mapping.
       Each processor at each time has either a job from the sequence or none. *)
    Definition schedule :=
      processor num_cpus -> time -> option (JobIn arr_seq).

  End ScheduleDef.
  
  Section ScheduledJobs.

    Context {Job: eqType}. (* Assume a job type with decidable equality,... *)
    Context {arr_seq: arrival_sequence Job}.
    
    Variable job_cost: Job -> nat. (* ...a cost function, ... *)
    
    Context {num_cpus: nat}.
    Variable rate: Job -> processor num_cpus -> nat. (*...and a specific rate for each processor *)
    Variable sched: schedule num_cpus arr_seq.

    Variable j: JobIn arr_seq.

    (* Whether a job is scheduled at time t *)
    Definition scheduled (t: time) :=
      [exists cpu in 'I_(num_cpus), sched cpu t == Some j].

    (* Whether a processor is idle *)
    Definition is_idle (cpu: 'I_(num_cpus)) (t: time) :=
      sched cpu t = None.

    (* Define the service as rate of the processor the job is scheduled on. *)
    Definition service_at (t: time) :=
      \sum_(cpu < num_cpus | sched cpu t == Some j) rate j cpu.

    (* Cumulative service received during [0, t') *)
    Definition service (t': time) := \sum_(0 <= t < t') service_at t.

    (* Cumulative service received during [t1, t2) *)
    Definition service_during (t1 t2: time) := \sum_(t1 <= t < t2) service_at t.
    
    (* Whether a job has completed at time t *)
    Definition completed (t: time) := service t == job_cost j.

    (* A pending job has arrived but has not completed. *)
    Definition pending (t: time) := has_arrived j t && ~~completed t.

    (* Whether a job is pending and not scheduled at time t *)
    Definition backlogged (t: time) := pending t && ~~scheduled t.

    (* A carried-in job in [t1,t2) arrives before t1 and is not completed at time t1 *)
    Definition carried_in (t1: time) := arrived_before j t1 && ~~ completed t1.

    (* A carried-out job in [t1,t2) arrives after t1 and is not completed at time t2 *)
    Definition carried_out (t1 t2: time) := arrived_between j t1 t2 && ~~ completed t2.

    (* The list of jobs scheduled at time t. *)
    Definition jobs_scheduled_at (t: time) :=
      \cat_(cpu < num_cpus) make_sequence (sched cpu t).
    
    (* The (duplicate-free) list of jobs scheduled in the interval [t1, t2). *)
    Definition jobs_scheduled_between (t1 t2: time) :=
      undup (\cat_(t1 <= t < t2) jobs_scheduled_at t).

  End ScheduledJobs.

  (* Let's define how valid schedules can look like. *)
  Section ValidSchedules.

    Context {Job: eqType}. (* Assume a job type with decidable equality *)
    Context {arr_seq: arrival_sequence Job}.
    Context {num_cpus: nat}.
    
    Variable job_cost: Job -> nat. (* and a cost function. *)

    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    (* Whether job parallelism is disallowed *)
    Definition jobs_dont_execute_in_parallel :=
      forall j t cpu1 cpu2,
        sched cpu1 t == Some j -> sched cpu2 t == Some j -> cpu1 = cpu2.

    (* Whether a job can only be scheduled if it has arrived *)
    Definition jobs_must_arrive_to_execute :=
      forall j t, scheduled sched j t -> has_arrived j t.

    (* Whether a job can be scheduled after it completes *)
    Definition completed_jobs_dont_execute :=
      forall j t, service rate sched j t <= job_cost j.

    (* In a valid sporadic schedule, jobs have to be arrived before they executed
       and in case they completed, they don't execute any more. *) 
    Definition valid_sporadic_schedule :=
      jobs_must_arrive_to_execute /\ completed_jobs_dont_execute.

  End ValidSchedules.

  Section ServiceProperties.

    Context {Job: eqType}.
    Context {arr_seq: arrival_sequence Job}.
    
    Variable job_cost: Job -> nat.

    Variable num_cpus: nat.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.
    Variable j: JobIn arr_seq.

    Section Basic.

      (* If a job is not scheduled, it won't get service. *)
      Lemma not_scheduled_no_service :
        forall t,
          ~~ scheduled sched j t -> service_at rate sched j t = 0.
      Proof.
        unfold scheduled, service_at; intros t NOTSCHED.
        rewrite negb_exists_in in NOTSCHED.
        move: NOTSCHED => /forall_inP NOTSCHED.
        rewrite big_seq_cond.
        rewrite -> eq_bigr with (F2 := fun i => 0);
          first by rewrite big_const_seq iter_addn mul0n addn0.
        move => cpu /andP [_ SCHED].
        exploit (NOTSCHED cpu); [by ins | clear NOTSCHED].
        by move: SCHED => /eqP SCHED; rewrite SCHED eq_refl.
      Qed.

      (* If the service during a time interval isn't 0, there will be
         a time t in this interval where the service isn't 0. *) 
      Lemma job_scheduled_during_interval :
        forall t1 t2,
          service_during rate sched j t1 t2 != 0 ->
          exists t,
            t1 <= t < t2 /\ 
            service_at rate sched j t != 0.
      Proof.
        intros t1 t2 NONZERO.
        destruct ([exists t: 'I_t2, (t >= t1) && (service_at rate sched j t != 0)]) eqn:EX.
        {
          move: EX => /existsP EX; destruct EX as [x EX]. move: EX => /andP [GE SERV].
          exists x; split; last by done.
          by apply/andP; split; [by done | apply ltn_ord].
        }
        {
          apply negbT in EX; rewrite negb_exists in EX; move: EX => /forallP EX.
          unfold service_during in NONZERO; rewrite big_nat_cond in NONZERO.
          rewrite (eq_bigr (fun x => 0)) in NONZERO;
            first by rewrite -big_nat_cond big_const_nat iter_addn mul0n addn0 in NONZERO.
          intros i; rewrite andbT; move => /andP [GT LT].
          specialize (EX (Ordinal LT)); simpl in EX.
          by rewrite GT andTb negbK in EX; apply/eqP.
        }
      Qed.
      
    End Basic.
    
    Section MaxRate.

      Variable max_rate: nat.

      (* There has to be a maximum rate for all processors. *)
      Hypothesis there_is_max_rate:
        forall j cpu, rate j cpu <= max_rate.

      (* One job won't be executed on more than one processor at the same time. *)
      Hypothesis no_parallelism:
        jobs_dont_execute_in_parallel sched.

      (* Service received by jobs is always less than or equal to the maximum rate. *)
      Lemma service_at_le_max_rate :
        forall t, service_at rate sched j t <= max_rate.
      Proof.
        unfold service_at, jobs_dont_execute_in_parallel in *; ins.
        destruct (scheduled sched j t) eqn:SCHED; unfold scheduled in SCHED.
        {
          move: SCHED => /exists_inP SCHED; des.
          rewrite -big_filter.
          rewrite (bigD1_seq x);
            [simpl | | by rewrite filter_index_enum enum_uniq];
              last by rewrite mem_filter; apply/andP; split;
                [by ins | by rewrite mem_index_enum].
          rewrite -big_filter -filter_predI big_filter.
          rewrite -> eq_bigr with (F2 := fun cpu => 0);
            first by rewrite big_const_seq iter_addn /= mul0n 2!addn0 there_is_max_rate.
          intro i; move => /andP [/eqP NEQ SCHEDi].
          apply no_parallelism with (cpu1 := x) in SCHEDi; [by subst | by ins].
        }
        {
          apply negbT in SCHED; rewrite negb_exists_in in SCHED.
          move: SCHED => /forall_inP SCHED.
          by rewrite big_pred0; red; ins; apply negbTE, SCHED.
        }
      Qed.
        
    End MaxRate.
        
    Section Completion.

      Hypothesis completed_jobs:
        completed_jobs_dont_execute job_cost rate sched.
      (* Let the rate on each processor be at most 1. *)
      Hypothesis max_service_one:
        forall j' t, service_at rate sched j' t <= 1.

      (* Let the service interval be the interval a job is getting service during.
         Then the length of the service interval is less than or equal to the cost of the job. *)
      Lemma service_interval_le_cost :
        forall t t',
          service_during rate sched j t t' <= job_cost j.
      Proof.
        unfold service_during; rename completed_jobs into COMP; red in COMP; ins.
        destruct (t > t') eqn:GT.
          by rewrite big_geq // -ltnS; apply ltn_trans with (n := t); ins.
          apply leq_trans with
              (n := \sum_(0 <= t0 < t') service_at rate sched j t0);
            last by apply COMP.
          rewrite -> big_cat_nat with (m := 0) (n := t);
            [by apply leq_addl | by ins | by rewrite leqNgt negbT //].
      Qed.

      (* If a job is completed at time t, it will be completed at every time t' which is later than t. *)
      Lemma completion_monotonic :
        forall t t',
          t <= t' ->
          completed job_cost rate sched j t ->
          completed job_cost rate sched j t'.
      Proof.
        unfold completed; move => t t' LE /eqP COMPt.
        rewrite eqn_leq; apply/andP; split;
          first by apply service_interval_le_cost.
        by apply leq_trans with (n := service rate sched j t);
          [by rewrite COMPt | by apply extend_sum].
      Qed.
      
    End Completion.

    Section Arrival.

      Hypothesis jobs_must_arrive:
        jobs_must_arrive_to_execute sched.

      (* The service received by a job at any time t before its arrival time is 0. ... *)
      Lemma service_before_arrival_zero :
        forall t0 (LT: t0 < job_arrival j),
          service_at rate sched j t0 = 0.
      Proof.
        rename jobs_must_arrive into ARR; red in ARR; ins.
        specialize (ARR j t0).
        apply contra with (c := scheduled sched j t0)
                            (b := has_arrived j t0) in ARR;
          last by rewrite -ltnNge.
        apply/eqP; rewrite -leqn0; unfold service_at.
        rewrite -> eq_bigr with (F2 := fun cpu => 0);
          first by rewrite big_const_seq iter_addn mul0n addn0.
        intros i SCHED; move: ARR; rewrite negb_exists_in; move => /forall_inP ARR.
        by exploit (ARR i); [by ins | ins]; destruct (sched i t0 == Some j).
      Qed.

      (* ... That's why the sum of service received by a job before its arrival time is 0, as well. *)
      Lemma sum_service_before_arrival :
        forall t1 t2 (LT: t2 <= job_arrival j),
          \sum_(t1 <= i < t2) service_at rate sched j i = 0.
      Proof.
        ins; apply/eqP; rewrite -leqn0.
        apply leq_trans with (n := \sum_(t1 <= i < t2) 0);
          last by rewrite big_const_nat iter_addn mul0n addn0.
        rewrite big_nat_cond [\sum_(_ <= _ < _) 0]big_nat_cond.
        apply leq_sum; intro i; rewrite andbT; move => /andP LTi; des.
        rewrite service_before_arrival_zero; first by ins.
        by apply leq_trans with (n := t2); ins.
      Qed.

      (* Hence, you can ignore the service received by a job before its arrival time. *)
      Lemma service_before_arrival_eq_service_during :
        forall t0 t (LT: t0 <= job_arrival j),
          \sum_(t0 <= t < job_arrival j + t) service_at rate sched j t =
          \sum_(job_arrival j <= t < job_arrival j + t) service_at rate sched j t.
      Proof.
        ins; rewrite -> big_cat_nat with (n := job_arrival j); [| by ins | by apply leq_addr].
        by rewrite /= sum_service_before_arrival; [by rewrite add0n | by apply leqnn].
      Qed.
      
    End Arrival.

  End ServiceProperties.

End Schedule.
  
Module ScheduleOfSporadicTask.

  Import SporadicTask.
  Export Schedule.

  Section ValidSchedule.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.    
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.

    Context {arr_seq: arrival_sequence Job}.
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* Whether jobs of the same task can't execute in parallel. *)
    Definition jobs_of_same_task_dont_execute_in_parallel :=
      forall (j j': JobIn arr_seq) t,
        job_task j = job_task j' ->
        scheduled sched j t -> scheduled sched j' t -> False.

  End ValidSchedule.

End ScheduleOfSporadicTask.

Module ScheduleOfTaskWithJitter.

  Export Schedule.
  
  Section ArrivalAfterJitter.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.    
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    Variable job_jitter: Job -> nat.

    Context {arr_seq: arrival_sequence Job}.
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* Whether a job can only be scheduled if it has arrived *)
    Definition jobs_execute_after_jitter :=
      forall j t,
        scheduled sched j t ->
        job_arrival j + job_jitter j <= t.

    Section BasicLemmas.

      (* The arrival time has to be before the jitter *)
      Lemma arrival_before_jitter :
        jobs_execute_after_jitter ->
        jobs_must_arrive_to_execute sched.
      Proof.
        unfold jobs_execute_after_jitter, jobs_must_arrive_to_execute.
        intros ARRIVE j t SCHED; unfold has_arrived.
        rewrite -(leq_add2r (job_jitter j)).
        by apply leq_trans with (n := t);
          [by apply ARRIVE | by apply leq_addr].
      Qed.
      
    End BasicLemmas.
 
  End ArrivalAfterJitter.

End ScheduleOfTaskWithJitter.