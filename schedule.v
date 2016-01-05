Require Import Vbase job task util_lemmas arrival_sequence
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Definition, properties and lemmas about schedules. *)
Module Schedule.

  Export ArrivalSequence.

  (* A processor is defined as a bounded natural number: [0, num_cpus). *)
  Definition processor (num_cpus: nat) := 'I_num_cpus.
  
  Section ScheduleDef.

    Context {Job: eqType}.

    (* Given the number of processors and an arrival sequence, ...*)
    Variable num_cpus: nat.
    Variable arr_seq: arrival_sequence Job.

    (* ... we define a schedule as a mapping such that each processor
       at each time contains either a job from the sequence or none. *)
    Definition schedule :=
      processor num_cpus -> time -> option (JobIn arr_seq).

  End ScheduleDef.

  (* Next, we define properties of jobs in a schedule. *)
  Section ScheduledJobs.

    Context {Job: eqType}.

    (* Given an arrival sequence, ... *)
    Context {arr_seq: arrival_sequence Job}.
    
    Variable job_cost: Job -> nat. (* ... a job cost function, ... *)

    (* ... a rate function for each job/processor, ...*)
    Context {num_cpus: nat}.
    Variable rate: Job -> processor num_cpus -> nat.

    (* ... we define the following properties for job j in schedule sched. *)
    Variable sched: schedule num_cpus arr_seq.
    Variable j: JobIn arr_seq.

    (* A job j is scheduled at time t iff there exists a cpu where it is mapped.*)
    Definition scheduled (t: time) :=
      [exists cpu in 'I_(num_cpus), sched cpu t == Some j].

    (* A processor cpu is idle at time t if it doesn't contain any jobs. *)
    Definition is_idle (cpu: 'I_(num_cpus)) (t: time) :=
      sched cpu t = None.

    (* The instantaneous service of job j at time t is the sum of the rate of every cpu where
       it is scheduled on. Note that although we use a sum, we usually assume no parallelism. *)
    Definition service_at (t: time) :=
      \sum_(cpu < num_cpus | sched cpu t == Some j) rate j cpu.

    (* The cumulative service received by job j during [0, t'). *)
    Definition service (t': time) := \sum_(0 <= t < t') service_at t.

    (* The cumulative service received by job j during [t1, t2). *)
    Definition service_during (t1 t2: time) := \sum_(t1 <= t < t2) service_at t.
    
    (* Job j has completed at time t if it received enough service. *)
    Definition completed (t: time) := service t == job_cost j.

    (* Job j is pending at time t iff it has arrived but has not completed. *)
    Definition pending (t: time) := has_arrived j t && ~~completed t.

    (* Job j is backlogged at time t iff it is pending and not scheduled. *)
    Definition backlogged (t: time) := pending t && ~~scheduled t.

    (* Job j is carry-in in interval [t1, t2) iff it arrives before t1 and is
       not complete at time t1 *)
    Definition carried_in (t1: time) := arrived_before j t1 && ~~ completed t1.

    (* Job j is carry-out in interval [t1, t2) iff it arrives after t1 and is
       not complete at time t2 *)
    Definition carried_out (t1 t2: time) := arrived_between j t1 t2 && ~~ completed t2.

    (* The list of scheduled jobs at time t is the concatenation of the jobs
       scheduled on each processor. *)
    Definition jobs_scheduled_at (t: time) :=
      \cat_(cpu < num_cpus) make_sequence (sched cpu t).
    
    (* The list of jobs scheduled during the interval [t1, t2) is the
       the duplicate-free concatenation of the jobs scheduled at instant. *)
    Definition jobs_scheduled_between (t1 t2: time) :=
      undup (\cat_(t1 <= t < t2) jobs_scheduled_at t).

  End ScheduledJobs.

  (* In this section, we define properties of valid schedules. *)
  Section ValidSchedules.

    Context {Job: eqType}. (* Assume a job type with decidable equality, ...*)
    Context {arr_seq: arrival_sequence Job}. (* ..., an arrival sequence, ...*)
    Context {num_cpus: nat}.
    
    Variable job_cost: Job -> nat. (* ... a cost function, .... *)

    (* ... a rate function and a schedule. Then we define...*)
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    (* ... whether job parallelism is disallowed, ... *)
    Definition jobs_dont_execute_in_parallel :=
      forall j t cpu1 cpu2,
        sched cpu1 t == Some j -> sched cpu2 t == Some j -> cpu1 = cpu2.

    (* ... whether a job can only be scheduled if it has arrived, ... *)
    Definition jobs_must_arrive_to_execute :=
      forall j t, scheduled sched j t -> has_arrived j t.

    (* ... whether a job can be scheduled after it completes. *)
    Definition completed_jobs_dont_execute :=
      forall j t, service rate sched j t <= job_cost j.

  End ValidSchedules.

  (* In this section, we prove some basic lemmas about service. *)
  Section ServiceLemmas.

    (* Consider an arrival sequence, ...*)
    Context {Job: eqType}.
    Context {arr_seq: arrival_sequence Job}.

    (* ... a job cost function, ...*)
    Variable job_cost: Job -> nat.

    (* ..., and a particular schedule. *)
    Variable num_cpus: nat.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    (* Next, we prove some lemmas about the service received by a job j. *)
    Variable j: JobIn arr_seq.

    Section Basic.

      (* At any time t, if job j is not scheduled, it doesn't get service. *)
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

      (* If the cumulative service during a time interval is not zero, there
         must be a time t in this interval where the service is not 0. *) 
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

      (* Assume a maximum rate for all jobs/processors, ... *)
      Variable max_rate: nat.
      Hypothesis there_is_max_rate:
        forall j cpu, rate j cpu <= max_rate.

      (* ... and assume that a job cannot execute in parallel. Then... *)
      Hypothesis no_parallelism:
        jobs_dont_execute_in_parallel sched.

      (* ..., the service received by job j at any time t is limited by the rate. *)
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

      (* Assume that completed jobs do not execute. *)
      Hypothesis H_completed_jobs:
        completed_jobs_dont_execute job_cost rate sched.


      (* Then, after job j completes, it remains completed. *)
      Lemma completion_monotonic :
        forall t t',
          t <= t' ->
          completed job_cost rate sched j t ->
          completed job_cost rate sched j t'.
      Proof.
        unfold completed; move => t t' LE /eqP COMPt.
        rewrite eqn_leq; apply/andP; split; first by apply H_completed_jobs.
        by apply leq_trans with (n := service rate sched j t);
          [by rewrite COMPt | by apply extend_sum].
      Qed.
      
      (* Also, the service received by job j in any interval is no larger than its cost. *)
      Lemma cumulative_service_le_job_cost :
        forall t t',
          service_during rate sched j t t' <= job_cost j.
      Proof.
        unfold service_during; rename H_completed_jobs into COMP; red in COMP; ins.
        destruct (t > t') eqn:GT.
          by rewrite big_geq // -ltnS; apply ltn_trans with (n := t); ins.
          apply leq_trans with
              (n := \sum_(0 <= t0 < t') service_at rate sched j t0);
            last by apply COMP.
          rewrite -> big_cat_nat with (m := 0) (n := t);
            [by apply leq_addl | by ins | by rewrite leqNgt negbT //].
      Qed.


      
    End Completion.

    Section Arrival.

      (* Assume that jobs must arrive to execute. *)
      Hypothesis H_jobs_must_arrive:
        jobs_must_arrive_to_execute sched.

      (* Then, job j does not receive service at any time t prior to its arrival. *)
      Lemma service_before_job_arrival_zero :
        forall t (LT: t < job_arrival j),
          service_at rate sched j t = 0.
      Proof.
        rename H_jobs_must_arrive into ARR; red in ARR; ins.
        specialize (ARR j t).
        apply contra with (c := scheduled sched j t)
                            (b := has_arrived j t) in ARR;
          last by rewrite -ltnNge.
        apply/eqP; rewrite -leqn0; unfold service_at.
        rewrite -> eq_bigr with (F2 := fun cpu => 0);
          first by rewrite big_const_seq iter_addn mul0n addn0.
        intros i SCHED; move: ARR; rewrite negb_exists_in; move => /forall_inP ARR.
        by exploit (ARR i); [by ins | ins]; destruct (sched i t == Some j).
      Qed.

      (* The same applies for the cumulative service received by job j. *)
      Lemma cumulative_service_before_job_arrival_zero :
        forall t1 t2 (LT: t2 <= job_arrival j),
          \sum_(t1 <= i < t2) service_at rate sched j i = 0.
      Proof.
        ins; apply/eqP; rewrite -leqn0.
        apply leq_trans with (n := \sum_(t1 <= i < t2) 0);
          last by rewrite big_const_nat iter_addn mul0n addn0.
        rewrite big_nat_cond [\sum_(_ <= _ < _) 0]big_nat_cond.
        apply leq_sum; intro i; rewrite andbT; move => /andP LTi; des.
        rewrite service_before_job_arrival_zero; first by ins.
        by apply leq_trans with (n := t2); ins.
      Qed.

      (* Hence, you can ignore the service received by a job before its arrival time. *)
      Lemma service_before_arrival_eq_service_during :
        forall t0 t (LT: t0 <= job_arrival j),
          \sum_(t0 <= t < job_arrival j + t) service_at rate sched j t =
          \sum_(job_arrival j <= t < job_arrival j + t) service_at rate sched j t.
      Proof.
        ins; rewrite -> big_cat_nat with (n := job_arrival j); [| by ins | by apply leq_addr].
        by rewrite /= cumulative_service_before_job_arrival_zero; [rewrite add0n | apply leqnn].
      Qed.
      
    End Arrival.

  End ServiceLemmas.

End Schedule.

(* Specific properties of a schedule of sporadic jobs. *)
Module ScheduleOfSporadicTask.

  Import SporadicTask Job.
  Export Schedule.

  Section ValidSchedule.

    (* Assume the job cost and task are known. *)
    Context {sporadic_task: eqType}.
    Context {Job: eqType}.    
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.

    (* Then, in a valid schedule of sporadic tasks, ...*)
    Context {arr_seq: arrival_sequence Job}.
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* ... jobs of the same task cannot execute in parallel. *)
    Definition jobs_of_same_task_dont_execute_in_parallel :=
      forall (j j': JobIn arr_seq) t,
        job_task j = job_task j' ->
        scheduled sched j t -> scheduled sched j' t -> False.
    
  End ValidSchedule.

  Section BasicLemmas.

    (* Assume the job cost and task are known. *)
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    Context {Job: eqType}.    
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.

    (* Then, in a valid schedule of sporadic tasks ...*)
    Context {arr_seq: arrival_sequence Job}.
    Context {num_cpus: nat}.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    (* ...such that jobs do not execute after completion, ...*)
    Hypothesis jobs_dont_execute_after_completion :
       completed_jobs_dont_execute job_cost rate sched.

    Variable tsk: sporadic_task.
    
    Variable j: JobIn arr_seq.
    Hypothesis H_job_of_task: job_task j = tsk.
    Hypothesis valid_job:
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
    
    (* Remember that for any job of tsk, service <= task_cost tsk *)
    Lemma cumulative_service_le_task_cost :
        forall t t',
          service_during rate sched j t t' <= task_cost tsk.
    Proof.
      rename valid_job into VALID; unfold valid_sporadic_job in *; ins; des.
      apply leq_trans with (n := job_cost j);
        last by rewrite -H_job_of_task; apply VALID0.
      by apply cumulative_service_le_job_cost.
    Qed.

  End BasicLemmas.
  
End ScheduleOfSporadicTask.

(* Specific properties for a schedule of sporadic tasks with jitter. *)
Module ScheduleOfTaskWithJitter.

  Export ScheduleOfSporadicTask.
  
  Section ArrivalAfterJitter.

    (* Assume the job cost, task and jitter are known. *)
    Context {sporadic_task: eqType}.
    Context {Job: eqType}.    
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    Variable job_jitter: Job -> nat.

    (* Then, in a valid schedule of sporadic jobs with jitter, ... *)
    Context {arr_seq: arrival_sequence Job}.
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* ... a job can only be scheduled after the jitter. *)
    Definition jobs_execute_after_jitter :=
      forall j t,
        scheduled sched j t ->
        job_arrival j + job_jitter j <= t.

    Section BasicLemmas.

      (* Note that if a job only executes after the jitter, it also only
         executes after its arrival time. *)
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