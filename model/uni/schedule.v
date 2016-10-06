Require Import rt.util.all.
Require Import rt.model.time rt.model.task rt.model.job rt.model.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module UniprocessorSchedule.

  Import SporadicTaskset.
  Export Time ArrivalSequence.

  Section Schedule.

    (* We begin by defining a uniprocessor schedule. *)
    Section ScheduleDef.

      Context {Job: eqType}.
      Variable job_cost: Job -> time.

      (* Consider any job arrival sequence. *)
      Variable arr_seq: arrival_sequence Job.

      (* A uniprocessor schedule associates each point in time to either
         Some job that is scheduled or None, if the processor is idle. *)
      Definition schedule := time -> option (JobIn arr_seq).

    End ScheduleDef.

    (* In this section, we define properties of a schedule. *)
    Section ScheduleProperties.

      Context {Job: eqType}.
      Variable job_cost: Job -> time.

      (* Consider any uniprocessor schedule. *)
      Context {arr_seq: arrival_sequence Job}.
      Variable sched: schedule arr_seq.

      (* Let's define properties of the jobs to be scheduled. *)
      Section JobProperties.
        
        (* Let j be any job from the arrival sequence. *)
        Variable j: JobIn arr_seq.

        (* First, we define whether a job j is scheduled at time t, ... *)
        Definition scheduled_at (t: time) := sched t == Some j.

        (* ...which also yields the instantaneous service received by
           job j at time t (i.e., either 0 or 1). *)
        Definition service_at (t: time) : time := scheduled_at t.

        (* Based on the notion of instantaneous service, we define the
           cumulative service received by job j during any interval [t1, t2). *)
        Definition service_during (t1 t2: time) :=
          \sum_(t1 <= t < t2) service_at t.

        (* Using the previous definition, we define the cumulative service
           received by job j up to time t, i.e., during interval [0, t). *)
        Definition service (t: time) := service_during 0 t.

        (* Next, we say that job j has completed by time t if it received enough
           service in the interval [0, t). *)
        Definition completed_by (t: time) := service t == job_cost j.

        (* Job j is pending at time t iff it has arrived but has not yet completed. *)
        Definition pending (t: time) := has_arrived j t && ~~completed_by t.

        (* Job j is backlogged at time t iff it is pending and not scheduled. *)
        Definition backlogged (t: time) := pending t && ~~scheduled_at t.

      End JobProperties.

      (* In this section, we define some properties of the processor. *)
      Section ProcessorProperties.

        (* We say that the processor is idle at time t iff there is no job being scheduled. *)
        Definition is_idle (t: time) := sched t == None.

        (* In addition, we define the total service performed by the processor in any interval
           [t1, t2) as the cumulative time in which the processor is not idle. *)
        Definition total_service_during (t1 t2: time) :=
          \sum_(t1 <= t < t2) ~~ is_idle t.

        (* Using the previous definition, we also define the total service up to time t2.*)
        Definition total_service (t2: time) := total_service_during 0 t2.

      End ProcessorProperties.
      
    End ScheduleProperties.

    (* In this section, we define properties of valid schedules. *)
    Section ValidSchedules.

      Context {Job: eqType}.
      Variable job_cost: Job -> time.

      (* Consider any uniprocessor schedule. *)
      Context {arr_seq: arrival_sequence Job}.
      Variable sched: schedule arr_seq.

      (* We define whether a job can only be scheduled if it has arrived ... *)
      Definition jobs_must_arrive_to_execute :=
        forall j t, scheduled_at sched j t -> has_arrived j t.

      (* ... and whether a job can be scheduled after it completes. *)
      Definition completed_jobs_dont_execute :=
        forall j t, service sched j t <= job_cost j.

    End ValidSchedules.

    (* In this section, we prove some basic lemmas about schedules. *)   
    Section Lemmas.

      Context {Job: eqType}.
      Variable job_cost: Job -> time.

      (* Consider any uniprocessor schedule. *)
      Context {arr_seq: arrival_sequence Job}.
      Variable sched: schedule arr_seq.

      (* Let's begin with lemmas about service. *)
      Section Service.

        (* Let j be any job that is to be scheduled. *)
        Variable j: JobIn arr_seq.
        
        (* First, we prove that the instantaneous service cannot be greater than 1, ... *)
        Lemma service_at_most_one:
          forall t, service_at sched j t <= 1.
        Proof.
          by intros t; apply leq_b1.
        Qed.

        (* ...which implies that the cumulative service received by job j in any
           interval of length delta is at most delta. *)
        Lemma cumulative_service_le_delta:
          forall t delta,
            service_during sched j t (t + delta) <= delta.
        Proof.
          unfold service_during; intros t delta.
          apply leq_trans with (n := \sum_(t <= t0 < t + delta) 1);
            last by simpl_sum_const; rewrite addKn leqnn.
          by apply leq_sum; intros t0 _; apply leq_b1.
        Qed.

      End Service.

      (* Next, we prove properties related to job completion. *)
      Section Completion.

        (* Assume that completed jobs do not execute. *)
        Hypothesis H_completed_jobs:
          completed_jobs_dont_execute job_cost sched.
              
        (* Let j be any job that is to be scheduled. *)
        Variable j: JobIn arr_seq.
        
        (* We prove that after job j completes, it remains completed. *)
        Lemma completion_monotonic:
          forall t t',
            t <= t' ->
            completed_by job_cost sched j t ->
            completed_by job_cost sched j t'.
        Proof.
          unfold completed_by; move => t t' LE /eqP COMPt.
          rewrite eqn_leq; apply/andP; split; first by apply H_completed_jobs.
          by apply leq_trans with (n := service sched j t);
            [by rewrite COMPt | by apply extend_sum].
        Qed.

        (* We also prove that a completed job cannot be scheduled. *)
        Lemma completed_implies_not_scheduled :
          forall t,
            completed_by job_cost sched j t ->
            ~~ scheduled_at sched j t.
        Proof.
          rename H_completed_jobs into COMP.
          unfold completed_jobs_dont_execute in *.
          intros t COMPLETED.
          apply/negP; red; intro SCHED.
          have BUG := COMP j t.+1.
          rewrite leqNgt in BUG; move: BUG => /negP BUG; apply BUG.
          unfold service, service_during; rewrite big_nat_recr // /= -addn1.
          apply leq_add; first by move: COMPLETED => /eqP <-.
          by rewrite /service_at SCHED.
        Qed.
        
        (* Next, we show that the service received by job j in any interval
           is no larger than its cost. *)
        Lemma cumulative_service_le_job_cost :
          forall t t',
            service_during sched j t t' <= job_cost j.
        Proof.
          unfold service_during; rename H_completed_jobs into COMP; red in COMP; ins.
          destruct (t > t') eqn:GT.
            by rewrite big_geq // -ltnS; apply ltn_trans with (n := t); ins.
            apply leq_trans with
                (n := \sum_(0 <= t0 < t') service_at sched j t0);
              last by apply COMP.
            rewrite -> big_cat_nat with (m := 0) (n := t);
              [by apply leq_addl | by ins | by rewrite leqNgt negbT //].
        Qed.
      
      End Completion.

      (* In this section we prove properties related to job arrivals. *)
      Section Arrival.

        (* Assume that jobs must arrive to execute. *)
        Hypothesis H_jobs_must_arrive:
          jobs_must_arrive_to_execute sched.

        (* Let j be any job that is to be scheduled. *)
        Variable j: JobIn arr_seq.

        (* First, we show that job j does not receive service at any time t
           prior to its arrival. *)
        Lemma service_before_job_arrival_zero :
          forall t,
            t < job_arrival j ->
            service_at sched j t = 0.
        Proof.
          rename H_jobs_must_arrive into ARR; red in ARR; intros t LT.
          specialize (ARR j t).
          apply contra with (c := scheduled_at sched j t)
                              (b := has_arrived j t) in ARR;
            last by rewrite -ltnNge.
          by apply/eqP; rewrite eqb0.
        Qed.

        (* Note that the same property applies to the cumulative service. *)
        Lemma cumulative_service_before_job_arrival_zero :
          forall t1 t2,
            t2 <= job_arrival j ->
            \sum_(t1 <= i < t2) service_at sched j i = 0.
        Proof.
          intros t1 t2 LE; apply/eqP; rewrite -leqn0.
          apply leq_trans with (n := \sum_(t1 <= i < t2) 0);
            last by rewrite big_const_nat iter_addn mul0n addn0.
          rewrite big_nat_cond [\sum_(_ <= _ < _) 0]big_nat_cond.
          apply leq_sum; intro i; rewrite andbT; move => /andP LTi; des.
          rewrite service_before_job_arrival_zero; first by ins.
          by apply leq_trans with (n := t2); ins.
        Qed.

        (* Hence, one can ignore the service received by a job before its arrival time. *)
        Lemma ignore_service_before_arrival:
          forall t1 t2,
            t1 <= job_arrival j ->
            t2 >= job_arrival j ->
            \sum_(t1 <= t < t2) service_at sched j t =
              \sum_(job_arrival j <= t < t2) service_at sched j t.
        Proof.
          intros t1 t2 LE1 GE2.
          rewrite -> big_cat_nat with (n := job_arrival j);
            [| by done | by done].
          by rewrite /= cumulative_service_before_job_arrival_zero; [rewrite add0n | apply leqnn].
        Qed.

      End Arrival.

      (* In this section, we prove properties about pending jobs. *)
      Section Pending.

        (* Assume that jobs must arrive to execute... *)
        Hypothesis H_jobs_must_arrive:
          jobs_must_arrive_to_execute sched.

       (* ...and that completed jobs do not execute. *)
        Hypothesis H_completed_jobs:
          completed_jobs_dont_execute job_cost sched.

        (* Let j be any job. *)
        Variable j: JobIn arr_seq.

        (* First, we show that if job j is scheduled, then it must be pending. *)
        Lemma scheduled_implies_pending:
          forall t,
            scheduled_at sched j t ->
            pending job_cost sched j t.
        Proof.
          rename H_jobs_must_arrive into ARRIVE,
                 H_completed_jobs into COMP.
          unfold jobs_must_arrive_to_execute, completed_jobs_dont_execute in *.
          intros t SCHED.
          unfold pending; apply/andP; split; first by apply ARRIVE.
          apply/negP; unfold not; intro COMPLETED.
          have BUG := COMP j t.+1.
          rewrite leqNgt in BUG; move: BUG => /negP BUG; apply BUG.
          unfold service, service_during; rewrite -addn1 big_nat_recr // /=.
          apply leq_add;
            first by move: COMPLETED => /eqP COMPLETED; rewrite -COMPLETED.
          by rewrite /service_at SCHED.
        Qed.

      End Pending.

      (* In this section we show that the schedule is unique at any point. *)
      Section OnlyOneJobScheduled.

        (* Let j1 and j2 be any jobs. *)
        Variable j1 j2: JobIn arr_seq.

        (* At any time t, if both j1 and j2 are scheduled, then they must be the same job. *)
        Lemma only_one_job_scheduled:
          forall t,
            scheduled_at sched j1 t ->
            scheduled_at sched j2 t ->
            j1 = j2.
        Proof.
          move => t /eqP SCHED1 /eqP SCHED2.
          by rewrite SCHED1 in SCHED2; inversion SCHED2.
        Qed.
          
      End OnlyOneJobScheduled.        
      
    End Lemmas.
  
  End Schedule.

End UniprocessorSchedule.