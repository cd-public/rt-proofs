Require Import Classical Vbase JobDefs helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Definition time := nat.

Module ArrivalSequence.

  Section ArrivalSequenceDef.

    Variable JobType: eqType. (* Assume any job type with decidable equality *)
    Variable job_arrival: JobType -> nat. (* that has a job_arrival *)

    Definition arrival_sequence := time -> seq JobType.

  End ArrivalSequenceDef.

  Section ArrivalSequenceProperties.

    Context {JobType: eqType}.
    Variable job_arrival: JobType -> nat.
    Variable arr: arrival_sequence JobType.

    (* The arrival time parameter of a job matches the time it arrives.*)
    Definition arrival_times_match :=
      forall j t, j \in arr t -> job_arrival j = t.

    (* If job j arrives at two times, then they must be the same time. *)
    Definition no_multiple_arrivals :=
      forall j t1 t2, j \in arr t1 -> j \in arr t2 -> t1 = t2.

    (* No multiple jobs arrivals at the same time. *)
    Definition arrival_sequence_unique := forall t, uniq (arr t).

    (* A valid arrival sequence satisfies the three properties above. *)
    Definition valid_arrival_sequence :=
      no_multiple_arrivals /\ arrival_times_match /\ arrival_sequence_unique.

  End ArrivalSequenceProperties.  
  
  Section ArrivingJobs.

    Context {JobType: eqType}. (* Assume any job type with decidable equality *)
    Variable arr: arrival_sequence JobType.
    Variable j: JobType.

    (* Whether a job arrives at time t. *)
    Definition arrives_at (t: time) :=  j \in arr t.

    (* A job has arrived at time t iff it arrives at some time t_0, with 0 <= t_0 <= t. *)
    Definition has_arrived (t: nat) := [exists t_0 in 'I_(t.+1), arrives_at t_0].

    (* A job arrived before t iff it arrives at some time t_0, with 0 <= t_0 < t. *)
    Definition arrived_before (t: nat) := [exists t_0 in 'I_(t), arrives_at t_0].

    (* A job arrives between t1 and t2 iff it arrives at some time t with t1 <= t < t2. *)
    Definition arrived_between (t1 t2: nat) := [exists t in 'I_(t2), ((t1 <= t) && arrives_at t)].

  End ArrivingJobs.

  Section SetOfArrivals.

    Variable JobType: eqType.
    Variable arr: arrival_sequence JobType.

    (* List of jobs that arrived before t', defined by concatenation. *)
    Definition prev_arrivals (t': time) :=  \cat_(0 <= t < t') arr t.

    (* List of jobs that arrived up to time t (inclusive) *)
    Definition all_arrivals (t': time) := \cat_(0 <= t < t'.+1) arr t.

    (* Prove that any job is in the list of arrivals iff it has arrived. *)
    Lemma in_all_arrivals_iff_has_arrived :
      forall t' j, (j \in all_arrivals t') = (has_arrived arr j t').
    Proof.
      unfold all_arrivals, has_arrived; ins.
      induction t'.
      {
        rewrite big_nat_recr // big_geq // /=.
        destruct (j \in arr 0) eqn:IN; symmetry.
          by apply/exists_inP_nat; unfold arrives_at; exists 0; split.
          {
            apply negbTE; rewrite negb_exists_in.
            apply/(forall_inP_nat 1 (fun x => ~~ arrives_at arr j x)); ins.
            move: LT; rewrite ltnS leqn0; move => /eqP LT; subst.
            by unfold arrives_at; apply negbT.
          }
      }
      {
        rewrite big_nat_recr // mem_cat IHt'.
        destruct ([exists t_0 in 'I_t'.+1, arrives_at arr j t_0] || (j \in arr t'.+1)) eqn:OR.
        {
          move: OR => /orP OR; des.
          {
            rewrite OR orTb; symmetry; apply/exists_inP_nat.
            move: OR => /exists_inP_nat OR; des.
            exists x; split; [by apply (ltn_trans OR); ins | by ins].
          }
          {
            rewrite OR orbT; symmetry; apply/exists_inP_nat.
            exists t'.+1; split; [by apply ltnSn | by ins].
          }
        }
        {
          rewrite OR; symmetry.
          apply negbT in OR; rewrite negb_or in OR.
          move: OR => /andP OR; des.
          rewrite negb_exists_in in OR.
          move: OR => /(forall_inP_nat t'.+1 (fun x => ~~ arrives_at arr j x)) OR.
          apply negbTE; rewrite negb_exists_in.
          apply/(forall_inP_nat t'.+2 (fun x => ~~ arrives_at arr j x)); ins.
          rewrite ltnS in LT; unfold arrives_at in *.
          move: LT; rewrite leq_eqVlt; move => /orP LT; des.
            by move: LT => /eqP LT; subst.
            by apply OR.
        }
      }
    Qed.

    (* Prove that any job is in the list of jobs that arrived before t' it arrived before t'.*)
    Lemma in_prev_arrivals_iff_arrived_before :
      forall t' j, j \in (prev_arrivals t') = (arrived_before arr j t').
    Proof.
      unfold prev_arrivals, arrived_before; ins.
      destruct t'; last by rewrite in_all_arrivals_iff_has_arrived.
      rewrite big_geq // in_nil; symmetry.
      apply negbTE; rewrite negb_exists_in. apply/forall_inP; ins.
      by have BUG := ltn_ord x.
    Qed.

    Section UniqueArrivals.

      Hypothesis no_multiple_job_arrivals: no_multiple_arrivals arr.
      Hypothesis arr_seq_uniq: arrival_sequence_unique arr.

      (* Prove that the list of jobs arrivals is unique. *)
      Lemma uniq_prev_arrivals : forall t, uniq (prev_arrivals t).
      Proof.
        unfold arrival_sequence_unique, no_multiple_arrivals in *;
        rename arr_seq_uniq into UNIQ, no_multiple_job_arrivals into NOMULT.
        induction t; first by unfold prev_arrivals; rewrite -/prev_arrivals big_geq //.
        unfold prev_arrivals; rewrite big_nat_recr // /=.
        rewrite cat_uniq; apply/and3P; split; [by ins | | by apply UNIQ].
        apply/hasP; unfold not; intro HAS; destruct HAS as [x IN MEM];
          rewrite -unfold_in mem_mem in MEM.
        rewrite in_prev_arrivals_iff_arrived_before in MEM; move: MEM => /exists_inP_nat MEM; des.
        by apply (NOMULT x t x0) in MEM0; [by subst; rewrite ltnn in MEM | by ins].
      Qed.

    End UniqueArrivals.
    
  End SetOfArrivals.
  
End ArrivalSequence.

Module Schedule.

  Export ArrivalSequence.

  Section ScheduleDef.

    Variable JobType: eqType. (* Assume any job type with decidable equality. *)
  
    (* Schedule mapping is defined as the amount of service given to jobs during
       discrete time [t, t+1). *)
    Definition schedule_mapping := JobType -> time -> nat.

    (* Every schedule is a pair of an arrival sequence and a mapping. *)
    Definition schedule := (arrival_sequence JobType * schedule_mapping) % type.

  End ScheduleDef.
  
  (* Define projections: arrival sequence and mapping. *)
  Coercion arr_seq_of {JobType: eqType} (sched: schedule JobType) := pair_1st sched.
  Coercion mapping_of {JobType: eqType} (sched: schedule JobType) := pair_2nd sched.
  
  Section ScheduledJobs.

    Context {JobType: eqType}. (* Assume a job type with decidable equality *)
    Variable job_cost: JobType -> nat. (* and that has a cost function. *)

    Variable sched: schedule JobType.
    Variable j: JobType.

    (* Service received by a job during [t, t+1) -- just an alias to the mapping. *)
    Definition service_at (t: time) := mapping_of sched j t.

    (* Cumulative service received during [0, t') *)
    Definition service (t': time) := \sum_(0 <= t < t') (service_at t).

    (* Cumulative service received during [t1, t2) *)
    Definition service_during (t1 t2: time) := \sum_(t1 <= t < t2) (service_at t).

    (* Whether a job is scheduled at time t *)
    Definition scheduled (t: time) := service_at t != 0.

    (* Whether a job has completed at time t (assumes costs are non-zero!) *)
    Definition completed (t: time) := (service t == job_cost j).

    (* A pending job has arrived but has not completed. *)
    Definition pending (t: time) := has_arrived sched j t && ~~completed t.

    (* Whether a job is pending and not scheduled at time t *)
    Definition backlogged (t: time) := pending t && ~~scheduled t.

    (* A carried-in job in [t1,t2) arrives before t1 and is not completed at time t1 *)
    Definition carried_in (t1: time) := arrived_before sched j t1 && ~~ completed t1.

    (* A carried-out job in [t1,t2) arrives after t1 and is not completed at time t2 *)
    Definition carried_out (t1 t2: time) := arrived_between sched j t1 t2 && ~~ completed t2.

  End ScheduledJobs.

  Section ValidSchedules.

    Context {JobType: eqType}. (* Assume a job type with decidable equality *)
    Variable job_cost: JobType -> nat. (* and that has a cost function. *)
    Variable sched: schedule JobType.

    (* Whether a job can only be scheduled if it has arrived *)
    Definition job_must_arrive_to_exec :=
      forall j t, scheduled sched j t -> has_arrived sched j t.

    (* Whether a job can be scheduled after it completes *)
    Definition completed_job_doesnt_exec :=
      forall j t, service sched j t <= job_cost j.

    Definition valid_sporadic_schedule :=
      job_must_arrive_to_exec /\ completed_job_doesnt_exec.

  End ValidSchedules.

  Section ServiceProperties.

    Variable JobType: eqType.
    Variable job_arrival: JobType -> nat.
    Variable job_cost: JobType -> nat.
    Variable sched: schedule JobType.
    Variable j: JobType.

    Section Completion.

      Hypothesis completed_jobs: completed_job_doesnt_exec job_cost sched.
      Hypothesis max_service_one: forall j' t, service_at sched j' t <= 1.

      Lemma service_interval_le_cost :
        forall t t', service_during sched j t t' <= job_cost j.
      Proof.
        unfold service_during; rename completed_jobs into COMP; red in COMP; ins.
        destruct (t > t') eqn:GT.
          by rewrite big_geq // -ltnS; apply ltn_trans with (n := t); ins.
          apply leq_trans with (n := \sum_(0 <= t0 < t') service_at sched j t0);
            last by apply COMP.
          rewrite -> big_cat_nat with (m := 0) (n := t);
            [by apply leq_addl | by ins | by rewrite leqNgt negbT //].
      Qed.

    End Completion.

    Section Arrival.

      Hypothesis jobs_must_arrive: job_must_arrive_to_exec sched.
      Hypothesis arrival_times_valid: arrival_times_match job_arrival sched.
      Hypothesis no_multiple_job_arrivals: no_multiple_arrivals sched.

      Lemma service_before_arrival_zero :
        forall t0 (LT: t0 < job_arrival j), service_at sched j t0 = 0.
      Proof.
        unfold no_multiple_arrivals, arrival_times_match in *.
        rename jobs_must_arrive into ARR; red in ARR; ins.
        specialize (ARR j t0).
        apply contra with (c := scheduled sched j t0) (b := has_arrived sched j t0) in ARR;
          first by rewrite -/scheduled negbK in ARR; apply/eqP.
        {
          destruct (classic (exists arr_j, arrives_at sched j arr_j)) as [ARRIVAL|NOARRIVAL]; des;
          last by apply/negP; move => /exists_inP_nat ARRIVED; des; apply NOARRIVAL; exists x.
          {
            generalize ARRIVAL; apply arrival_times_valid in ARRIVAL; ins.
            rewrite -> ARRIVAL in *.
            apply/negP; unfold not, has_arrived; move => /exists_inP_nat ARRIVED; des.
            apply leq_trans with (p := arr_j) in ARRIVED; last by ins.
            apply no_multiple_job_arrivals with (t1 := x) in ARRIVAL0; last by ins.
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
        rewrite service_before_arrival_zero; first by ins.
        by apply leq_trans with (n := t2); ins.
      Qed.

    End Arrival.

  End ServiceProperties.

End Schedule.

(* Specific definitions for schedules of sporadic tasks *)
Module ScheduleOfSporadicTask.

  Import SporadicTaskJob.
  Export Schedule.

  Section EarlierJobs.

    Variable JobType: eqType.
    Variable job_cost: JobType -> nat.
    Variable job_task: JobType -> sporadic_task.
    Variable sched: schedule JobType.

    (* Whether job j1 arrives earlier than j2 (both are from the same task) *)
    Definition earlier_job (j1 j2: JobType) :=
      job_task j1 = job_task j2 /\
      exists arr1 arr2, arrives_at sched j1 arr1 /\
                        arrives_at sched j2 arr2 /\
                        arr1 < arr2.

    Definition exists_earlier_job (t: time) (jlow: JobType) :=
      exists j0, earlier_job j0 jlow /\ (pending job_cost) sched j0 t.

    (* TODO: Can we not have to pass job_cost as a parameter?
             If pending is a function of a type that has job_cost function? *)
    
End EarlierJobs.

End ScheduleOfSporadicTask.