Require Import Vbase JobDefs TaskDefs helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Definition time := nat.

Module ArrivalSequence.

  (*
  Section ArrivalSequenceDef.

    Variable Job: eqType. (* Assume any job type with decidable equality *)
    Variable job_arrival: Job -> nat. (* that has a job_arrival *)

    Definition arrival_sequence := time -> seq Job.

  End ArrivalSequenceDef.

  Section ArrivalSequenceProperties.

    Context {Job: eqType}.
    Variable job_arrival: Job -> nat.
    Variable arr: arrival_sequence Job.

    (* The arrival time parameter of a job matches the time it arrives.*)
    Definition arrival_times_match :=
      forall j t, j \in arr t <-> job_arrival j = t.

    (* If job j arrives at two times, then they must be the same time. *)
    Definition no_multiple_arrivals :=
      forall j t1 t2, j \in arr t1 -> j \in arr t2 -> t1 = t2.

    (* No multiple jobs arrivals at the same time. *)
    Definition arrival_sequence_is_a_set := forall t, uniq (arr t).

    (* A valid arrival sequence satisfies the three properties above. *)
    Definition valid_arrival_sequence :=
      no_multiple_arrivals /\ arrival_times_match /\ arrival_sequence_is_a_set.

  End ArrivalSequenceProperties.  *)
  
  Section ArrivingJobs.

    Context {Job: eqType}. (* Assume any job type with decidable equality *)
    Variable job_arrival: Job -> nat.
    Variable j: Job.

    (* Whether a job arrives at time t. *)
    Definition arrives_at (t: time) := job_arrival j == t.

    (* A job has arrived at time t iff it arrives at some time t_0, with 0 <= t_0 <= t. *)
    Definition has_arrived (t: nat) := job_arrival j <= t.

    (* A job arrived before t iff it arrives at some time t_0, with 0 <= t_0 < t. *)
    Definition arrived_before (t: nat) := job_arrival j < t.

    (* A job arrives between t1 and t2 iff it arrives at some time t with t1 <= t < t2. *)
    Definition arrived_between (t1 t2: nat) := t1 <= job_arrival j < t2.

  End ArrivingJobs.

  (*Section SetOfArrivals.

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
    
  End SetOfArrivals.*)
  
End ArrivalSequence.

Module Schedule.

  Export ArrivalSequence.

  Definition processor := nat.
  
  Section ScheduleDef.

    Variable Job: eqType. (* Assume any job type with decidable equality. *)

    Definition schedule := processor -> time -> option Job.

  End ScheduleDef.
  
  Section ScheduledJobs.

    Context {Job: eqType}. (* Assume a job type with decidable equality, *)
    Variable job_arrival: Job -> nat. (* a job arrival time, *)
    Variable job_cost: Job -> nat. (* and a cost. *)

    Variable num_cpus: nat.
    Variable rate: Job -> processor -> nat.
    Variable sched: schedule Job.
    Variable j: Job.

    (* Whether a job is scheduled at time t *)
    Definition scheduled (t: time) :=
      [exists cpu in 'I_(num_cpus), (sched cpu t == Some j)].

    Definition service_at (t: time) :=
      \sum_(0 <= cpu < num_cpus) (sched cpu t == Some j) * (rate j cpu).

    (* Cumulative service received during [0, t') *)
    Definition service (t': time) := \sum_(0 <= t < t') service_at t.

    (* Cumulative service received during [t1, t2) *)
    Definition service_during (t1 t2: time) := \sum_(t1 <= t < t2) service_at t.
    
    (* Whether a job has completed at time t *)
    Definition completed (t: time) := service t == job_cost j.

    (* A pending job has arrived but has not completed. *)
    Definition pending (t: time) := (has_arrived job_arrival) j t && ~~completed t.

    (* Whether a job is pending and not scheduled at time t *)
    Definition backlogged (t: time) := pending t && ~~scheduled t.

    (* A carried-in job in [t1,t2) arrives before t1 and is not completed at time t1 *)
    Definition carried_in (t1: time) := (arrived_before job_arrival) j t1 && ~~ completed t1.

    (* A carried-out job in [t1,t2) arrives after t1 and is not completed at time t2 *)
    Definition carried_out (t1 t2: time) := (arrived_between job_arrival) j t1 t2 && ~~ completed t2.

  End ScheduledJobs.

  Section ValidSchedules.

    Context {Job: eqType}. (* Assume a job type with decidable equality *)
    Variable job_arrival: Job -> nat.
    Variable job_cost: Job -> nat. (* and that has a cost function. *)

    Variable num_cpus: nat.
    Variable rate: Job -> processor -> nat.
    Variable sched: schedule Job.

    (* Whether job parallelism is disallowed *)
    Definition jobs_dont_execute_in_parallel :=
      forall j t cpu1 cpu2,
        sched cpu1 t == Some j -> sched cpu2 t == Some j -> cpu1 = cpu2.
    
    (* Whether a job can only be scheduled if it has arrived *)
    Definition job_must_arrive_to_exec :=
      forall j t, scheduled num_cpus sched j t -> has_arrived job_arrival j t.

    (* Whether a job can be scheduled after it completes *)
    Definition completed_job_doesnt_exec :=
      forall j t, service num_cpus rate sched j t <= job_cost j.

    Definition valid_sporadic_schedule :=
      job_must_arrive_to_exec /\ completed_job_doesnt_exec.

  End ValidSchedules.

  Section ServiceProperties.

    Context {Job: eqType}.
    Variable job_arrival: Job -> nat.
    Variable job_cost: Job -> nat.

    Variable num_cpus: nat.
    Variable rate: Job -> processor -> nat.
    Variable sched: schedule Job.
    Variable j: Job.

    Section Basic.

      Lemma service_monotonic :
        forall t t',
          t <= t' ->
            service num_cpus rate sched j t <= service num_cpus rate sched j t'.
      Proof.
        unfold service; ins; rewrite -> big_cat_nat with (p := t') (n := t);
          by  [apply leq_addr | by ins | by ins].
      Qed.

    End Basic.
    
    Section MaxRate.

      Variable max_rate: nat.
      Hypothesis there_is_max_rate:
        forall j cpu, rate j cpu <= max_rate.

      Hypothesis no_parallelism:
        jobs_dont_execute_in_parallel sched.

      Lemma service_at_le_max_rate :
        forall t, service_at num_cpus rate sched j t <= max_rate.
      Proof.
        unfold service_at, jobs_dont_execute_in_parallel in *; ins.
        rewrite -> eq_bigr with (F2 := fun cpu => if sched cpu t == Some j then rate j cpu else 0);
          last by ins; rewrite mulnbl.
        rewrite -big_mkcond /=.
        destruct (scheduled num_cpus sched j t) eqn:SCHED; unfold scheduled in SCHED.
        {
          move: SCHED => /(exists_inP_nat num_cpus (fun cpu => sched cpu t == Some j)) SCHED; des.
          rewrite -big_filter.
          rewrite (bigD1_seq x); [simpl | | by rewrite filter_uniq // iota_uniq];
            last by rewrite mem_filter; apply/andP; split;
              [by ins | by rewrite mem_iota; apply/andP; split; [by ins | by rewrite subn0 add0n]].
          rewrite -big_filter -filter_predI big_filter.
          rewrite -> eq_bigr with (F2 := fun cpu => 0);
            first by rewrite big_const_seq iter_addn /= mul0n 2!addn0 there_is_max_rate.
          intro i; move => /andP [/eqP NEQ SCHEDi].
          apply no_parallelism with (cpu1 := x) in SCHEDi; [by subst | by ins].
        }
        {
          apply negbT in SCHED; rewrite negb_exists_in in SCHED.
          move: SCHED => /(forall_inP_nat num_cpus (fun cpu => sched cpu t != Some j)) SCHED.
          rewrite big_nat_cond big_pred0 //; red; ins; apply/negP; move => /andP [LT EQ].
          by specialize (SCHED x LT); move: EQ => /eqP EQ; rewrite EQ eq_refl in SCHED.
        }
      Qed.
        
    End MaxRate.
        
    Section Completion.

      Hypothesis completed_jobs:
        completed_job_doesnt_exec job_cost num_cpus rate sched.
      Hypothesis max_service_one:
        forall j' t, service_at num_cpus rate sched j' t <= 1.

      Lemma service_interval_le_cost :
        forall t t',
          service_during num_cpus rate sched j t t' <= job_cost j.
      Proof.
        unfold service_during; rename completed_jobs into COMP; red in COMP; ins.
        destruct (t > t') eqn:GT.
          by rewrite big_geq // -ltnS; apply ltn_trans with (n := t); ins.
          apply leq_trans with
              (n := \sum_(0 <= t0 < t') service_at num_cpus rate sched j t0);
            last by apply COMP.
          rewrite -> big_cat_nat with (m := 0) (n := t);
            [by apply leq_addl | by ins | by rewrite leqNgt negbT //].
      Qed.

    End Completion.

    Section Arrival.

      Hypothesis jobs_must_arrive:
        job_must_arrive_to_exec job_arrival num_cpus sched.
      (*Hypothesis arrival_times_valid:
        arrival_times_match job_arrival sched.
      Hypothesis no_multiple_job_arrivals: no_multiple_arrivals sched.*)

      Lemma service_before_arrival_zero :
        forall t0 (LT: t0 < job_arrival j),
          service_at num_cpus rate sched j t0 = 0.
      Proof.
        rename jobs_must_arrive into ARR; red in ARR; ins.
        specialize (ARR j t0).
        apply contra with (c := scheduled num_cpus sched j t0) (b := has_arrived job_arrival j t0) in ARR; last by rewrite -ltnNge.
        apply/eqP; rewrite -leqn0; unfold service_at.
        apply leq_trans with (n := \sum_(0 <= cpu < num_cpus) 0);
          last by rewrite big_const_nat iter_addn mul0n addn0 leqnn.
        rewrite big_nat_cond [\sum_(_ <= _ < _) 0]big_nat_cond.
        apply leq_sum; intro i; rewrite andbT; move => /andP [_ LTcpus].
        rewrite leqn0 muln_eq0; apply/orP; left.
        unfold scheduled in ARR.
        rewrite negb_exists_in in ARR.
        move: ARR => /(forall_inP_nat num_cpus (fun x => sched x t0 != Some j)) ARR.
        apply/eqP; specialize (ARR i LTcpus).
        by destruct (sched i t0 == Some j).
      Qed.

      Lemma sum_service_before_arrival :
        forall t1 t2 (LT: t2 <= job_arrival j),
          \sum_(t1 <= i < t2) service_at num_cpus rate sched j i = 0.
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

  Import SporadicTask.
  Export Schedule.

  Section EarlierJobs.

    Variable Job: eqType.
    Variable job_arrival: Job -> nat.
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.

    Variable num_cpus: nat.
    Variable rate: Job -> processor -> time.
    Variable sched: schedule Job.

    (* Whether job j1 arrives earlier than j2 (same task) *)
    Definition earlier_job (j1 j2: Job) :=
      job_task j1 = job_task j2 /\
      exists arr1 arr2, arrives_at job_arrival j1 arr1 /\
                        arrives_at job_arrival j2 arr2 /\
                        arr1 < arr2.

    Definition exists_earlier_job (t: time) (jlow: Job) :=
      exists j0, earlier_job j0 jlow /\
                 (pending job_arrival job_cost num_cpus rate) sched j0 t.

    (* TODO: How do we avoid passing so many parameters? *)
    
End EarlierJobs.

End ScheduleOfSporadicTask.