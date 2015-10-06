Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs
               PlatformDefs WorkloadDefs SchedulabilityDefs PriorityDefs
               ResponseTimeDefs divround helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop div path tuple.

Module ResponseTimeAnalysis.

  Import Job SporadicTaskset Schedule Workload Schedulability ResponseTime Priority SporadicTaskArrival.

  Section Interference.

    (* Assume any job arrival sequence...*)
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    Context {arr_seq: arrival_sequence Job}.

    (* ... and any platform. *)
    Context {num_cpus: nat}.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    (* Consider any job j in a time interval [t1, t2), and ... *)
    Variable j: JobIn arr_seq.
    Variable t1 t2: time.

    (* recall the definition of backlogged (pending and not scheduled). *)
    Let job_is_backlogged (t: time) :=
      backlogged job_cost rate sched j t.

    (* We define the total interference incurred by job j during [t1, t2)
       as the cumulative time in which j is backlogged in this interval. *)
    Definition total_interference :=
      \sum_(t1 <= t < t2) job_is_backlogged t.

    Section TaskInterference.

      (* In order to define task interference, consider any task tsk. *)
      Variable tsk: sporadic_task.
    
      Definition schedules_job_of_tsk (cpu: processor num_cpus) (t: time) :=
        match (sched cpu t) with
          | Some j' => job_task j' == tsk
          | None => false
        end.

      (* We know that tsk is scheduled at time t if there exists a processor
         scheduling a job of tsk. *)
      Definition task_is_scheduled (t: time) :=
        [exists cpu in processor num_cpus, schedules_job_of_tsk cpu t].

      (* We define the total interference incurred by tsk during [t1, t2)
         as the cumulative time in which tsk is scheduled. *)
      Definition task_interference :=
        \sum_(t1 <= t < t2)
          (job_is_backlogged t && task_is_scheduled t).

      (* Note that this definition assumes that no multiple jobs of
         the same task execute in parallel (task precedence). *)
    End TaskInterference.

    Section BasicLemmas.

      (* Interference cannot be larger than the considered time window. *)
      Lemma total_interference_le_delta : total_interference <= t2 - t1.
      Proof.
        unfold total_interference.
        apply leq_trans with (n := \sum_(t1 <= t < t2) 1);
          first by apply leq_sum; ins; apply leq_b1.
        by rewrite big_const_nat iter_addn mul1n addn0 leqnn.
      Qed.

    End BasicLemmas.
    
    Section CorrespondenceWithService.

      (* Assume that jobs do not execute in parallel, ...*)
      Hypothesis no_parallelism:
        jobs_dont_execute_in_parallel sched.

      (* and that processors have unit speed. *)
      Hypothesis rate_equals_one :
        forall j cpu, rate j cpu = 1.

      (* Also assume that jobs only execute after they arrived
         and no longer than their execution costs. *)
      Hypothesis jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute sched.
      Hypothesis completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost rate sched.

      (* If job j had already arrived at time t1 and did not yet
         complete by time t2, ...*)
      Hypothesis job_has_arrived :
        has_arrived j t1.
      Hypothesis job_is_not_complete :
        ~~ completed job_cost rate sched j t2.

      (* then the service received by j during [t1, t2) equals
         the cumulative time in which it did not incur interference. *)
      Lemma complement_of_interf_equals_service :
        \sum_(t1 <= t < t2) service_at rate sched j t =
          t2 - t1 - total_interference.
      Proof.
        unfold completed, total_interference, job_is_backlogged,
               backlogged, service_during, pending.
        rename no_parallelism into NOPAR,
               rate_equals_one into RATE,
               jobs_must_arrive_to_execute into MUSTARRIVE,
               completed_jobs_dont_execute into COMP,
               job_is_not_complete into NOTCOMP.

        assert (SERVICE_ONE: forall j t, service_at rate sched j t <= 1).
          by ins; apply service_at_le_max_rate; ins; rewrite RATE.

        (* Reorder terms... *)  
        apply/eqP; rewrite subh4; first last.
        {  
          rewrite -[t2 - t1]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
          by apply leq_sum; ins; apply leq_b1.
        }
        {
          rewrite -[t2 - t1]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
          by apply leq_sum; ins; apply service_at_le_max_rate; ins; rewrite RATE.
        }
        apply/eqP.
        
        apply eq_trans with (y := \sum_(t1 <= t < t2)
                                    (1 - service_at rate sched j t));
          last first.
        {
          apply/eqP; rewrite <- eqn_add2r with (p := \sum_(t1 <= t < t2)
                                               service_at rate sched j t).
          rewrite subh1; last first.
            rewrite -[t2 - t1]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
            by apply leq_sum; ins; apply SERVICE_ONE.
          rewrite -addnBA // subnn addn0 -big_split /=.
          rewrite -[t2 - t1]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
          apply/eqP; apply eq_bigr; ins; rewrite subh1;
            [by rewrite -addnBA // subnn addn0 | by apply SERVICE_ONE].
        }
        rewrite big_nat_cond [\sum_(_ <= _ < _ | true)_]big_nat_cond.
        apply eq_bigr; intro t; rewrite andbT; move => /andP [GEt1 LTt2].
        destruct (~~ scheduled sched j t) eqn:SCHED; last first.
        {
          apply negbFE in SCHED; unfold scheduled in *.
          move: SCHED => /exists_inP SCHED; destruct SCHED as [cpu INcpu SCHEDcpu].
          rewrite andbF; apply/eqP.
          rewrite -(eqn_add2r (service_at rate sched j t)) add0n.
          rewrite subh1; last by ins; apply SERVICE_ONE.
          rewrite -addnBA // subnn addn0.
          rewrite eqn_leq; apply/andP; split; first by apply SERVICE_ONE.
          unfold service_at; rewrite big_mkcond /= (bigD1 cpu) // /= SCHEDcpu.
          by rewrite ltn_addr // RATE.
        }
        apply not_scheduled_no_service with (rate0 := rate) in SCHED.
        rewrite SCHED subn0 andbT; apply/eqP; rewrite eqb1.
        apply/andP; split; first by apply leq_trans with (n := t1).
        rewrite neq_ltn; apply/orP; left.
        apply leq_ltn_trans with (n := service rate sched j t2);
          first by apply service_monotonic, ltnW.
        rewrite ltn_neqAle; apply/andP; split;
           [by apply NOTCOMP | by apply COMP].
      Qed.
      
    End CorrespondenceWithService.

  End Interference.
  
  Section InterferenceBound.

    (* Let tsk \in ts be the task to be analyzed. *)
    Variable ts: sporadic_taskset.
    Let task_in_ts := 'I_(size ts).
    Local Coercion nth_task (idx: task_in_ts) := (tnth (in_tuple ts)) idx.
    Let indexed_ts := enum task_in_ts.
    
    Variable tsk: task_in_ts.

    (* Assume a known response-time bound for each interfering task ... *)
    Variable R_other: task_in_ts -> time.
    (* ... and an interval length delta. *)
    Variable delta: time.

    (* Based on the workload bound, ... *)
    Let workload_bound (tsk_other: task_in_ts) :=
      W tsk_other (R_other tsk_other) delta.
    
    (* Bertogna and Cirinei define the following interference bound
       for a task. *)
    Definition interference_bound (tsk_other: task_in_ts) :=
      minn (workload_bound tsk_other) (delta - (task_cost tsk) + 1).

    Section InterferenceFP.

      (* Assume an FP policy. *)
      Variable higher_eq_priority: fp_policy.

      (* Under FP scheduling, lower-priority tasks don't interfere. *)
      Let interference_caused_by (tsk_other: task_in_ts) :=
        if (higher_eq_priority tsk_other tsk) && (tsk_other != tsk) then
          interference_bound tsk_other
        else 0.
          
      (* The total interference incurred by tsk is thus bounded by: *)
      Definition total_interference_bound_fp :=
        \sum_(tsk_other <- indexed_ts)
           interference_caused_by tsk_other.
  
    End InterferenceFP.

    Section InterferenceJLFP.

      (* Under JLFP scheduling, all other tasks may cause interference. *)
      Let interference_caused_by (tsk_other: task_in_ts) :=
        if tsk_other != tsk then
          interference_bound tsk_other
        else 0.
      
      (* The total interference incurred by tsk is thus bounded by: *)
      Definition total_interference_bound_jlfp :=
        \sum_(tsk_other <- indexed_ts)
           interference_caused_by tsk_other.

    End InterferenceJLFP.

  End InterferenceBound.
  
  Section ResponseTimeBound.

    (* Assume any job arrival sequence... *)
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    Context {arr_seq: arrival_sequence Job}.

    (* ... in which jobs arrive sporadically and have valid parameters. *)
    Hypothesis H_sporadic_tasks: sporadic_task_model arr_seq job_task.
    Hypothesis H_valid_job_parameters:
      forall (j: JobIn arr_seq),
        (valid_sporadic_job job_cost job_deadline job_task) j.

    (* Consider any schedule such that...*)
    Variable num_cpus: nat.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    (* ...jobs do not execute before their arrival times nor longer
       than their execution costs. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost rate sched.

    (* Also assume that jobs do not execute in parallel, processors have
       unit speed, and that there exists at least one processor. *)
    Hypothesis H_no_parallelism:
      jobs_dont_execute_in_parallel sched.
    Hypothesis H_rate_equals_one :
      forall j cpu, rate j cpu = 1.
    Hypothesis H_at_least_one_cpu :
      num_cpus > 0.

    (* Assume that we have a task set where all tasks have valid
       parameters and restricted deadlines. *)
    Variable ts: sporadic_taskset.

    (* We add a coercion from task indices to their respective tasks.
       This removes a layer of indirection in the definitions. *)
    Let task_in_ts := 'I_(size ts).
    Local Coercion nth_task (idx: task_in_ts) := (tnth (in_tuple ts)) idx.
    Let indexed_ts := enum task_in_ts.

    Hypothesis H_valid_task_parameters: valid_sporadic_taskset ts.
    Hypothesis H_restricted_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    (* Next, consider some task tsk in the task set that is
       to be analyzed. *)
    Variable tsk: task_in_ts.
    (*Hypothesis task_in_ts: tsk \in ts.*)

    Let no_deadline_is_missed_by_tsk (tsk: task_in_ts) :=
      task_misses_no_deadline job_cost job_deadline job_task rate sched tsk.
    Let is_response_time_bound (tsk: task_in_ts) :=
      is_response_time_bound_of_task job_cost job_task tsk rate sched.

    (* Assume a known response-time bound for any interfering task *)
    Variable R_other: task_in_ts -> time.
    
    (* We derive the response-time bounds for FP and EDF scheduling
       separately. *)
    Section UnderFPScheduling.

      (* For FP scheduling, assume there exists a fixed task priority. *)
      Variable higher_eq_priority: fp_policy.

      (* We say that tsk can be interfered with by tsk_other if
         tsk_other is a different task from the task set that has
         higher or equal priority. *)
      Definition is_interfering_task (tsk_other: task_in_ts) :=
        higher_eq_priority tsk_other tsk && (tsk_other != tsk).

      (* Assume that for any interfering task, a response-time
         bound R_other is known. *)
      Hypothesis H_response_time_of_interfering_tasks_is_known:
        forall tsk_other,
          is_interfering_task tsk_other ->
          is_response_time_bound_of_task job_cost job_task tsk_other
                                         rate sched (R_other tsk_other).

      (* Assume that the response-time bounds are larger than task costs. *)
      Hypothesis R_other_ge_cost:
        forall (tsk_other: task_in_ts),
          R_other tsk_other >= task_cost tsk_other.
      
      (* Assume that no deadline is missed by any interfering task, i.e.,
         response-time bound R_other <= deadline. *)
      Hypothesis H_interfering_tasks_miss_no_deadlines:
        forall tsk_other,
          is_interfering_task tsk_other ->
          R_other tsk_other <= task_deadline tsk_other.

      (* Assume that the schedule satisfies the global scheduling
         invariant, i.e., if any job of tsk is backlogged, all
         the processors must be busy with jobs of equal or higher
         priority. *)
      Hypothesis H_global_scheduling_invariant:
        forall (j: JobIn arr_seq) (t: time),
          job_task j = tsk ->
          backlogged job_cost rate sched j t ->
          count
            (fun tsk_other : task_in_ts =>
               is_interfering_task tsk_other &&
               task_is_scheduled job_task sched tsk_other t) indexed_ts = num_cpus.

      (* Next, we define Bertogna and Cirinei's response-time bound recurrence *)
      
      (* Let R be any time. *)
      Variable R: time.
      
      (* Bertogna and Cirinei's response-time analysis states that
         if R is a fixed-point of the following recurrence, ... *)
      Hypothesis H_response_time_recurrence_holds :
        R = task_cost tsk +
            div_floor
              (total_interference_bound_fp ts tsk R_other R higher_eq_priority)
              num_cpus.

      (*..., and R is no larger than the deadline of tsk, ...*)
      Hypothesis H_response_time_no_larger_than_deadline:
        R <= task_deadline tsk.

      (* ..., then R bounds the response time of tsk in any schedule. *)
      Theorem bertogna_cirinei_response_time_bound_fp :
        is_response_time_bound tsk R.
      Proof.
        unfold is_response_time_bound, is_response_time_bound_of_task,
               job_has_completed_by, completed,
               completed_jobs_dont_execute,
               valid_sporadic_job in *.
        rename H_completed_jobs_dont_execute into COMP,
               H_response_time_recurrence_holds into REC,
               H_valid_job_parameters into PARAMS,
               H_valid_task_parameters into TASK_PARAMS,
               H_restricted_deadlines into RESTR,
               H_response_time_of_interfering_tasks_is_known into RESP,
               H_interfering_tasks_miss_no_deadlines into NOMISS,
               H_rate_equals_one into RATE,
               H_global_scheduling_invariant into INVARIANT.
        intros j JOBtsk.
        
        (* For simplicity, let x denote per-task interference under FP
           scheduling, and let X denote the total interference. *)
        set x := fun tsk_other =>
          if is_interfering_task tsk_other then
            task_interference job_cost job_task rate sched j
                     (job_arrival j) (job_arrival j + R) tsk_other
          else 0.
        set X := total_interference job_cost rate sched j (job_arrival j) (job_arrival j + R).

        (* Let's recall the workload bound under FP scheduling. *)
        set workload_bound := fun tsk_other =>
          if is_interfering_task tsk_other then
            W tsk_other (R_other tsk_other) R
          else 0.                      
        
        (* Now we start the proof. Assume by contradiction that job j
           is not complete at time (job_arrival j + R). *)
        destruct (completed job_cost rate sched j (job_arrival j + R)) eqn:COMPLETED;
          first by move: COMPLETED => /eqP COMPLETED; rewrite COMPLETED eq_refl.
        apply negbT in COMPLETED; exfalso.

        (* Since j has not completed, recall the time when it is not
           executing is the total interference. *)
        exploit (complement_of_interf_equals_service job_cost rate sched j (job_arrival j)
                                                     (job_arrival j + R));
          last intro EQinterf; ins; unfold has_arrived;
          first by apply leqnn.
        rewrite {2}[_ + R]addnC -addnBA // subnn addn0 in EQinterf.

        (* In order to derive a contradiction, we first show that
           the interference x_k of any task is no larger than the
           workload bound W_k. *)
        assert (WORKLOAD: forall tsk_k, x tsk_k <= workload_bound tsk_k).   
        {
          intros tsk_k; unfold x, workload_bound.
          destruct (is_interfering_task tsk_k) eqn:INk; last by ins.

          apply leq_trans with (n := workload job_task rate sched tsk_k
                                    (job_arrival j) (job_arrival j + R)).
          {
            unfold task_interference, workload.
            apply leq_sum; intros t _.
            rewrite -mulnb -[\sum_(_ < _) _]mul1n.
            apply leq_mul; first by apply leq_b1.
            destruct (task_is_scheduled job_task sched tsk_k t) eqn:SCHED;
              last by ins.
            unfold task_is_scheduled in SCHED.
            move: SCHED =>/exists_inP SCHED.
            destruct SCHED as [cpu _ HAScpu].
            rewrite -> bigD1 with (j := cpu); simpl; last by ins.
            apply ltn_addr.
            unfold service_of_task, schedules_job_of_tsk in *.
            by destruct (sched cpu t);[by rewrite HAScpu mul1n RATE|by ins].
          }       
          {
            apply workload_bounded_by_W with
               (job_cost := job_cost) (job_deadline := job_deadline); ins;
              [ by rewrite RATE
              | by apply TASK_PARAMS, mem_tnth
              | by apply RESTR, mem_tnth 
              | by red; red; ins; apply RESP |].
            red; red; move => j' /eqP JOBtsk' _;
            unfold job_misses_no_deadline.
            specialize (PARAMS j'); des.
            rewrite PARAMS1 JOBtsk'.
            apply completion_monotonic with (t := job_arrival j' + R_other tsk_k); ins;
              [by rewrite leq_add2l; apply NOMISS | by apply RESP].
          }
        }

        (* In the remaining of the proof, we show that the workload bound
           W_k is less than the task interference x (contradiction!).
           For that, we require a few auxiliary lemmas: *)

        (* 1) We show that the total interference X >= R - e_k + 1.
              Otherwise, job j would have completed on time. *)
        assert (INTERF: X >= R - task_cost tsk + 1).
        {
          unfold completed in COMPLETED.
          rewrite addn1.
          move: COMPLETED; rewrite neq_ltn; move => /orP COMPLETED; des;
            last first.
          {
            apply (leq_ltn_trans (COMP j (job_arrival j + R))) in COMPLETED.
            by rewrite ltnn in COMPLETED.
          }
          apply leq_trans with (n := R - service rate sched j (job_arrival j + R)); last first.
          {
            unfold service; rewrite service_before_arrival_eq_service_during; ins.
            rewrite EQinterf.
            rewrite subKn; first by ins.
            {
              unfold total_interference.
              rewrite -{1}[_ j]add0n big_addn addnC -addnBA // subnn addn0.
              rewrite -{2}[R]subn0 -[R-_]mul1n -[1*_]addn0 -iter_addn.
              by rewrite -big_const_nat leq_sum //; ins; apply leq_b1.
            }
          }
          {
            apply ltn_sub2l; last first.
            {
              apply leq_trans with (n := job_cost j); first by ins.
              by rewrite -JOBtsk; specialize (PARAMS j); des; apply PARAMS0.
            }
            apply leq_trans with (n := job_cost j); first by ins.
            apply leq_trans with (n := task_cost tsk);
              first by rewrite -JOBtsk; specialize (PARAMS j); des; apply PARAMS0.
            by rewrite REC; apply leq_addr.
          }
        }

        (* 2) Then, we prove that the sum of the interference of each
           task is equal to the total interference multiplied by the
           number of processors. This holds because interference only
           occurs when all processors are busy with some task. *)
        assert(ALLBUSY: \sum_(tsk_k <- indexed_ts) x tsk_k = X * num_cpus).
        {
          unfold x, X, total_interference, task_interference.
          rewrite -big_mkcond -exchange_big big_distrl /=.
          apply eq_big_nat; move => t LTt.
          destruct (backlogged job_cost rate sched j t) eqn:BACK;
            last by rewrite (eq_bigr (fun i => 0));
              [by rewrite big_const_seq iter_addn mul0n addn0 mul0n|by ins].
          rewrite big_mkcond mul1n /=.
          rewrite (eq_bigr (fun i =>
                              (if is_interfering_task i &&
                                  task_is_scheduled job_task sched i t then 1 else 0)));
            last by ins; destruct (is_interfering_task i); rewrite ?andTb ?andFb; ins.
          by rewrite -big_mkcond sum1_count; apply (INVARIANT j).
        }

        (* 3) Next, we prove the auxiliary lemma from the paper. *)
        assert (MINSERV: \sum_(tsk_k <- indexed_ts) x tsk_k >=
                         (R - task_cost tsk + 1) * num_cpus ->
               \sum_(tsk_k <- indexed_ts) minn (x tsk_k) (R - task_cost tsk + 1) >=
               (R - task_cost tsk + 1) * num_cpus).
        {
          intro SUMLESS.
          set more_interf := fun tsk_k => x tsk_k >= R - task_cost tsk + 1.
          rewrite [\sum_(_ <- _) minn _ _](bigID more_interf) /=.
          unfold more_interf, minn.
          rewrite [\sum_(_ <- _ | R - _ + _ <= _)_](eq_bigr (fun i => R - task_cost tsk + 1));
            last first.
          {
            intros i COND; rewrite leqNgt in COND.
            destruct (R - task_cost tsk + 1 > x i); ins.
          }
          rewrite [\sum_(_ <- _ | ~~_)_](eq_big (fun i => x i < R - task_cost tsk + 1)
                                                (fun i => x i));
            [| by red; ins; rewrite ltnNge
             | by intros i COND; rewrite -ltnNge in COND; rewrite COND].

          (* Case 1 |A| = 0 *)
          destruct (~~ has (fun i => R - task_cost tsk + 1 <= x i) indexed_ts) eqn:HASa.
          {
            rewrite [\sum_(_ <- _ | _ <= _) _]big_hasC; last by apply HASa.
            rewrite big_seq_cond; move: HASa => /hasPn HASa.
            rewrite add0n (eq_bigl (fun i => (i \in indexed_ts) && true));
              last by red; intros tsk_k; destruct (tsk_k \in indexed_ts) eqn:INk;
                [by rewrite andTb ltnNge; apply HASa | by rewrite andFb].
            by rewrite -big_seq_cond. 
          } apply negbFE in HASa.
          
          set cardA := count (fun i => R - task_cost tsk + 1 <= x i) indexed_ts.
          destruct (cardA >= num_cpus) eqn:CARD.
          {
            apply leq_trans with ((R - task_cost tsk + 1) * cardA);
              first by rewrite leq_mul2l; apply/orP; right.
            unfold cardA; rewrite -sum1_count big_distrr /=.
            rewrite -[\sum_(_ <- _ | _) _]addn0.
            by apply leq_add; [by apply leq_sum; ins; rewrite muln1|by ins].
          } apply negbT in CARD; rewrite -ltnNge in CARD.

          assert (GEsum: \sum_(i <- indexed_ts | x i < R - task_cost tsk + 1) x i >=
                           (R - task_cost tsk + 1) * (num_cpus - cardA)).
          {
            set some_interference_A := fun t =>
              backlogged job_cost rate sched j t &&
              has (fun tsk_k => (is_interfering_task tsk_k &&
                                 ((x tsk_k) >= R - task_cost tsk + 1) &&
                                 task_is_scheduled job_task sched tsk_k t)) indexed_ts.      
            set total_interference_B := fun t =>
              backlogged job_cost rate sched j t *
              count (fun tsk_k =>
                is_interfering_task tsk_k &&
                ((x tsk_k) < R - task_cost tsk + 1) &&
                task_is_scheduled job_task sched tsk_k t) indexed_ts.

            apply leq_trans with ((\sum_(job_arrival j <= t < job_arrival j + R)
                                      some_interference_A t) * (num_cpus - cardA)).
            {
              rewrite leq_mul2r; apply/orP; right.
              move: HASa => /hasP HASa; destruct HASa as [tsk_a INa LEa].
              apply leq_trans with (n := x tsk_a); first by apply LEa.
              unfold x, task_interference, some_interference_A.
              destruct (is_interfering_task tsk_a) eqn:INTERFa; last by ins.
              apply leq_sum; ins.
              destruct (backlogged job_cost rate sched j i);
                [rewrite 2!andTb | by ins].
              destruct (task_is_scheduled job_task sched (nth_task tsk_a) i) eqn:SCHEDa;
                [apply eq_leq; symmetry | by ins].
              apply/eqP; rewrite eqb1.
              apply/hasP; exists tsk_a; first by ins.
              apply/andP; split; last by ins.
              by apply/andP; split; ins.
            }
            apply leq_trans with (\sum_(job_arrival j <= t < job_arrival j + R)
                                     total_interference_B t).
            {
              rewrite big_distrl /=.
              apply leq_sum; intros t _.
              unfold some_interference_A, total_interference_B. 
              destruct (backlogged job_cost rate sched j t) eqn:BACK;
                [rewrite andTb mul1n | by ins].
              destruct (has (fun tsk_k : task_in_ts =>
                       is_interfering_task tsk_k &&
                       (R - task_cost tsk + 1 <= x tsk_k) &&
                       task_is_scheduled job_task sched tsk_k t) indexed_ts) eqn:HAS;
                last by ins.
              rewrite mul1n; move: HAS => /hasP HAS.
              destruct HAS as [tsk_k INk H].
              move: H => /andP [/andP [INTERFk LEk] SCHEDk].
              
              exploit INVARIANT;
                [by apply JOBtsk | by apply BACK | intro COUNT].

              unfold cardA.
              set interfering_tasks_at_t :=
                [seq tsk_k <- indexed_ts | is_interfering_task tsk_k &&
                                  task_is_scheduled job_task sched tsk_k t].

              rewrite -(count_filter (fun i => true)) in COUNT.
              fold interfering_tasks_at_t in COUNT.
              rewrite count_predT in COUNT.
              apply leq_trans with (n := num_cpus -
                                      count (fun i => is_interfering_task i &&
                                                    (x i >= R -  task_cost tsk + 1) &&
                                                    task_is_scheduled job_task sched i t) indexed_ts).
              {
                apply leq_sub2l.
                rewrite -2!sum1_count big_mkcond /=.
                rewrite [\sum_(_ <- _ | _ <= _)_]big_mkcond /=.
                apply leq_sum; intros i _.
                unfold x; destruct (is_interfering_task i);
                  [rewrite andTb | by rewrite 2!andFb].
                destruct (task_is_scheduled job_task sched i t);
                  [by rewrite andbT | by rewrite andbF].
              }

              rewrite leq_subLR.
              rewrite -count_predUI.
              apply leq_trans with (n :=
                count (predU (fun i : task_in_ts =>
                                is_interfering_task i &&
                                (R - task_cost tsk + 1 <= x i) &&
                                task_is_scheduled job_task sched i t)
                             (fun tsk_k0 : task_in_ts =>
                                is_interfering_task tsk_k0 &&
                                (x tsk_k0 < R - task_cost tsk + 1) &&
                                task_is_scheduled job_task sched tsk_k0 t))
                      indexed_ts); last by apply leq_addr.
              apply leq_trans with (n := size interfering_tasks_at_t);
                first by rewrite COUNT.
              unfold interfering_tasks_at_t.
              rewrite -count_predT count_filter.
              rewrite leq_eqVlt; apply/orP; left; apply/eqP.
              apply eq_count; red; simpl.
              intros i.
              destruct (is_interfering_task i),
                       (task_is_scheduled job_task sched i t);
                rewrite 3?andTb ?andFb ?andbF ?andbT /=; try ins.
              by rewrite leqNgt orNb. 
            }
            {
              unfold x at 2, task_interference.
              rewrite [\sum_(i <- indexed_ts | _) _](eq_bigr
                (fun i => \sum_(job_arrival j <= t < job_arrival j + R)
                             is_interfering_task i &&
                             backlogged job_cost rate sched j t &&
                             task_is_scheduled job_task sched i t));
                last first.
              {
                ins; destruct (is_interfering_task i);
                  first by apply eq_bigr; ins.
                by rewrite (eq_bigr (fun i => 0));
                  [by rewrite big_const_nat iter_addn mul0n addn0 | by ins].
              }
              {
                rewrite exchange_big /=; apply leq_sum; intros t _.
                unfold total_interference_B.
                destruct (backlogged job_cost rate sched j t); last by ins.
                rewrite mul1n -sum1_count.
                rewrite big_mkcond [\sum_(i <- indexed_ts | _ < _) _]big_mkcond.
                by apply leq_sum; ins; destruct (x i<R - task_cost tsk + 1);
                  [by ins | by rewrite andbF andFb].
              }
            }
          }
          
          rewrite big_const_seq iter_addn addn0; fold cardA.
          apply leq_trans with (n := (R-task_cost tsk+1)*cardA +
                                     (R-task_cost tsk+1)*(num_cpus-cardA));
            last by rewrite leq_add2l.
          by rewrite -mulnDr subnKC //; apply ltnW.
        }

        (* 4) Now, we prove that the Bertogna's interference bound
              is not enough to cover sum of the "minimum" term over
              all tasks (artifact of the proof by contradiction). *)
        assert (SUM: \sum_(tsk_k <- indexed_ts)
                        minn (x tsk_k) (R - task_cost tsk + 1)
                     > total_interference_bound_fp ts tsk R_other
                                                   R higher_eq_priority).
        {
          apply ltn_div_trunc with (d := num_cpus);
            first by apply H_at_least_one_cpu.
          rewrite -(ltn_add2l (task_cost tsk)) -REC.
          rewrite -addn1 -leq_subLR.
          rewrite -[R + 1 - _]subh1; last by rewrite REC; apply leq_addr.
          rewrite leq_divRL; last by apply H_at_least_one_cpu.
          apply MINSERV.
          apply leq_trans with (n := X * num_cpus); last by rewrite ALLBUSY.
          by rewrite leq_mul2r; apply/orP; right; apply INTERF.
        }

        (* 5) This implies that there exists a task such that
              min (x_k, R - e_i + 1) > min (W_k, R - e_i + 1). *)
        assert (EX: has (fun tsk_k : task_in_ts =>
                           minn (x tsk_k) (R - task_cost tsk + 1) >
                             minn (workload_bound tsk_k) (R - task_cost tsk + 1))
                        indexed_ts).
        {
          apply/negP; unfold not; intro NOTHAS.
          move: NOTHAS => /negP /hasPn NOTHAS.
          rewrite -[_ < _]negbK in SUM.
          move: SUM => /negP SUM; apply SUM; rewrite -leqNgt.
          unfold total_interference_bound_fp.
          rewrite [\sum_(_ <- _) if _ then _ else _]big_seq_cond.
          rewrite [\sum_(_ <- _ | _ && _)_]big_mkcond /=.
          apply leq_sum; intros tsk_k _.
          unfold x, workload_bound, is_interfering_task, workload_bound in *.
          specialize (NOTHAS tsk_k).
          fold (nth_task tsk) (nth_task tsk_k) in *.
          destruct (tsk_k \in indexed_ts) eqn:IN,
                   (higher_eq_priority (nth_task tsk_k) tsk),
                   (tsk_k != tsk);
          rewrite ?andFb ?andTb ?andbT ?min0n IN; try apply leqnn;
            last by rewrite mem_enum in IN.
          specialize (NOTHAS IN).
          rewrite 3?andbT in NOTHAS.
          unfold interference_bound.
          by rewrite leqNgt; apply NOTHAS.
        }

        (* For this particular task, we show that x_k > W_k.
           This contradicts the previous claim. *)
        move: EX => /hasP EX; destruct EX as [tsk_k INk LTmin].
        unfold task_interference, minn at 1 in LTmin.
        destruct (workload_bound tsk_k < R - task_cost tsk + 1) eqn:MIN;
          [clear MIN | by move: LTmin; rewrite leq_min ltnn andbF].
        move: LTmin; rewrite leq_min; move => /andP LTmin; des.
        apply (leq_ltn_trans (WORKLOAD tsk_k)) in LTmin.
        by rewrite ltnn in LTmin.
      Qed.

    End UnderFPScheduling.

    Section UnderJLFPScheduling.

      (* Bertogna and Cirinei's response-time bound recurrence *)
      Definition response_time_recurrence_jlfp R :=
        R <= task_cost tsk + div_floor
                             (total_interference_bound_jlfp ts tsk R_other R)
                             num_cpus.

      Variable R: time.

      Hypothesis response_time_recurrence_holds:
        response_time_recurrence_jlfp R.

      Hypothesis response_time_no_larger_than_deadline:
        R <= task_deadline tsk.

      (* to be completed... *)
      
    End UnderJLFPScheduling.
    
  End ResponseTimeBound.

  Section ResponseTimeIterationFP.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.

    Variable num_cpus: nat.
    Variable higher_eq_priority: fp_policy.
    Hypothesis H_valid_policy: valid_fp_policy higher_eq_priority.

    (* To access tasks more easily, we use indices {0,...,|ts|-1}. *)
    Variable ts: sporadic_taskset.
    Let task_in_ts := 'I_(size ts).
    Let indexed_ts := enum (task_in_ts).
    
    (* Then, we define a coercion from indices to tasks so that
       we can access the task properties directly. *)
    Local Coercion nth_task (idx: task_in_ts) := (tnth (in_tuple ts)) idx.

    (* Next we define the fixed-point iteration for computing
       Bertogna's response-time bound. *)

    (* First, we define a known bound on the maximum number of steps.
       Note that "deadline + 1" is pessimistic, but we don't care about
       the precise runtime complexity here. *)
    Definition max_steps (idx: task_in_ts) := task_deadline idx + 1.

    (* Let 'idx' be the index of the task to be analyzed.
       Given a vector of size 'idx' containing known response-time bounds
       for the higher-priority tasks, we compute the response-time bound
       of 'idx' by applying the following function "step" times. *)
    Definition rt_rec (idx: task_in_ts)
                      (R_prev: idx.-tuple nat) (step: nat) :=
      iter step
           (fun t => task_cost idx +
                       div_floor
                         (total_interference_bound_fp
                           ts idx (ext_tuple_to_fun_index R_prev) t
                           higher_eq_priority)
                         num_cpus)
           (task_cost idx).

    (* In order to obtain the vector of size 'idx' containing response-time
       bounds for the higher-priority tasks, we apply the same recursion
       rt_rec that we just defined (max_steps times for each task). *)
    Program Fixpoint R_hp' (idx: nat) (P: idx < size ts) : idx.-tuple nat :=
      match idx with
        | 0 => nil_tuple _ (* Task 0 has no higher-priority tasks *)
        | S k => rcons_tuple
                   (R_hp' k _) (* [previous Rs]*)
                   (rt_rec (@Ordinal _ k _) (* + [current R]*)
                           (R_hp' k _)
                           (max_steps (@Ordinal _ k _)))
      end.
    Next Obligation. by apply ltSnm. Qed.
    Next Obligation. by apply ltSnm. Qed.
    Definition R_hp (idx: task_in_ts) := R_hp' idx (ltn_ord idx).
    
    (* The response-time bound R of a task idx is computed by calling
       rt_rec with the vector R_hp of higher-priority tasks' bounds. *)
    Definition R (idx: task_in_ts) :=
      rt_rec idx (R_hp idx) (max_steps idx).
    
    (* To conclude, we say that the schedulability test returns true
       iff for every task i: 0, ..., |ts|-1, R tsk_i <= d_i *)
    Definition fp_schedulability_test :=
      all (fun tsk_i => R tsk_i <= task_deadline tsk_i) indexed_ts.

    Section AuxiliaryLemmas.

      (* First, we prove that R is no less than the cost of the task.
         This is required since the formulas use the workload bound W. *)
      Lemma R_ge_cost:
        forall (tsk: task_in_ts), R tsk >= task_cost tsk.
      Proof.
        intros tsk.
        unfold R, rt_rec.
        destruct (max_steps tsk); first by apply leqnn.
        by rewrite iterS; apply leq_addr.
      Qed.
      
      (* Next we establish the equivalence between computing R directly
         and accessing an R that we previously stored in the vector. *)
      Lemma rhp_eq_R:
        forall (tsk i: task_in_ts) (LT: i < tsk),
          ext_tuple_to_fun_index (R_hp tsk) i = R i.
      Proof.
        intros tsk i LT.
        destruct i as [i Hi].
        unfold ext_tuple_to_fun_index; des_eqrefl2;
          [clear LT | by rewrite EQ in LT].
        
      Admitted.

    End AuxiliaryLemmas.
    
    Section Proof.

      (* Assume that higher_eq_priority is an order relation. *)
      Hypothesis H_reflexive: reflexive higher_eq_priority.
      Hypothesis H_transitive: transitive higher_eq_priority.
      Hypothesis H_unique_priorities:
        antisymmetric_over_seq higher_eq_priority ts.

      (* Assume the task set has no duplicates, ... *)
      Hypothesis H_ts_is_a_set: uniq ts.

      (* ...all tasks have valid parameters, ... *)
      Hypothesis H_valid_task_parameters: valid_sporadic_taskset ts.

      (* ...restricted deadlines, ...*)
      Hypothesis H_restricted_deadlines:
        forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

      (* ...and tasks are ordered by decreasing priorities. *)
      Hypothesis H_sorted_ts: sorted higher_eq_priority ts.

      (* Next, consider any arrival sequence such that...*)
      Context {arr_seq: arrival_sequence Job}.

     (* ...all jobs come from task set ts, ...*)
      Hypothesis H_all_jobs_from_taskset:
        forall (j: JobIn arr_seq), job_task j \in ts.
      
      (* ...they have valid parameters,...*)
      Hypothesis H_valid_job_parameters:
        forall (j: JobIn arr_seq),
          valid_sporadic_job job_cost job_deadline job_task j.
      
      (* ... and satisfy the sporadic task model.*)
      Hypothesis H_sporadic_tasks: sporadic_task_model arr_seq job_task.
      
      (* Then, consider any platform with at least one CPU and unit
         unit execution rate, where...*)
      Variable rate: Job -> processor num_cpus -> nat.
      Variable sched: schedule num_cpus arr_seq.
      Hypothesis H_at_least_one_cpu :
        num_cpus > 0.
      Hypothesis H_rate_equals_one :
        forall j cpu, rate j cpu = 1.

      (* ...jobs only execute after they arrived and no longer
         than their execution costs,... *)
      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute sched.
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost rate sched.

      (* ...and do not execute in parallel. *)
      Hypothesis H_no_parallelism:
        jobs_dont_execute_in_parallel sched.

      (* Assume the platform satisfies the global scheduling
         invariant. *)
      Hypothesis H_global_scheduling_invariant:
        forall (tsk: task_in_ts) (j: JobIn arr_seq) (t: time),
          job_task j = tsk ->
          backlogged job_cost rate sched j t ->
          count
            (fun tsk_other : task_in_ts =>
               is_interfering_task ts tsk higher_eq_priority tsk_other &&
               task_is_scheduled job_task sched tsk_other t) indexed_ts = num_cpus.

      Definition no_deadline_missed_by (tsk: sporadic_task) :=
        task_misses_no_deadline job_cost job_deadline job_task
                                rate sched tsk.

      
      (* Now we present the proofs of termination and correctness of
         the schedulability test. *)
      
      (*  To prove convergence of R, we first show convergence of rt_rec. *)
      Lemma rt_rec_converges:
        forall (tsk: task_in_ts),
          rt_rec tsk (R_hp tsk) (max_steps tsk) <= task_deadline tsk ->
          rt_rec tsk (R_hp tsk) (max_steps tsk) =
            rt_rec tsk (R_hp tsk) (max_steps tsk).+1.
      Proof.
        rename H_valid_task_parameters into TASKPARAMS.
        unfold valid_sporadic_taskset, valid_sporadic_task in *.

        (* To simplify, let's call the function f.*)
        intros tsk LE; set (f := rt_rec tsk (R_hp tsk)); fold f in LE.

        (* First prove that f is monotonic.*)
        assert (MON: forall x1 x2, x1 <= x2 -> f x1 <= f x2).
        {
          intros x1 x2 LEx; unfold f, rt_rec.
          apply fun_mon_iter_mon; [by ins | by ins; apply leq_addr |].
          clear LEx x1 x2; intros x1 x2 LEx.
          
          unfold div_floor, total_interference_bound_fp.
          rewrite leq_add2l leq_div2r // leq_sum //; intros i _; simpl in i.
          unfold interference_bound; fold (nth_task i) (nth_task tsk) in *; fold task_in_ts in i.
          destruct (higher_eq_priority (nth_task i) (nth_task tsk) && (i != tsk)) eqn:HP; last by ins.
          rewrite leq_min; apply/andP; split.
          {
            apply leq_trans with (n := W i (ext_tuple_to_fun_index (R_hp tsk) i) x1);
              first by apply geq_minl.            
            exploit (TASKPARAMS (nth_task i));
              [by rewrite mem_nth | intro PARAMS; des].
            apply W_monotonic; try (by ins).
            {
              move: HP => /andP HP; des.
              assert (LTi: i < tsk).
              {
                exploit (leq_ij_implies_before_ij ts higher_eq_priority);
                  try by ins; apply HP.
                by intros LEi; rewrite ltn_neqAle; apply/andP; split.
              } clear HP0.
              rewrite rhp_eq_R; last by apply LTi.
              by apply R_ge_cost.
            }
          }
          {
            apply leq_trans with (n := x1 - task_cost tsk + 1);
              first by apply geq_minr.
            by rewrite leq_add2r leq_sub2r //.
          }
        }

        (* Either f converges by the deadline or not. *)
        unfold max_steps in *; rewrite -> addn1 in *.
        destruct ([exists k in 'I_(task_deadline tsk).+1,
                     f k == f k.+1]) eqn:EX.
        {
          move: EX => /exists_inP EX; destruct EX as [k _ ITERk].
          move: ITERk => /eqP ITERk.
          unfold f, rt_rec.
          by apply iter_fix with (k := k);
            [by ins | by apply ltnW, ltn_ord].
        }
        apply negbT in EX; rewrite negb_exists_in in EX.
        move: EX => /forall_inP EX.
        assert (GROWS: forall k: 'I_(task_deadline tsk).+1,
                         f k < f k.+1).
        {
          intros k; rewrite ltn_neqAle; apply/andP; split; first by apply EX.
          apply MON, leqnSn.
        }

        (* If it doesn't converge, then it becomes larger than the deadline.
           But initialy we assumed otherwise. Contradiction! *)
        assert (BY1: f (task_deadline tsk).+1 > task_deadline tsk).
        {
          clear MON LE EX.
          induction (task_deadline tsk).+1; first by ins.
          apply leq_ltn_trans with (n := f n);
            last by apply (GROWS (Ordinal (ltnSn n))).
          apply IHn; intros k.
          by apply (GROWS (widen_ord (leqnSn n) k)).
        }
        by apply leq_ltn_trans with (m := f (task_deadline tsk).+1) in BY1;
          [by rewrite ltnn in BY1 | by ins].
      Qed.

      (* Next we show that for any task, R converges. *)
      Theorem R_converges:
        forall (tsk: task_in_ts),
          R tsk <= task_deadline tsk ->
          R tsk = task_cost tsk +
                  div_floor
                    (total_interference_bound_fp ts tsk R
                    (R tsk) higher_eq_priority)
                  num_cpus.
      Proof.
        unfold valid_sporadic_taskset, valid_sporadic_task in *; intros tsk LE.
        unfold R at 1; rewrite rt_rec_converges; last by apply LE.
        unfold rt_rec at 1; rewrite iterS.

        (* The proof follows trivially since rt_rec converges.
            However, to express R in terms of rt_rec, we need to
            unfold the formula multiple times, until we reach
            (rt_rec of some high-priority task). *) 
        f_equal; f_equal.
        unfold total_interference_bound_fp.
        apply eq_bigr; intros i _; simpl in i.
        destruct (higher_eq_priority
                    (tnth (in_tuple ts) i) (tnth (in_tuple ts) tsk) 
                                     && (i != tsk)) eqn:HP; last by ins.
        move: HP => /andP [HP NEQ].
        assert (LTi: i < tsk).
        {
           exploit (leq_ij_implies_before_ij ts higher_eq_priority);
             try by ins; apply HP.
           by intros LEi; rewrite ltn_neqAle; apply/andP; split.
        } clear HP NEQ.
        unfold interference_bound; f_equal.
        by unfold W; repeat f_equal; rewrite rhp_eq_R.
      Qed.

      (* Finally, we show that if the schedulability test suceeds, ...*)
      Hypothesis H_test_passes: fp_schedulability_test.

      (*..., then no task misses its deadline. *)
      Theorem taskset_schedulable_by_fp_rta :
        forall (tsk: task_in_ts), no_deadline_missed_by tsk.
      Proof.
        unfold no_deadline_missed_by, task_misses_no_deadline,
               job_misses_no_deadline, completed,
               fp_schedulability_test,
               valid_sporadic_job in *.
        rename H_valid_job_parameters into JOBPARAMS,
               H_valid_task_parameters into TASKPARAMS,
               H_restricted_deadlines into RESTR,
               H_completed_jobs_dont_execute into COMP,
               H_jobs_must_arrive_to_execute into MUSTARRIVE,
               H_global_scheduling_invariant into INVARIANT,
               H_valid_policy into VALIDhp,
               H_sorted_ts into SORT,
               H_unique_priorities into UNIQ,
               H_all_jobs_from_taskset into ALLJOBS,
               H_test_passes into TEST.
      
        move: SORT TEST => SORT /allP TEST.
        move => tsk j /eqP JOBtsk.
      
        rewrite eqn_leq; apply/andP; split;
          first by apply service_interval_le_cost.
        apply leq_trans with (n := service rate sched j (job_arrival j + R tsk)); last first.
        {
          apply service_monotonic; rewrite leq_add2l.
          specialize (JOBPARAMS j); des; rewrite JOBPARAMS1 JOBtsk.
          by apply TEST, mem_enum.
        }
        rewrite leq_eqVlt; apply/orP; left; rewrite eq_sym.

        generalize dependent job_cost.
        generalize dependent j.
        destruct tsk as [tsk_i LTi].

        induction tsk_i as [|i IH] using strong_ind.
        {
          (* Base case: no higher-priority tasks *)
          unfold sorted in SORT.
          intros j JOBtsk job_cost' JOBPARAMS COMP INVARIANT.

          set tsk0 := Ordinal (n:=size ts) (m:=0) LTi.
          have BOUND := bertogna_cirinei_response_time_bound_fp.
          unfold is_response_time_bound_of_task,
            job_has_completed_by, completed in BOUND.
          apply BOUND with (job_deadline := job_deadline) (ts := ts)
                           (job_task := job_task) (tsk := tsk0)
                           (R_other := R) (higher_eq_priority := higher_eq_priority);
            try (by ins); clear BOUND; last first.
          by apply R_converges, TEST, mem_enum.
          by ins; apply INVARIANT with (j := j0); ins.
          by ins; apply TEST, mem_enum.
          by ins; apply R_ge_cost. 
          {
            intros tsk_other INTERF.
            unfold is_interfering_task in INTERF.
            move: INTERF => /andP INTERF; des.
            assert (LE: tsk_other < tsk0).
            {
              rewrite ltn_neqAle; apply/andP; split; first by ins.
              by apply leq_ij_implies_before_ij with (leT := higher_eq_priority); try red; ins.
            }
            by rewrite ltn0 in LE. 
          }
        }
        {
          (* Inductive Step *)
          intros j JOBtsk job_cost' JOBPARAMS COMP INVARIANT.
          set tsk_i' := Ordinal (n:=size ts) (m:=i.+1) LTi.
          have BOUND := bertogna_cirinei_response_time_bound_fp.
          unfold is_response_time_bound_of_task,
            job_has_completed_by, completed in BOUND.
          apply BOUND with (job_deadline := job_deadline) (ts := ts)
                      (job_task := job_task) (tsk := tsk_i') (R_other := R)
                      (higher_eq_priority := higher_eq_priority);
            try (by ins); clear BOUND; last first.
          by apply R_converges, TEST, mem_enum.
          by ins; apply INVARIANT with (j := j0); ins.  
          by ins; apply TEST, mem_enum.
          by ins; apply R_ge_cost.
          {
            intros tsk_other INTERF j' JOBtsk'.
            move: INTERF => /andP INTERF; des.
            assert (HP: tsk_other < tsk_i').
            {
              rewrite ltn_neqAle; apply/andP; split; first by ins.
              by apply leq_ij_implies_before_ij with (leT := higher_eq_priority); try red; ins.
            }
            assert (LT: tsk_other < size ts).
              by apply ltn_trans with (n := tsk_i'); [by apply HP | by apply LTi].
            specialize (IH tsk_other HP LT j').
            exploit IH; last (clear IH; intro IH).
              by rewrite JOBtsk'; unfold nth_task; f_equal; apply ord_inj.
              by instantiate (1 := job_cost'); apply JOBPARAMS.
              by apply COMP.
              by apply INVARIANT.
              {
                move: IH => /eqP IH; rewrite -IH; apply/eqP.
                by repeat f_equal; apply ord_inj; ins.
              }
          }
        }
      Qed.

    End Proof.

  End ResponseTimeIterationFP.

End ResponseTimeAnalysis.