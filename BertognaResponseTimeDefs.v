Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs
               PlatformDefs WorkloadDefs SchedulabilityDefs PriorityDefs
               ResponseTimeDefs divround helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop div.

Module ResponseTimeAnalysis.

  Import Job SporadicTaskset Schedule Workload Schedulability ResponseTime Priority SporadicTaskArrival.

  Section TaskInterference.

    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    Context {arr_seq: arrival_sequence Job}.

    Context {num_cpus: nat}.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    Variable j: JobIn arr_seq.
    Variable t1 delta: time.

    (*Definition total_interference :=
      delta - service_during rate sched j t1 (t1 + delta).*)

    Variable tsk: sporadic_task.
    
    Definition job_is_backlogged (t: time) :=
      backlogged job_cost rate sched j t.

    Definition has_job_of_tsk (cpu: processor num_cpus) (t: time) :=
      match (sched cpu t) with
        | Some j' => job_task j' == tsk
        | None => false
      end.
    
    Definition tsk_is_scheduled (t: time) :=
      [exists cpu in processor num_cpus, has_job_of_tsk cpu t].
    
    Definition task_interference :=
      \sum_(t1 <= t < t1 + delta)
        (job_is_backlogged t && tsk_is_scheduled t).

  End TaskInterference.
  
  Section InterferenceBound.

    (* Let tsk \in ts be the task to be analyzed. *)
    Variable ts: sporadic_taskset.
    Variable tsk: sporadic_task.

    (* Assume a known response-time bound for each interfering task ... *)
    Variable R_other: sporadic_task -> time.
    (* ... and an interval length delta. *)
    Variable delta: time.

    (* Based on Bertogna and Cirinei's workload bound, ... *)
    Definition workload_bound (tsk_other: sporadic_task) :=
      W tsk_other (R_other tsk_other) delta.
    
    (* ... we define interference bounds for FP and JLFP scheduling. *)
    Definition interference_bound (tsk_other: sporadic_task) :=
      minn (workload_bound tsk_other) (delta - (task_cost tsk) + 1).

    Section InterferenceFP.

      (* Assume an FP policy. *)
      Variable higher_eq_priority: fp_policy.

      (* Under FP scheduling, lower-priority tasks do not cause interference. *)
      Let interference_caused_by (tsk_other: sporadic_task) :=
        if (higher_eq_priority tsk_other tsk) && (tsk_other != tsk) then
          interference_bound tsk_other
        else 0.
          
      (* The total interference incurred by tsk is thus bounded by: *)
      Definition total_interference_fp :=
        \sum_(tsk_other <- ts)
           interference_caused_by tsk_other.
  
    End InterferenceFP.

    Section InterferenceJLFP.

      (* Under JLFP scheduling, all the other tasks may cause interference. *)
      Let interference_caused_by (tsk_other: sporadic_task) :=
        if tsk_other != tsk then
          interference_bound tsk_other
        else 0.
      
      (* The total interference incurred by tsk is thus bounded by: *)
      Definition total_interference_jlfp :=
        \sum_(tsk_other <- ts)
           interference_caused_by tsk_other.

    End InterferenceJLFP.

  End InterferenceBound.
  
  Section ResponseTimeBound.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    
    Context {arr_seq: arrival_sequence Job}.

    Hypothesis sporadic_tasks: sporadic_task_model arr_seq job_task.
    
    Variable num_cpus: nat.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost rate sched.

    Hypothesis H_no_parallelism:
      jobs_dont_execute_in_parallel sched.
    Hypothesis H_rate_equals_one :
      forall j cpu, rate j cpu = 1.
    
    Variable ts: sporadic_taskset.
    Hypothesis H_valid_task_parameters: valid_sporadic_taskset ts.
    Hypothesis H_valid_job_parameters:
      forall (j: JobIn arr_seq),
        (valid_sporadic_task_job job_cost job_deadline job_task) j.

    Hypothesis H_restricted_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.
    
    Variable tsk: sporadic_task.
    Hypothesis task_in_ts: tsk \in ts.

    Definition no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task rate sched tsk.

    Definition is_response_time_bound (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_cost job_task tsk rate sched.
    
    Variable R_other: sporadic_task -> time.

    Section UnderFPScheduling.

      Variable higher_eq_priority: fp_policy.

      Definition is_interfering_task (tsk_other: sporadic_task) :=
        tsk_other \in ts /\
        tsk_other != tsk /\
        higher_eq_priority tsk_other tsk.

      Hypothesis H_response_time_of_interfering_tasks_is_known:
        forall tsk_other job_cost,
          is_interfering_task tsk_other ->
          is_response_time_bound_of_task job_cost job_task tsk_other rate sched (R_other tsk_other).

      Hypothesis H_interfering_tasks_miss_no_deadlines:
        forall tsk_other,
          is_interfering_task tsk_other ->
          task_misses_no_deadline job_cost job_deadline job_task rate sched tsk_other.

      (* Bertogna and Cirinei's response-time bound recurrence *)
      Definition response_time_recurrence_fp R :=
        R = task_cost tsk + div_floor
                               (total_interference_fp ts tsk R_other R higher_eq_priority)
                               num_cpus.

      Variable R: time.

      Hypothesis H_response_time_recurrence_holds:
        response_time_recurrence_fp R.

      Hypothesis H_response_time_no_larger_than_deadline:
        R <= task_deadline tsk.
      
      Theorem bertogna_cirinei_response_time_bound_fp :
        is_response_time_bound tsk R.
      Proof.
        unfold response_time_recurrence_fp,
               is_response_time_bound, is_response_time_bound_of_task,
               job_has_completed_by, completed,
               completed_jobs_dont_execute,
               valid_sporadic_task_job in *.
        rename H_completed_jobs_dont_execute into COMP,
               H_response_time_recurrence_holds into REC,
               H_valid_job_parameters into PARAMS,
               H_valid_task_parameters into TASK_PARAMS,
               H_restricted_deadlines into RESTR,
               H_response_time_of_interfering_tasks_is_known into RESP_OTHER,
               H_interfering_tasks_miss_no_deadlines into NOMISS,
               H_rate_equals_one into RATE.
        intros j JOBtsk.
        rewrite eqn_leq; apply/andP; split; first by apply COMP.
        set X := R - service rate sched j (job_arrival j + R).
        rewrite -(leq_add2l X).
        unfold X; rewrite [R - _ + service _ _ _ _]subh1; last first.
        
        unfold service; rewrite service_before_arrival_eq_service_during; ins.
        apply leq_trans with (\sum_(job_arrival j <= t < job_arrival j + R) 1); last by rewrite big_const_nat iter_addn mul1n addn0 addnC -addnBA // subnn addn0 leqnn.
        by apply leq_sum; ins; apply service_at_le_max_rate; ins; rewrite RATE.

        move: JOBtsk => /eqP JOBtsk.
        rewrite -addnBA // subnn addn0.
        fold X; rewrite REC.
        apply leq_trans with (n := task_cost tsk + X);
          first by specialize (PARAMS j); des; rewrite addnC leq_add2r -JOBtsk; apply PARAMS0.

        rewrite leq_add2l.
        set x := fun tsk_other =>
          if higher_eq_priority tsk_other tsk && (tsk_other != tsk) then
            task_interference job_cost job_task rate sched j
                     (job_arrival j) R tsk_other
          else 0.


        apply leq_trans
          with (n := div_floor
                       (\sum_(k <- ts) minn (x k) (R - task_cost tsk + 1))
                       num_cpus);
          last first.
        {
          (* First show that the workload bound is an interference bound.*)
          apply leq_div2r; unfold total_interference_fp, x.
          rewrite big_seq_cond [\sum_(_ <- _ | true)_]big_seq_cond.
          apply leq_sum; intro tsk_k; rewrite andbT; intro INk.
          destruct (higher_eq_priority tsk_k tsk && (tsk_k != tsk)) eqn:OTHER;
            last by rewrite min0n.
          move: OTHER => /andP [HPother NEQother].
          unfold interference_bound.
          rewrite leq_min; apply/andP; split; last by apply geq_minr.
          apply leq_trans with (n := task_interference job_cost job_task rate sched j (job_arrival j) R tsk_k); first by apply geq_minl.

          apply leq_trans with (n := workload job_task rate sched tsk_k
                                     (job_arrival j) (job_arrival j + R));
            last by apply workload_bounded_by_W with (job_cost := job_cost)
                                        (job_deadline := job_deadline); ins;
              [ by rewrite RATE
              | by apply TASK_PARAMS
              | by apply RESTR
              | by red; ins; red; apply RESP_OTHER
              | by red; red; ins; apply NOMISS with (tsk_other := tsk_k);
                      repeat split].

          unfold task_interference, workload.
          apply leq_sum; intros t _.
          rewrite -mulnb -[\sum_(_ < _) _]mul1n.
          apply leq_mul; first by apply leq_b1.
          destruct (tsk_is_scheduled job_task sched tsk_k t) eqn:SCHED;
            last by ins.
          unfold tsk_is_scheduled in SCHED.
          move: SCHED =>/exists_inP SCHED; destruct SCHED as [cpu _ HAScpu].
          rewrite -> bigD1 with (j := cpu); simpl; last by ins.
          apply ltn_addr.
          unfold service_of_task, has_job_of_tsk in *.
          by destruct (sched cpu t); [by rewrite HAScpu mul1n RATE|by ins].
        }

        {
          (* Show that X <= 1/m * \sum_k min(x_k, delta - e_k + 1) *)
          admit.
        }
      Qed.         

    End UnderFPScheduling.

    Section UnderJLFPScheduling.

      (* Bertogna and Cirinei's response-time bound recurrence *)
      Definition response_time_recurrence_jlfp R :=
        R <= task_cost tsk + div_floor
                             (total_interference_jlfp ts tsk R_other R)
                             num_cpus.

      Variable R: time.

      Hypothesis response_time_recurrence_holds:
        response_time_recurrence_jlfp R.

      Hypothesis response_time_no_larger_than_deadline:
        R <= task_deadline tsk.

      Theorem bertogna_cirinei_response_time_bound_jlfp :
        is_response_time_bound tsk R.
      Proof.
      Admitted.
      
    End UnderJLFPScheduling.
    
  End ResponseTimeBound.
  
End ResponseTimeAnalysis.