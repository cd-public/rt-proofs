Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs
               PlatformDefs WorkloadDefs SchedulabilityDefs PriorityDefs
               ResponseTimeDefs divround helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop div.

Module ResponseTimeAnalysis.

  Import Job SporadicTaskset Schedule Workload Schedulability ResponseTime Priority SporadicTaskArrival.

  Section Interference.

    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    Context {arr_seq: arrival_sequence Job}.

    Context {num_cpus: nat}.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    Variable j: JobIn arr_seq.
    Variable t1 t2: time.

    Let job_is_backlogged (t: time) :=
      backlogged job_cost rate sched j t.

    Definition total_interference :=
      \sum_(t1 <= t < t2) job_is_backlogged t.

    Section TaskInterference.

      Variable tsk: sporadic_task.
    
      Definition has_job_of_tsk (cpu: processor num_cpus) (t: time) :=
        match (sched cpu t) with
          | Some j' => job_task j' == tsk
          | None => false
        end.
    
      Definition tsk_is_scheduled (t: time) :=
        [exists cpu in processor num_cpus, has_job_of_tsk cpu t].
    
      Definition task_interference :=
        \sum_(t1 <= t < t2)
          (job_is_backlogged t && tsk_is_scheduled t).

    End TaskInterference.

    Section BasicLemmas.

      Lemma total_interference_le_delta : total_interference <= t2 - t1.
      Proof.
        unfold total_interference.
        apply leq_trans with (n := \sum_(t1 <= t < t2) 1);
          first by apply leq_sum; ins; apply leq_b1.
        by rewrite big_const_nat iter_addn mul1n addn0 leqnn.
      Qed.

    End BasicLemmas.
    
    Section CorrespondenceWithService.

      Hypothesis no_parallelism:
        jobs_dont_execute_in_parallel sched.

      Hypothesis rate_equals_one :
        forall j cpu, rate j cpu = 1.

      Hypothesis jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute sched.

      Hypothesis completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost rate sched.
      
      Hypothesis job_has_arrived :
        has_arrived j t1.
      
      Hypothesis job_is_not_complete :
        ~~ completed job_cost rate sched j t2.

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
    Variable tsk: sporadic_task.

    (* Assume a known response-time bound for each interfering task ... *)
    Variable R_other: sporadic_task -> time.
    (* ... and an interval length delta. *)
    Variable delta: time.

    (* Based on Bertogna and Cirinei's workload bound, ... *)
    Let workload_bound (tsk_other: sporadic_task) :=
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
      Definition total_interference_bound_fp :=
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
      Definition total_interference_bound_jlfp :=
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
        R = task_cost tsk +
            div_floor
              (total_interference_bound_fp ts tsk R_other R higher_eq_priority)
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
        destruct (completed job_cost rate sched j (job_arrival j + R)) eqn:COMPLETED;
          first by move: COMPLETED => /eqP COMPLETED; rewrite COMPLETED eq_refl.
        apply negbT in COMPLETED.

        (* Recall that the complement of the interference equals service.*)
        exploit (complement_of_interf_equals_service job_cost rate sched j (job_arrival j) (job_arrival j + R));
          last intro EQinterf; ins; unfold has_arrived;
          first by apply leqnn.
        rewrite {2}[_ + R]addnC -addnBA // subnn addn0 in EQinterf.

        unfold service; move: JOBtsk => /eqP JOBtsk.
        
        (* Now we start the proof. *)
        rewrite eqn_leq; apply/andP; split; first by apply COMP.

        (* Rephrase the service in terms of backlogged time. *)
        rewrite service_before_arrival_eq_service_during // EQinterf.
        set X := total_interference job_cost rate sched j 
                                    (job_arrival j) (job_arrival j + R).

        (* Reorder the inequality. *)
        rewrite -(leq_add2l X).
        rewrite addnBA; last first.
        {
          rewrite -[R](addKn (job_arrival j)).
          apply total_interference_le_delta.
        }
        rewrite [X + R]addnC -addnBA // subnn addn0.


        (* Bound the backlogged time using Bertogna's interference bound. *)
        rewrite REC addnC; apply leq_add;
          first by specialize (PARAMS j); des; rewrite -JOBtsk; apply PARAMS0.
                
        set x := fun tsk_other =>
          if higher_eq_priority tsk_other tsk && (tsk_other != tsk) then
            task_interference job_cost job_task rate sched j
                     (job_arrival j) (job_arrival j + R) tsk_other
          else 0.

        (* First, we show that Bertogna and Cirinei's interference bound
           indeed upper-bounds the sum of individual task interferences. *)
        assert (BOUND:
          \sum_(k <- ts) minn (x k) (R - task_cost tsk + 1) <=
          total_interference_bound_fp ts tsk R_other R higher_eq_priority).
        {
          unfold total_interference_bound_fp, x.
          rewrite big_seq_cond [\sum_(_ <- _ | true)_]big_seq_cond.
          apply leq_sum; intro tsk_k; rewrite andbT; intro INk.
          destruct (higher_eq_priority tsk_k tsk && (tsk_k != tsk)) eqn:OTHER;
            last by rewrite min0n.
          move: OTHER => /andP [HPother NEQother].
          unfold interference_bound.
          rewrite leq_min; apply/andP; split; last by apply geq_minr.
          apply leq_trans with (n := task_interference job_cost job_task rate sched j (job_arrival j) (job_arrival j + R) tsk_k);
            first by apply geq_minl.

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
            by destruct (sched cpu t);[by rewrite HAScpu mul1n RATE|by ins].
        }

        (* Now, we show that total interference is bounded by the
           average of total task interference. *)
        assert (AVG: X <= div_floor
                            (\sum_(k <- ts) minn (x k) (R-task_cost tsk+1))
                            num_cpus).
        {
          admit.
        }

        (* To conclude the proof, we just apply transitivity with
           the proven lemmas. *)
        apply (leq_trans AVG), leq_div2r, BOUND.
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