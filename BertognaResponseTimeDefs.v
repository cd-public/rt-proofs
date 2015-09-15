Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs
               PlatformDefs WorkloadDefs SchedulabilityDefs PriorityDefs
               ResponseTimeDefs divround helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

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
    Hypothesis H_at_least_one_cpu :
      num_cpus > 0.
    
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
        (tsk_other \in ts) &&
        higher_eq_priority tsk_other tsk &&
        (tsk_other != tsk).

      Hypothesis H_response_time_of_interfering_tasks_is_known:
        forall tsk_other job_cost,
          is_interfering_task tsk_other ->
          is_response_time_bound_of_task job_cost job_task tsk_other rate sched (R_other tsk_other).

      Hypothesis H_interfering_tasks_miss_no_deadlines:
        forall tsk_other,
          is_interfering_task tsk_other ->
          task_misses_no_deadline job_cost job_deadline job_task rate sched tsk_other.

      Hypothesis H_global_scheduling_invariant:
        forall (j: JobIn arr_seq) (t: time),
          job_task j = tsk ->
          backlogged job_cost rate sched j t ->
          count
            (fun tsk_other : sporadic_task =>
               is_interfering_task tsk_other &&
               tsk_is_scheduled job_task sched tsk_other t) ts = num_cpus.

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
               H_response_time_of_interfering_tasks_is_known into RESP,
               H_interfering_tasks_miss_no_deadlines into NOMISS,
               H_rate_equals_one into RATE,
               H_global_scheduling_invariant into INVARIANT.
        intros j JOBtsk.

        (* Assume by contradiction that job j is not completed at
           time (job_arrival j + R). *)
        destruct (completed job_cost rate sched j (job_arrival j + R)) eqn:COMPLETED;
          first by move: COMPLETED => /eqP COMPLETED; rewrite COMPLETED eq_refl.
        apply negbT in COMPLETED; exfalso.

        (* Let x denote the per-task interference under FP scheduling. *)
        set x := fun tsk_other =>
          if is_interfering_task tsk_other then
            task_interference job_cost job_task rate sched j
                     (job_arrival j) (job_arrival j + R) tsk_other
          else 0.

        set workload_bound := fun tsk_other =>
          if is_interfering_task tsk_other then
            W tsk_other (R_other tsk_other) R
          else 0.                        

        assert (WORKLOAD: forall tsk_k, x tsk_k <= workload_bound tsk_k).   
        {
          intros tsk_k; unfold x, workload_bound.
          destruct (is_interfering_task tsk_k) eqn:INk; last by ins.
          generalize INk; move: INk => /andP [/andP [IN0 IN1] IN2]; ins.

          apply leq_trans with (n := workload job_task rate sched tsk_k
                                              (job_arrival j) (job_arrival j + R));
            last first.
            apply workload_bounded_by_W with (job_cost := job_cost)
                                        (job_deadline := job_deadline); ins;
              [ by rewrite RATE
              | by apply TASK_PARAMS
              | by apply RESTR
              | by red; ins; red; apply RESP
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

        (* Recall that the complement of the interference equals service.*)
        exploit (complement_of_interf_equals_service job_cost rate sched j (job_arrival j) (job_arrival j + R));
          last intro EQinterf; ins; unfold has_arrived;
          first by apply leqnn.
        rewrite {2}[_ + R]addnC -addnBA // subnn addn0 in EQinterf.

        (* Let's call the total interference X. *)
        set X := total_interference job_cost rate sched j (job_arrival j) (job_arrival j + R).

        move: JOBtsk => /eqP JOBtsk.

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

        assert(ALLBUSY: \sum_(tsk_k <- ts) x tsk_k = X * num_cpus).
        {
          unfold x, X, total_interference, task_interference.
          rewrite -big_mkcond -exchange_big big_distrl /=.
          apply eq_big_nat; move => t LTt.
          destruct (backlogged job_cost rate sched j t) eqn:BACK;
            last by rewrite (eq_bigr (fun i => 0));
              [by rewrite big_const_seq iter_addn mul0n addn0 mul0n|by ins].
          rewrite big_mkcond mul1n /=.
          rewrite (eq_bigr (fun i => (if is_interfering_task i && tsk_is_scheduled job_task sched i t then 1 else 0)));
            last by ins; destruct (is_interfering_task i); rewrite ?andTb ?andFb; ins.
          by rewrite -big_mkcond sum1_count; apply (INVARIANT j).
        }
        
        assert (MINSERV: \sum_(tsk_k <- ts) x tsk_k >=
                         (R - task_cost tsk + 1) * num_cpus ->
               \sum_(tsk_k <- ts) minn (x tsk_k) (R - task_cost tsk + 1) >=
               (R - task_cost tsk + 1) * num_cpus).
        {
          intro SUMLESS.
          set more_interf := fun tsk_k => x tsk_k >= R - task_cost tsk + 1.
          rewrite [\sum_(_ <- _) minn _ _](bigID more_interf) /=.
          unfold more_interf, minn.
          rewrite [\sum_(_ <- _ | R - _ + _ <= _)_](eq_bigr (fun i => R - task_cost tsk + 1)); last first.
          {
            intros i COND; rewrite leqNgt in COND.
            destruct (R - task_cost tsk + 1 > x i); ins.
          }
          rewrite [\sum_(_ <- _ | ~~_)_](eq_big (fun i => x i < R - task_cost tsk + 1) (fun i => x i));
            [| by red; ins; rewrite ltnNge
             | by intros i COND; rewrite -ltnNge in COND; rewrite COND].

          (* Case 1 |A| = 0 *)
          destruct (~~ has (fun i => R - task_cost tsk + 1 <= x i) ts) eqn:HASa.
          {
            rewrite [\sum_(_ <- _ | _ <= _) _]big_hasC; last by apply HASa.
            rewrite big_seq_cond; move: HASa => /hasPn HASa.
            rewrite add0n (eq_bigl (fun i => (i \in ts) && true));
              last by red; intros tsk_k; destruct (tsk_k \in ts) eqn:INk;
                [by rewrite andTb ltnNge; apply HASa | by rewrite andFb].
            by rewrite -big_seq_cond. 
          } apply negbFE in HASa.
          
          set card := count (fun i => R - task_cost tsk + 1 <= x i) ts.
          destruct (card >= num_cpus) eqn:CARD.
          {
            apply leq_trans with ((R - task_cost tsk + 1) * card);
              first by rewrite leq_mul2l; apply/orP; right.
            unfold card; rewrite -sum1_count big_distrr /=.
            rewrite -[\sum_(_ <- _ | _) _]addn0.
            by apply leq_add; [by apply leq_sum; ins; rewrite muln1|by ins].
          } apply negbT in CARD; rewrite -ltnNge in CARD.

          assert (GEsum: \sum_(i <- ts | x i < R - task_cost tsk + 1) x i >=
                           (R - task_cost tsk + 1) * (num_cpus - card)).
          {
            set some_interference_A := fun t =>
              backlogged job_cost rate sched j t &&
              has (fun tsk_k => (is_interfering_task tsk_k && ((x tsk_k) >= R - task_cost tsk + 1) && tsk_is_scheduled job_task sched tsk_k t)) ts.      
            set total_interference_B := fun t =>
              backlogged job_cost rate sched j t *
              count (fun tsk_k =>
                is_interfering_task tsk_k &&
                ((x tsk_k) < R - task_cost tsk + 1) &&
                tsk_is_scheduled job_task sched tsk_k t) ts.

            apply leq_trans with ((\sum_(job_arrival j <= t < job_arrival j + R) some_interference_A t) * (num_cpus - card)).
            {
              rewrite leq_mul2r; apply/orP; right.
              move: HASa => /hasP HASa; destruct HASa as [tsk_a INa LEa].
              apply leq_trans with (n := x tsk_a); first by apply LEa.
              unfold x, task_interference, some_interference_A.
              destruct (is_interfering_task tsk_a) eqn:INTERFa; last by ins.
              apply leq_sum; ins.
              destruct (backlogged job_cost rate sched j i);
                [rewrite 2!andTb | by ins].
              destruct (tsk_is_scheduled job_task sched tsk_a i) eqn:SCHEDa;
                [apply eq_leq; symmetry | by ins].
              apply/eqP; rewrite eqb1.
              apply/hasP; exists tsk_a; first by ins.
              apply/andP; split; last by ins.
              by apply/andP; split; ins.
            }
            apply leq_trans with (\sum_(job_arrival j <= t < job_arrival j + R) total_interference_B t).
            {
              rewrite big_distrl /=.
              apply leq_sum; intros t _.
              unfold some_interference_A, total_interference_B. 
              destruct (backlogged job_cost rate sched j t) eqn:BACK;
                [rewrite andTb mul1n | by ins].
              destruct (has (fun tsk_k : sporadic_task =>
                       is_interfering_task tsk_k &&
                       (R - task_cost tsk + 1 <= x tsk_k) &&
                       tsk_is_scheduled job_task sched tsk_k t) ts) eqn:HAS;
                last by ins.
              rewrite mul1n; move: HAS => /hasP HAS.
              destruct HAS as [tsk_k INk H].
              move: H => /andP [/andP [INTERFk LEk] SCHEDk].
              
              exploit INVARIANT;
                [by apply JOBtsk | by apply BACK | intro COUNT].

              unfold card.
              set interfering_tasks_at_t :=
                [seq tsk_k <- ts | is_interfering_task tsk_k && tsk_is_scheduled job_task sched tsk_k t].

              rewrite -(count_filter (fun i => true)) in COUNT.
              fold interfering_tasks_at_t in COUNT.
              rewrite count_predT in COUNT.
              apply leq_trans with (n := num_cpus - count (fun i => is_interfering_task i && (x i >= R -  task_cost tsk + 1) && tsk_is_scheduled job_task sched i t) ts).
              {
                apply leq_sub2l.
                rewrite -2!sum1_count big_mkcond /=.
                rewrite [\sum_(_ <- _ | _ <= _)_]big_mkcond /=.
                apply leq_sum; intros i _.
                unfold x; destruct (is_interfering_task i);
                  [rewrite andTb | by rewrite 2!andFb].
                destruct (tsk_is_scheduled job_task sched i t);
                  [by rewrite andbT | by rewrite andbF].
              }

              rewrite leq_subLR.
              rewrite -count_predUI.
              apply leq_trans with (n :=
                count (predU (fun i : sporadic_task =>
                                is_interfering_task i &&
                                (R - task_cost tsk + 1 <= x i) &&
                                tsk_is_scheduled job_task sched i t)
                             (fun tsk_k0 : sporadic_task =>
                                is_interfering_task tsk_k0 &&
                                (x tsk_k0 < R - task_cost tsk + 1) &&
                                tsk_is_scheduled job_task sched tsk_k0 t))
                      ts); last by apply leq_addr.
              apply leq_trans with (n := size interfering_tasks_at_t);
                first by rewrite COUNT.
              unfold interfering_tasks_at_t.
              rewrite -count_predT count_filter.
              rewrite leq_eqVlt; apply/orP; left; apply/eqP.
              apply eq_count; red; simpl.
              intros i.
              destruct (is_interfering_task i),
                       (tsk_is_scheduled job_task sched i t);
                rewrite 3?andTb ?andFb ?andbF ?andbT /=; try ins.
              by rewrite leqNgt orNb. 
            }
            {
              unfold x at 2, task_interference.
              rewrite [\sum_(i <- ts | _) _](eq_bigr
                (fun i => \sum_(job_arrival j <= t < job_arrival j + R)
                             is_interfering_task i &&
                             backlogged job_cost rate sched j t &&
                             tsk_is_scheduled job_task sched i t));
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
                rewrite big_mkcond [\sum_(i <- ts | _ < _) _]big_mkcond.
                by apply leq_sum; ins; destruct (x i<R - task_cost tsk + 1);
                  [by ins | by rewrite andbF andFb].
              }
            }
          }
          
          rewrite big_const_seq iter_addn addn0; fold card.
          apply leq_trans with (n := (R-task_cost tsk+1)*card +
                                     (R-task_cost tsk+1)*(num_cpus-card));
            last by rewrite leq_add2l.
          by rewrite -mulnDr subnKC //; apply ltnW.
        }
          
        assert (SUM: \sum_(tsk_k <- ts)
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

        assert (EX: has (fun tsk_k =>
                           minn (x tsk_k) (R - task_cost tsk + 1) >
                             minn (workload_bound tsk_k) (R - task_cost tsk + 1))
                        ts).
        {
          (* This part is crappy. I'll remove the ifs from the functions
             and try to keep it in the sum. *)
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
          destruct (tsk_k \in ts) eqn:IN,
                   (higher_eq_priority tsk_k tsk),
                   (tsk_k != tsk);
          rewrite ?andFb ?andTb ?andbT ?min0n IN; try apply leqnn.
          specialize (NOTHAS IN).
          rewrite 3?andbT in NOTHAS.
          unfold interference_bound.
          by rewrite leqNgt; apply NOTHAS.
        }

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

      Theorem bertogna_cirinei_response_time_bound_jlfp :
        is_response_time_bound tsk R.
      Proof.
      Admitted.
      
    End UnderJLFPScheduling.
    
  End ResponseTimeBound.

  Section ResponseTimeTaskset.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    
    Context {arr_seq: arrival_sequence Job}.

    Hypothesis sporadic_tasks: sporadic_task_model arr_seq job_task.
    
    Variable num_cpus: nat.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    (* Assume an FP policy. *)
    Variable higher_eq_priority: fp_policy.

    Variable ts: sporadic_taskset.
    Definition sorted_ts := sorted higher_eq_priority ts.

    Definition max_steps (tsk: sporadic_task) := task_deadline tsk + 1.

    Fixpoint rec (step: nat) (tsk: sporadic_task) : nat :=
      match step with
        | S step => task_cost tsk +
                    div_floor
                      (total_interference_bound_fp ts tsk
                           (fun tsk_high => task_deadline tsk_high)
                           (rec step tsk) higher_eq_priority) num_cpus
      | 0 => task_cost tsk
      end.

    Definition response_time_bound (tsk: sporadic_task) :=
      if rec (max_steps tsk) tsk <= task_deadline tsk then
        Some (rec (max_steps tsk) tsk)
      else None.
    
  End ResponseTimeTaskset.

End ResponseTimeAnalysis.