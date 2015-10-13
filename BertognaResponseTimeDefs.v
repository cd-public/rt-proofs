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

    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.

    Definition task_with_response_time := (sporadic_task * time)%type.
    
    (* Assume a known response-time bound for each interfering task ... *)
    Variable R_prev: seq task_with_response_time.

    (* ... and an interval length delta. *)
    Variable delta: time.

    Section PerTask.

      Variable tsk_R: task_with_response_time.
      Let tsk_other := fst tsk_R.
      Let R_other := snd tsk_R.
    
      (* Based on the workload bound, Bertogna and Cirinei define the
         following interference bound for a task. *)
      Definition interference_bound :=
        minn (W tsk_other R_other delta) (delta - (task_cost tsk) + 1).

    End PerTask.

    Section FP.
      
      (* Assume an FP policy. *)
      Variable higher_eq_priority: fp_policy.

      Definition is_interfering_task_fp (tsk_other: sporadic_task) :=
        higher_eq_priority tsk_other tsk && (tsk_other != tsk).
      
      (* The total interference incurred by tsk is thus bounded by: *)
      Definition total_interference_bound_fp :=
        \sum_((tsk_other, R_other) <- R_prev | is_interfering_task_fp tsk_other)
           interference_bound (tsk_other, R_other).
      
    End FP.

    Section JLFP.

      Let is_interfering_task_jlfp (tsk_other: sporadic_task) :=
        tsk_other != tsk.
      
      (* The total interference incurred by tsk is thus bounded by: *)
      Definition total_interference_bound_jlfp :=
        \sum_((tsk_other, R_other) <- R_prev | is_interfering_task_jlfp tsk_other)
           interference_bound (tsk_other, R_other).

    End JLFP.

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
    Hypothesis H_valid_task_parameters: valid_sporadic_taskset ts.
    Hypothesis H_restricted_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    (* Next, consider a task tsk that is to be analyzed. *)
    Variable tsk: sporadic_task.
    Hypothesis task_in_ts: tsk \in ts.

    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task rate sched tsk.
    Let is_response_time_bound (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_cost job_task tsk rate sched.

    (* Assume a known response-time bound for any interfering task *)
    Variable hp_bounds: seq task_with_response_time.
    
    (* We derive the response-time bounds for FP and EDF scheduling
       separately. *)
    Section UnderFPScheduling.

      (* For FP scheduling, assume there exists a fixed task priority. *)
      Variable higher_eq_priority: fp_policy.

      Let interferes_with_tsk := is_interfering_task_fp tsk higher_eq_priority.
      
      (* Assume that for any interfering task, a response-time
         bound R_other is known. *)
      Hypothesis H_response_time_of_interfering_tasks_is_known:
        forall hp_tsk,
          hp_tsk \in ts ->
          interferes_with_tsk hp_tsk ->
          exists R,
            (hp_tsk, R) \in hp_bounds.

      Hypothesis H_response_time_of_interfering_tasks_is_known2:
        forall hp_tsk R,
          (hp_tsk, R) \in hp_bounds ->
          is_response_time_bound_of_task job_cost job_task hp_tsk rate sched R.

      (* Assume that the response-time bounds are larger than task costs. *)
      Hypothesis H_response_time_bounds_ge_cost:
        forall hp_tsk R,
          (hp_tsk, R) \in hp_bounds -> R >= task_cost hp_tsk.
      
      (* Assume that no deadline is missed by any interfering task, i.e.,
         response-time bound R_other <= deadline. *)
      Hypothesis H_interfering_tasks_miss_no_deadlines:
        forall hp_tsk R,
          (hp_tsk, R) \in hp_bounds -> R <= task_deadline hp_tsk.

      (* Assume that the schedule satisfies the global scheduling
         invariant, i.e., if any job of tsk is backlogged, all
         the processors must be busy with jobs of equal or higher
         priority. *)
      Hypothesis H_global_scheduling_invariant:
        forall (j: JobIn arr_seq) (t: time),
          job_task j = tsk ->
          backlogged job_cost rate sched j t ->
          count
            (fun tsk_other : sporadic_task =>
               is_interfering_task_fp tsk higher_eq_priority tsk_other &&
               task_is_scheduled job_task sched tsk_other t) ts = num_cpus.

      (* Next, we define Bertogna and Cirinei's response-time bound recurrence *)
      
      (* Let R be any time. *)
      Variable R: time.

      (* Bertogna and Cirinei's response-time analysis states that
         if R is a fixed-point of the following recurrence, ... *)
      Hypothesis H_response_time_recurrence_holds :
        R = task_cost tsk +
            div_floor
              (total_interference_bound_fp tsk hp_bounds R higher_eq_priority)
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
               H_response_time_of_interfering_tasks_is_known into ALLHP,
               H_response_time_of_interfering_tasks_is_known2 into RESP,
               H_interfering_tasks_miss_no_deadlines into NOMISS,
               H_rate_equals_one into RATE,
               H_global_scheduling_invariant into INVARIANT,
               H_response_time_bounds_ge_cost into GE_COST.
        intros j JOBtsk.
        
        (* For simplicity, let x denote per-task interference under FP
           scheduling, and let X denote the total interference. *)
        set x := fun hp_tsk =>
          if (hp_tsk \in ts) && interferes_with_tsk hp_tsk then
            task_interference job_cost job_task rate sched j
                     (job_arrival j) (job_arrival j + R) hp_tsk
          else 0.
        set X := total_interference job_cost rate sched j (job_arrival j) (job_arrival j + R).

        (* Let's recall the workload bound under FP scheduling. *)
        set workload_bound := fun (tup: task_with_response_time) =>
          let (tsk_k, R_k) := tup in
            if interferes_with_tsk tsk_k then
              W tsk_k R_k R
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
        assert (WORKLOAD: forall tsk_k,
                            (tsk_k \in ts) && interferes_with_tsk tsk_k ->
                            forall R_k, 
                              (tsk_k, R_k) \in hp_bounds ->
                              x tsk_k <= workload_bound (tsk_k, R_k)).   
        {
          move => tsk_k /andP [INk INTERk] R_k HPk.
          unfold x, workload_bound; rewrite INk INTERk andbT.
          exploit (ALLHP tsk_k); [by ins | by ins | intro INhp; des].
          apply leq_trans with (n := workload job_task rate sched tsk_k
                                    (job_arrival j) (job_arrival j + R)).
          {
            unfold task_interference, workload.
            apply leq_sum; intros t _.
            rewrite -mulnb -[\sum_(_ < _) _]mul1n.
            apply leq_mul; first by apply leq_b1.
            destruct (task_is_scheduled job_task sched tsk_k t) eqn:SCHED; last by ins.
            unfold task_is_scheduled in SCHED.
            move: SCHED =>/exists_inP SCHED.
            destruct SCHED as [cpu _ HAScpu].
            rewrite -> bigD1 with (j := cpu); simpl; last by ins.
            apply ltn_addr; unfold service_of_task, schedules_job_of_tsk in *.
            by destruct (sched cpu t);[by rewrite HAScpu mul1n RATE|by ins].
          }
          {
            apply workload_bounded_by_W with
            (job_cost := job_cost) (job_deadline := job_deadline); ins;
              [ by rewrite RATE
              | by apply TASK_PARAMS
              | by apply RESTR
              | by red; red; ins; apply (RESP tsk_k)  
              | by apply GE_COST |].
            red; red; move => j' /eqP JOBtsk' _;
            unfold job_misses_no_deadline.
            specialize (PARAMS j'); des.
            rewrite PARAMS1 JOBtsk'.
            apply completion_monotonic with (t := job_arrival j' + R0); ins;
              [by rewrite leq_add2l; apply NOMISS | by apply (RESP tsk_k)].
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
        assert(ALLBUSY: \sum_(tsk_k <- ts) x tsk_k = X * num_cpus).
        {
          unfold x, X, total_interference, task_interference.
          rewrite -big_mkcond -exchange_big big_distrl /=.
          apply eq_big_nat; move => t LTt.
          destruct (backlogged job_cost rate sched j t) eqn:BACK;
            last by rewrite (eq_bigr (fun i => 0));
              [by rewrite big_const_seq iter_addn mul0n addn0 mul0n|by ins].
          rewrite big_mkcond mul1n /=.
          rewrite (eq_bigr (fun i =>
                              (if (i \in ts) && interferes_with_tsk i &&
                                             task_is_scheduled job_task sched i t then 1 else 0))); last first.
          {
            ins; destruct ((i \in ts) && interferes_with_tsk i) eqn:IN;
              rewrite IN; [by rewrite andTb | by rewrite andFb].
          }
          rewrite (eq_bigr (fun i => if (i \in ts) && true then (if interferes_with_tsk i && task_is_scheduled job_task sched i t then 1 else 0) else 0));
            last by ins; destruct (i \in ts) eqn:IN; rewrite IN ?andTb ?andFb.
          by rewrite -big_mkcond -big_seq_cond -big_mkcond sum1_count; apply (INVARIANT j).
        }

        (* 3) Next, we prove the auxiliary lemma from the paper. *)
        assert (MINSERV: \sum_(tsk_k <- ts) x tsk_k >=
                         (R - task_cost tsk + 1) * num_cpus ->
               \sum_(tsk_k <- ts) minn (x tsk_k) (R - task_cost tsk + 1) >=
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
          destruct (~~ has (fun i => R - task_cost tsk + 1 <= x i) ts) eqn:HASa.
          {
            rewrite [\sum_(_ <- _ | _ <= _) _]big_hasC; last by apply HASa.
            rewrite big_seq_cond; move: HASa => /hasPn HASa.
            rewrite add0n (eq_bigl (fun i => (i \in ts) && true));
              last by red; intros tsk_k; destruct (tsk_k \in ts) eqn:INk;
                [by rewrite andTb ltnNge; apply HASa | by rewrite andFb].
            by rewrite -big_seq_cond.
          } apply negbFE in HASa.
          
          set cardA := count (fun i => R - task_cost tsk + 1 <= x i) ts.
          destruct (cardA >= num_cpus) eqn:CARD.
          {
            apply leq_trans with ((R - task_cost tsk + 1) * cardA);
              first by rewrite leq_mul2l; apply/orP; right.
            unfold cardA; rewrite -sum1_count big_distrr /=.
            rewrite -[\sum_(_ <- _ | _) _]addn0.
            by apply leq_add; [by apply leq_sum; ins; rewrite muln1|by ins].
          } apply negbT in CARD; rewrite -ltnNge in CARD.

          assert (GEsum: \sum_(i <- ts | x i < R - task_cost tsk + 1) x i >=
                           (R - task_cost tsk + 1) * (num_cpus - cardA)).
          {
            set some_interference_A := fun t =>
              backlogged job_cost rate sched j t &&
              has (fun tsk_k => (interferes_with_tsk tsk_k &&
                              ((x tsk_k) >= R - task_cost tsk + 1) &&
                              task_is_scheduled job_task sched tsk_k t)) ts.      
            set total_interference_B := fun t =>
              backlogged job_cost rate sched j t *
              count (fun tsk_k =>
                interferes_with_tsk tsk_k &&
                ((x tsk_k) < R - task_cost tsk + 1) &&
                task_is_scheduled job_task sched tsk_k t) ts.

            apply leq_trans with ((\sum_(job_arrival j <= t < job_arrival j + R)
                                      some_interference_A t) * (num_cpus - cardA)).
            {
              rewrite leq_mul2r; apply/orP; right.
              move: HASa => /hasP HASa; destruct HASa as [tsk_a INa LEa].
              apply leq_trans with (n := x tsk_a); first by apply LEa.
              unfold x, task_interference, some_interference_A.
              destruct ((tsk_a \in ts) && interferes_with_tsk tsk_a) eqn:INTERFa;
                rewrite INTERFa; last by ins.
              move: INTERFa => /andP INTERFa; des.
              apply leq_sum; ins.
              destruct (backlogged job_cost rate sched j i);
                [rewrite 2!andTb | by ins].
              destruct (task_is_scheduled job_task sched tsk_a i) eqn:SCHEDa;
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
              destruct (has (fun tsk_k : sporadic_task =>
                       interferes_with_tsk tsk_k &&
                       (R - task_cost tsk + 1 <= x tsk_k) &&
                       task_is_scheduled job_task sched tsk_k t) ts) eqn:HAS;
                last by ins.
              rewrite mul1n; move: HAS => /hasP HAS.
              destruct HAS as [tsk_k INk H].
              move: H => /andP [/andP [INTERFk LEk] SCHEDk].
              
              exploit INVARIANT;
                [by apply JOBtsk | by apply BACK | intro COUNT].

              unfold cardA.
              set interfering_tasks_at_t :=
                [seq tsk_k <- ts | interferes_with_tsk tsk_k &&
                                  task_is_scheduled job_task sched tsk_k t].

              rewrite -(count_filter (fun i => true)) in COUNT.
              fold interfering_tasks_at_t in COUNT.
              rewrite count_predT in COUNT.
              apply leq_trans with (n := num_cpus -
                                      count (fun i => interferes_with_tsk i &&
                                                    (x i >= R -  task_cost tsk + 1) &&
                                                    task_is_scheduled job_task sched i t) ts).
              {
                apply leq_sub2l.
                rewrite -2!sum1_count big_mkcond /=.
                rewrite [\sum_(_ <- _ | _ <= _)_]big_mkcond /=.
                apply leq_sum; intros i _.
                unfold x; destruct (interferes_with_tsk i);
                  [rewrite andTb | by rewrite 2!andFb].
                destruct (task_is_scheduled job_task sched i t);
                  [by rewrite andbT | by rewrite andbF].
              }

              rewrite leq_subLR.
              rewrite -count_predUI.
              apply leq_trans with (n :=
                count (predU (fun i : sporadic_task =>
                                interferes_with_tsk i &&
                                (R - task_cost tsk + 1 <= x i) &&
                                task_is_scheduled job_task sched i t)
                             (fun tsk_k0 : sporadic_task =>
                                interferes_with_tsk tsk_k0 &&
                                (x tsk_k0 < R - task_cost tsk + 1) &&
                                task_is_scheduled job_task sched tsk_k0 t))
                      ts); last by apply leq_addr.
              apply leq_trans with (n := size interfering_tasks_at_t);
                first by rewrite COUNT.
              unfold interfering_tasks_at_t.
              rewrite -count_predT count_filter.
              rewrite leq_eqVlt; apply/orP; left; apply/eqP.
              apply eq_count; red; simpl.
              intros i.
              destruct (interferes_with_tsk i),
                       (task_is_scheduled job_task sched i t);
                rewrite 3?andTb ?andFb ?andbF ?andbT /=; try ins.
              by rewrite leqNgt orNb. 
            }
            {
              unfold x at 2, task_interference.
              rewrite [\sum_(i <- ts | _) _](eq_bigr
                (fun i => \sum_(job_arrival j <= t < job_arrival j + R)
                             (i \in ts) && interferes_with_tsk i &&
                             backlogged job_cost rate sched j t &&
                             task_is_scheduled job_task sched i t));
                last first.
              {
                ins; destruct ((i \in ts) && interferes_with_tsk i) eqn:INTERi; rewrite INTERi;
                  first by move: INTERi => /andP [_ INTERi]; apply eq_bigr; ins; rewrite INTERi andTb.
                by rewrite (eq_bigr (fun i => 0));
                  [by rewrite big_const_nat iter_addn mul0n addn0 | by ins].
              }
              {
                rewrite exchange_big /=; apply leq_sum; intros t _.
                unfold total_interference_B.
                destruct (backlogged job_cost rate sched j t); last by ins.
                rewrite mul1n -sum1_count.
                rewrite big_seq_cond big_mkcond [\sum_(i <- ts | _ < _) _]big_mkcond.
                apply leq_sum; ins; destruct (x i<R - task_cost tsk + 1);
                  [by rewrite 2!andbT andbA | by rewrite 2!andbF].
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
              is not enough to cover the sum of the "minimum" term over
              all tasks (artifact of the proof by contradiction). *)
        assert (SUM: \sum_((tsk_k, R_k) <- hp_bounds)
                       minn (x tsk_k) (R - task_cost tsk + 1) >
                       total_interference_bound_fp tsk hp_bounds
                                                   R higher_eq_priority).
        {
          apply leq_trans with (n := \sum_(tsk_k <- ts) minn (x tsk_k) (R - task_cost tsk + 1));
            last first.
          {
            rewrite (eq_bigr (fun i => minn (x (fst i)) (R - task_cost tsk + 1)));
              last by ins; destruct i.
            rewrite (bigID (fun i => (fst i \in ts) && interferes_with_tsk (fst i))) /=.
            rewrite -[\sum_(_ <- _) _]addn0; apply leq_add; last by ins.
            apply leq_trans with (n := \sum_(tsk_k <- ts | interferes_with_tsk tsk_k) minn (x tsk_k) (R - task_cost tsk + 1)).
            {
              rewrite [\sum_(_ <- _ | interferes_with_tsk _)_]big_mkcond eq_leq //.
              apply eq_bigr; intros i _; unfold x.
              by destruct (interferes_with_tsk i); rewrite ?andbT ?andbF ?min0n.
            }
            have MAP := big_map (fun x => fst x) (fun i => (i \in ts) && interferes_with_tsk i) (fun i => minn (x i) (R - task_cost tsk + 1)).
            rewrite -MAP -big_filter -[\sum_(_ <- [seq fst x0 | x0 <- _] | _)_]big_filter; clear MAP.
            apply leq_sum_subseq; rewrite subseq_filter; apply/andP; split;
              first by apply/allP; intro i; rewrite mem_filter andbC.
            admit.
          }
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

        (* 5) This implies that there exists a tuple (tsk_k, R_k) such that
              min (x_k, R - e_i + 1) > min (W_k, R - e_i + 1). *)        
        assert (EX:  has (fun tup : task_with_response_time =>
                            let (tsk_k, R_k) := tup in
                              (tsk_k \in ts) &&
                              interferes_with_tsk tsk_k &&        
                              (minn (x tsk_k) (R - task_cost tsk + 1) >
                              minn (workload_bound (tsk_k, snd tup)) (R - task_cost tsk + 1)))
                         hp_bounds).
        {
          apply/negP; unfold not; intro NOTHAS.
          move: NOTHAS => /negP /hasPn ALL.
          rewrite -[_ < _]negbK in SUM.
          move: SUM => /negP SUM; apply SUM; rewrite -leqNgt.
          unfold total_interference_bound_fp.
          rewrite [\sum_(i <- _ | let '(tsk_other, _) := i in _)_]big_mkcond.
          rewrite big_seq_cond [\sum_(i <- _ | true) _]big_seq_cond.
          apply leq_sum; move => tsk_k /andP [HPk _]; destruct tsk_k as [tsk_k R_k].
          specialize (ALL (tsk_k, R_k) HPk).
          unfold interference_bound, workload_bound, x in *.
          fold (interferes_with_tsk); destruct (interferes_with_tsk tsk_k) eqn:INTERFk;
            [rewrite andbT in ALL; rewrite andbT | by rewrite andbF min0n].
          destruct (tsk_k \in ts) eqn:INk; rewrite INk; last by rewrite min0n.
          by rewrite INk andTb -leqNgt in ALL.
        }
        
        (* For this particular task, we show that x_k > W_k.
           This contradicts the previous claim. *)
        move: EX => /hasP EX; destruct EX as [tup_k HPk LTmin].
        destruct tup_k as [tsk_k R_k]; simpl in LTmin.
        move: LTmin => /andP [INTERFk LTmin]; move: (INTERFk) => /andP [INk INTERFk'].
        rewrite INTERFk' in LTmin; unfold minn at 1 in LTmin.
        destruct (W tsk_k R_k R < R - task_cost tsk + 1); rewrite leq_min in LTmin;
          last by move: LTmin => /andP [_ BUG]; rewrite ltnn in BUG.
        move: LTmin => /andP [BUG _]; des.
        specialize (WORKLOAD tsk_k INTERFk R_k HPk).
        apply leq_ltn_trans with (p := x tsk_k) in WORKLOAD; first by rewrite ltnn in WORKLOAD.
        by unfold workload_bound; rewrite INTERFk'; apply BUG.
      Qed.

    End UnderFPScheduling.

    Section UnderJLFPScheduling.

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

    (* Consider a task set ts. *)
    Variable ts: sporadic_taskset.
    (*Load seq_nat_notation.*)
        
    (* Next we define the fixed-point iteration for computing
       Bertogna's response-time bound for any task in ts. *)
    
    (* First, given a function containing known response-time bounds
       for the higher-priority tasks, we compute the response-time bound
       of tsk using the following fixed-point iteration: 

       R_tsk <- f^step (R_tsk),
         where f is the response-time recurrence,
         step is the number of iterations,
         and f^0 = task_cost tsk. *)
    Definition per_task_rta (tsk: sporadic_task)
                      (R_prev: seq task_with_response_time) (step: nat) :=
      iter step
        (fun t => task_cost tsk +
                  div_floor
                    (total_interference_bound_fp
                                      tsk R_prev t higher_eq_priority)
                    num_cpus)
        (task_cost tsk).

    (* To ensure that the iteration converges, we will apply per_task_rta
       a "sufficient" number of times: task_deadline tsk + 1.
       Note that (deadline + 1) is pessimistic, but we don't care about
       the precise runtime complexity here. *)
    Definition max_steps (tsk: sporadic_task) := task_deadline tsk + 1.
    
    (* Next, we compute the response-time bounds of the task set.
       The function either returns a list of pairs (tsk, R_tsk) for the
       entire taskset or None, if the analysis failed for some task.
       Assume that the task set is sorted in increasing priority order. *)
    Definition R_list : option (seq task_with_response_time) :=
      (fix prev_pairs (ts: sporadic_taskset) :=
        match ts with
        | nil => Some nil
        | tsk :: ts' =>
          if (prev_pairs ts') is Some rt_bounds then
            let R := per_task_rta tsk rt_bounds (max_steps tsk) in
              if R <= task_deadline tsk then
                Some ((tsk, R) :: rt_bounds)
              else None
          else None
        end) ts.

    Definition fp_schedulability_test := R_list != None.
    
    (*Section AuxiliaryLemmas.

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

      (* Next, we prove a helper lemma about the size of the vector
         containing the previously computed bounds. *)
      Lemma size_R_hp' :
        forall t P, size (R_hp' t P) = t.
      Proof.
        by induction t; ins; rewrite size_rcons IHt.
      Qed.
        
      (* Finally, we establish the equivalence between computing R directly
         and accessing an R that we previously stored in the vector. *)
      Lemma rhp_eq_R:
        forall (tsk i: task_in_ts) (LT: i < tsk),
          ext_tuple_to_fun_index (R_hp tsk) i = R i.
      Proof.
        intros tsk i LT.
        destruct i as [i Hi].
        unfold ext_tuple_to_fun_index; des_eqrefl2;
          [clear LT | by rewrite EQ in LT].
        destruct tsk as [t T].
        rewrite (tnth_nth 0) /R /R_hp; simpl in *.
        revert i EQ Hi.
        induction t; intros => /=;
          first by rewrite ltn0 in EQ.
        {
          rewrite nth_rcons size_R_hp'; simpl in *; desf; first last.
          {
            apply negbT in Heq0; apply negbT in Heq.
            rewrite neq_ltn in Heq0; move: Heq0 => /orP OR; des;
              first by rewrite OR in Heq.
            rewrite ltnS in EQ.
            by apply (leq_ltn_trans EQ) in OR; rewrite ltnn in OR.
          }
          {
            move: Heq0 => /eqP Heq0; subst i.
            assert (EQP:  (R_hp' t (R_hp'_obligation_3 t.+1 (ltn_ord (Ordinal (n:=size ts) (m:=t.+1) T))  t Logic.eq_refl)) = 
             (R_hp' t (ltn_ord (Ordinal (n:=size ts) (m:=t) Hi)))).
              by f_equal; apply proof_irrelevance.
            rewrite EQP; clear EQP.
            assert (EQMAX:   (max_steps
        (Ordinal (n:=size ts) (m:=t)
           (ltnW (m:=t.+1) (n:=size ts)
                 (ltn_ord (Ordinal (n:=size ts) (m:=t.+1) T))))) =
                (max_steps (Ordinal (n:=size ts) (m:=t) Hi))).
              by f_equal; apply ord_inj; ins.
            rewrite EQMAX; clear EQMAX.
            assert (EQORD: ltnW (m:=t.+1) (n:=size ts)
                      (ltn_ord (Ordinal (n:=size ts) (m:=t.+1) T)) = Hi).
              by apply proof_irrelevance.
            by rewrite EQORD.
          }
          {
            rewrite -IHt; [by apply ltSnm | | by ins].
            ins; f_equal.
            assert (EQP: (R_hp'_obligation_1 t.+1 (ltn_ord (Ordinal (n:=size ts) (m:=t.+1) T)) t Logic.eq_refl) = (ltn_ord (Ordinal (n:=size ts) (m:=t) Hyp0))).
              by apply proof_irrelevance.
            by rewrite EQP.
          }
        }
      Qed.

    End AuxiliaryLemmas. *)
    
    Section Proof.

      (* Assume that higher_eq_priority is a total order over the task set. *)
      Hypothesis H_reflexive: reflexive higher_eq_priority.
      Hypothesis H_transitive: transitive higher_eq_priority.
      Hypothesis H_unique_priorities: antisymmetric higher_eq_priority.
      Hypothesis H_total: total higher_eq_priority.

      (* Assume the task set has no duplicates, ... *)
      Hypothesis H_ts_is_a_set: uniq ts.

      (* ...all tasks have valid parameters, ... *)
      Hypothesis H_valid_task_parameters: valid_sporadic_taskset ts.

      (* ...restricted deadlines, ...*)
      Hypothesis H_restricted_deadlines:
        forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

      (* ...and tasks are ordered by increasing priorities. *)
      Hypothesis H_sorted_ts: reverse_sorted higher_eq_priority ts.

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

      (* Assume the platform satisfies the global scheduling invariant. *)
      Hypothesis H_global_scheduling_invariant:
        forall (tsk: sporadic_task) (j: JobIn arr_seq) (t: time),
          tsk \in ts ->
          job_task j = tsk ->
          backlogged job_cost rate sched j t ->
          count
            (fun tsk_other : _ =>
               is_interfering_task_fp tsk higher_eq_priority tsk_other &&
               task_is_scheduled job_task sched tsk_other t) ts = num_cpus.

      Definition no_deadline_missed_by (tsk: sporadic_task) :=
        task_misses_no_deadline job_cost job_deadline job_task
                                rate sched tsk.

      (* Now we present the proofs of termination and correctness of
         the schedulability test. *)

                                            
      (*  To prove convergence of R, we first show convergence of rt_rec. *)
      Lemma rt_rec_converges:
        forall (tsk: sporadic_task) prev,
          tsk \in ts ->
          per_task_rta tsk prev (max_steps tsk) <= task_deadline tsk ->
          per_task_rta tsk prev (max_steps tsk) =
            per_task_rta tsk prev (max_steps tsk).+1.
      Proof.
        rename H_valid_task_parameters into TASKPARAMS.
        unfold valid_sporadic_taskset, valid_sporadic_task in *.

        (* To simplify, let's call the function f.*)
        intros tsk prev INtsk LE; set (f := per_task_rta tsk prev); fold f in LE.

        assert (INprev: forall i, i \in prev -> fst i \in ts).
          admit.

        assert (GE_COST: forall i,i \in prev -> snd i >= task_cost (fst i)).
          admit.
        
        (* First prove that f is monotonic.*)
        assert (MON: forall x1 x2, x1 <= x2 -> f x1 <= f x2).
        {
          intros x1 x2 LEx; unfold f, per_task_rta.
          apply fun_mon_iter_mon; [by ins | by ins; apply leq_addr |].
          clear LEx x1 x2; intros x1 x2 LEx.
          
          unfold div_floor, total_interference_bound_fp.
          rewrite big_seq_cond [\sum_(i <- _ | let '(tsk_other, _) := i in
                                   _ && (tsk_other != tsk))_]big_seq_cond.
          rewrite leq_add2l leq_div2r // leq_sum //.
          intros i; specialize (INprev i); specialize (GE_COST i).
          destruct i as [i R]; move => /andP [IN _].
          unfold interference_bound; simpl.
          rewrite leq_min; apply/andP; split.
          {
            apply leq_trans with (n := W i R x1); 
              first by apply geq_minl.            
            exploit (TASKPARAMS i); [by apply INprev | intro PARAMS; des].
            by apply W_monotonic; try (by ins); apply GE_COST.
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
      (*Theorem R_converges:
        forall tsk,
          tsk \in ts ->
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
      Qed.*)

      (* Finally, we show that if the schedulability test suceeds, ...*)
      Hypothesis H_test_passes: fp_schedulability_test.
      
      (*..., then no task misses its deadline. *)
      Theorem taskset_schedulable_by_fp_rta :
        forall tsk, tsk \in ts -> no_deadline_missed_by tsk.
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
               H_transitive into TRANS,
               H_unique_priorities into UNIQ,
               H_total into TOTAL,
               H_all_jobs_from_taskset into ALLJOBS,
               H_test_passes into TEST.
      
        move: SORT => SORT.
        move => tsk INtsk j /eqP JOBtsk.

        move: TEST => /eqP TEST.
        unfold R_list in TEST.
        clear ALLJOBS H_reflexive H_ts_is_a_set.

        have CONV := rt_rec_converges.

        (*generalize dependent j.
        generalize dependent tsk.
        
        destruct ts as [| tsk0 hp_tasks]; first by intro t; rewrite in_nil.
        desf; rename l into hp_bounds.

        set R0 := per_task_rta tsk0 hp_bounds (max_steps tsk0).
      
        assert (INbounds: forall hp_tsk,
                  hp_tsk \in ts ->
                  exists R_tsk,
                    (hp_tsk, R_tsk) \in R_list).
        {
          admit.
        }
        
        cut (
          forall (hp_tsk : task_eqType) (R : nat_eqType),
            (hp_tsk, R) \in (tsk0, R0) :: hp_bounds ->
             forall j : JobIn arr_seq,
             job_task j = hp_tsk ->
             service rate sched j (job_arrival j + job_deadline j ) == job_cost j). 
        {
          intros CUT; ins.
          specialize (INbounds tsk INtsk); des.
          by apply (CUT tsk R_tsk INbounds).
        }

        induction hp_bounds as [| (tsk_i, R_i) hp_tasks'].
        {
          (* Base case: lowest-priority task. *)
          intros hp_tsk R; rewrite mem_seq1; move/eqP => EQ j JOBj.
          
        }*)

        generalize dependent j.
        generalize dependent tsk.
        induction ts as [| tsk_i hp_tasks].
        {
          by intros tsk; rewrite in_nil.
        }
        {
          (* Inductive step: all higher-priority tasks are schedulable. *)
          intros tsk INtsk; rewrite in_cons in INtsk.
          move: INtsk => /orP INtsk; des; last first.
          {
            desf; apply IHhp_tasks; try (by ins).
            by red; ins; apply TASKPARAMS; rewrite in_cons; apply/orP; right.
            by ins; apply RESTR; rewrite in_cons; apply/orP; right.
            {
              intros tsk0 j t HP0 JOB0 BACK0.
              ins; exploit (INVARIANT tsk0 j t); try (by ins);
                [by rewrite in_cons; apply/orP; right | intro INV].
              assert (NOINTERF: is_interfering_task_fp tsk0 higher_eq_priority tsk_i = false).
              {
                apply negbTE; rewrite negb_and; apply/orP; left.
                move: SORT => SORT.
                apply order_path_min in SORT;
                  first by move: SORT => /allP SORT; specialize (SORT tsk0 HP0).
                by apply comp_relation_trans.
              }
              by rewrite NOINTERF andFb add0n in INV.
            }
            by simpl in SORT; apply path_sorted in SORT.
            by ins; apply CONV; ins; rewrite in_cons; apply/orP; right.
          }

          move: INtsk => /eqP INtsk; subst tsk.
          intros j JOBj; desf.
          set tsk_i := job_task j; rename l into hp_bounds.
          have BOUND := bertogna_cirinei_response_time_bound_fp.
          unfold is_response_time_bound_of_task, job_has_completed_by in BOUND.
          rewrite eqn_leq; apply/andP; split; first by apply service_interval_le_cost.
          set R := per_task_rta tsk_i hp_bounds (max_steps tsk_i).
          apply leq_trans with (n := service rate sched j (job_arrival j + R)); last first.
          {
            unfold valid_sporadic_taskset, valid_sporadic_task in *.
            apply service_monotonic; rewrite leq_add2l.
            specialize (JOBPARAMS j); des; rewrite JOBPARAMS1.
            by exploit (TASKPARAMS tsk_i);
              first by rewrite in_cons; apply/orP; left; apply/eqP.
          }
          rewrite leq_eqVlt; apply/orP; left; rewrite eq_sym.
  
          apply BOUND with (job_deadline := job_deadline) (job_task := job_task) (tsk := tsk_i)
                           (higher_eq_priority := higher_eq_priority) (ts := tsk_i :: hp_tasks)
                           (hp_bounds := hp_bounds);
            clear BOUND; try (by ins); try (by apply/eqP).
            by rewrite in_cons; apply/orP; left.
            admit. (*extra lemma *)
            {
              admit. (* by IH *)
            }
            by admit. (*extra lemma*)
            by admit. (*extra lemma*)
            by ins; apply INVARIANT with (j0 := j0); ins; rewrite in_cons; apply/orP; left.
            by apply CONV; [by rewrite in_cons; apply/orP; left | by apply Heq0].
        }
      Qed.

        (*rewrite eqn_leq; apply/andP; split;
          first by apply service_interval_le_cost.
        
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
        }*)
        
      Qed.

    End Proof.

  End ResponseTimeIterationFP.

End ResponseTimeAnalysis.