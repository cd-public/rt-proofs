Require Import Vbase task job task_arrival schedule platform workload
               bertogna_fp_theory schedulability priority interference
               platform response_time util_divround util_lemmas
               ssreflect ssrbool eqtype ssrnat seq fintype bigop div path tuple.

Module ResponseTimeAnalysisGuan.

  Import Job SporadicTaskset ScheduleOfTaskWithJitter Schedulability ResponseTime Priority SporadicTaskArrival Interference Platform.
  Export Workload ResponseTimeAnalysis.

  Section InterferenceBoundGuan.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.

    Variable num_cpus: nat.
    Variable higher_eq_priority: fp_policy sporadic_task.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.

    Let task_with_response_time := (sporadic_task * time)%type.
    
    (* Assume a known response-time bound for each interfering task ... *)
    Variable R_prev: seq task_with_response_time.

    (* ... and an interval length delta. *)
    Variable delta: time.

    Section TasksetPartition.

      (* Let's filter the list of task and response-times so that it only has interfering tasks. *)
      Let interfering_tasks :=
        [seq (tsk_other, R) <- R_prev | is_interfering_task_fp higher_eq_priority tsk tsk_other].

      (* After that, we list all possible pairs of subsets of that list:
           [(subset0, subset1), (subset0, subset2), ...]*)
      Let all_combinations :=
        allpairs (fun S1 S2 => (S1, S2))
                 (powerset interfering_tasks)
                 (powerset interfering_tasks).

      (* Finally, we let (NC, CI) be all the pairs of subsets that are partitions
         and such that the number of carried-in tasks is at most num_cpus - 1. *)
      Definition valid_NC_CI_partitions :=
        [seq (NC, CI) <- all_combinations | no_intersection NC CI &&
                                            (size CI <= num_cpus - 1)].
    End TasksetPartition.

    Section InterferenceBoundCarry.

      Variable tsk_R: task_with_response_time.
      Let tsk_other := fst tsk_R.
      Let R_other := snd tsk_R.
    
      Definition interference_bound_NC :=
        minn (W_NC task_cost task_period tsk_other delta) (delta - task_cost tsk + 1).

      Definition interference_bound_CI :=
        minn (W_CI task_cost task_period tsk_other R_other delta) (delta - task_cost tsk + 1).

    End InterferenceBoundCarry.
    
    (* Guan et al.'s analysis defines an interference bound based on the maximum interference
       across all partitions of (NC, CI), i.e., non-carried-in and carried-in tasks.
       For the sake of simplicity, we compute the maximum by enumeration, instead of using
       a linear-time algorithm. *)
    Definition guan_interference_bound :=
      \max_((NC, CI) <- valid_NC_CI_partitions)
       (\sum_((tsk_other, R) <- NC) interference_bound_NC (tsk_other,R) +
         \sum_((tsk_other, R) <- CI) interference_bound_CI (tsk_other,R)).

  End InterferenceBoundGuan.

  Section ResponseTimeBoundGuan.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    
    (* Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.

    (* ... in which jobs arrive sporadically and have valid parameters. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period arr_seq job_task.
    Hypothesis H_valid_job_parameters:
      forall (j: JobIn arr_seq),
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* Consider any schedule such that...*)
    Variable num_cpus: nat.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    (* ...jobs do not execute before their arrival times nor longer
       than their execution costs. *)
    Hypothesis H_jobs_execute_after_jitter:
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
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
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
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable hp_bounds: seq task_with_response_time.
    
    (* Assume there exists a fixed task priority. *)
    Variable higher_eq_priority: fp_policy sporadic_task.

    Let interferes_with_tsk := is_interfering_task_fp higher_eq_priority tsk.
      
    (* Assume that hp_bounds has exactly the tasks that interfere with tsk,... *)
    Hypothesis H_hp_bounds_has_interfering_tasks:
      [seq tsk_hp <- ts | interferes_with_tsk tsk_hp] = unzip1 hp_bounds.

    (* ...and that all values in the pairs contain valid response-time bounds *)
    Hypothesis H_response_time_of_interfering_tasks_is_known:
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
               is_interfering_task_fp higher_eq_priority tsk tsk_other &&
               task_is_scheduled job_task sched tsk_other t) ts = num_cpus.

      (* Next, we define Bertogna and Cirinei's response-time bound recurrence *)
      
      (* Let R be any time. *)
      Variable R: time.

      (* Guan et al.'s response-time analysis states that
         if R is a fixed-point of the following recurrence, ... *)
      Let I := guan_interference_bound task_cost task_period num_cpus
                             higher_eq_priority tsk hp_bounds R.
      Hypothesis H_response_time_recurrence_holds :
        R = task_cost tsk + (div_floor I num_cpus).

      (*..., and R is no larger than the deadline of tsk, ...*)
      Hypothesis H_response_time_no_larger_than_deadline:
        R <= task_deadline tsk.

      (* ..., then R bounds the response time of tsk. *)
      Theorem guan_response_time_bound_fp :
        is_response_time_bound tsk R.
      Proof.
        unfold is_response_time_bound, is_response_time_bound_of_task,
               completed, completed_jobs_dont_execute,
               valid_sporadic_job_with_jitter, valid_sporadic_job in *.
        rename H_completed_jobs_dont_execute into COMP,
               H_response_time_recurrence_holds into REC,
               H_valid_job_parameters into PARAMS,
               H_valid_task_parameters into TASK_PARAMS,
               H_restricted_deadlines into RESTR,
               H_response_time_of_interfering_tasks_is_known into RESP,
               H_hp_bounds_has_interfering_tasks into HAS,
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
                     hp_tsk (job_arrival j) (job_arrival j + R)
          else 0.
        set X := total_interference job_cost rate sched j (job_arrival j) (job_arrival j + R).

        admit.

        (*(* Let's recall the workload bound under FP scheduling. *)
        set workload_bound := fun (tup: task_with_response_time) =>
          let (tsk_k, R_k) := tup in
            if interferes_with_tsk tsk_k then
              W_jitter task_cost task_period task_jitter tsk_k R_k R
            else 0.  
        
        (* Now we start the proof. Assume by contradiction that job j
           is not complete at time (job_arrival j + R). *)
        destruct (completed job_cost rate sched j (job_arrival j + R')) eqn:COMPLETED;
          first by move: COMPLETED => /eqP COMPLETED; rewrite COMPLETED eq_refl.
        apply negbT in COMPLETED; exfalso.

        (* Note that j cannot have completed by job_arrival j + R either. *)
        assert (COMPLETED': ~~ completed job_cost rate sched j (job_arrival j + R)).
        {
          apply/negP; unfold not; intro BUG.
          apply completion_monotonic with (t' := job_arrival j + R') in BUG;
            try (by ins);
            [ by rewrite BUG in COMPLETED
            | by unfold R'; rewrite addnA; apply leq_addr].
        }
        
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
                Lemma exists_R :
        forall hp_tsk,
          hp_tsk \in ts ->
          interferes_with_tsk hp_tsk ->
          exists R,
            (hp_tsk, R) \in hp_bounds.
      Proof.
        intros hp_tsk IN INTERF.
        rewrite -[hp_bounds]zip_unzip; apply exists_unzip2.
        by rewrite zip_unzip -H_all_interfering_tasks_in_hp_bounds mem_filter; apply/andP.
      Qed.      

          exploit (exists_R tsk_k); [by ins | by ins | intro INhp; des].
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
            apply workload_bounded_by_W_jitter with (task_deadline0 := task_deadline) (job_cost0 := job_cost) (job_deadline0 := job_deadline) (job_jitter0 := job_jitter); ins;
              [ by rewrite RATE
              | by apply TASK_PARAMS
              | by apply RESTR
              | by red; red; ins; apply (RESP tsk_k)  
              | by apply GE_COST |].
            red; red; move => j' /eqP JOBtsk' _;
            unfold job_misses_no_deadline.
            specialize (PARAMS j'); des.
            rewrite PARAMS2 JOBtsk'.
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
          unfold completed in COMPLETED'; rewrite addn1.
          move: COMPLETED'; rewrite neq_ltn; move => /orP COMPLETED'; des;
            last first.
          {
            apply (leq_ltn_trans (COMP j (job_arrival j + R))) in COMPLETED'.
            by rewrite ltnn in COMPLETED'.
          }
          apply leq_trans with (n := R - service rate sched j (job_arrival j + R)); last first.
          {
            unfold service.
            rewrite service_before_arrival_eq_service_during; ins;
              last by apply arrival_before_jitter with (job_jitter0 := job_jitter).
            rewrite EQinterf subKn; first by ins.
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
              by rewrite -JOBtsk; specialize (PARAMS j); des; apply PARAMS1.
            }
            apply leq_trans with (n := job_cost j); first by ins.
            apply leq_trans with (n := task_cost tsk);
              first by rewrite -JOBtsk; specialize (PARAMS j); des; apply PARAMS1.
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
              [by rewrite andTb | by rewrite andFb].
          }
          rewrite (eq_bigr (fun i => if (i \in ts) && true then (if interferes_with_tsk i && task_is_scheduled job_task sched i t then 1 else 0) else 0));
            last by ins; destruct (i \in ts) eqn:IN; rewrite ?andTb ?andFb.
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
                last by ins.
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
              destruct (has (fun tsk_k : sporadic_task_with_jitter =>
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
                count (predU (fun i : sporadic_task_with_jitter =>
                                interferes_with_tsk i &&
                                (R - task_cost tsk + 1 <= x i) &&
                                task_is_scheduled job_task sched i t)
                             (fun tsk_k0 : sporadic_task_with_jitter =>
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
                ins; destruct ((i \in ts) && interferes_with_tsk i) eqn:INTERi;
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
                       I).
        {
          apply leq_trans with (n := \sum_(tsk_k <- ts) minn (x tsk_k) (R - task_cost tsk + 1));
            last first.
          {
            rewrite (eq_bigr (fun i => minn (x (fst i)) (R - task_cost tsk + 1)));
              last by ins; destruct i.
            apply leq_trans with (n := \sum_(tsk_k <- ts | interferes_with_tsk tsk_k) minn (x tsk_k) (R - task_cost tsk + 1)).
            {
              rewrite [\sum_(_ <- _ | interferes_with_tsk _)_]big_mkcond eq_leq //.
              apply eq_bigr; intros i _; unfold x.
              by destruct (interferes_with_tsk i); rewrite ?andbT ?andbF ?min0n.
            }
            have MAP := big_map (fun x => fst x) (fun i => true) (fun i => minn (x i) (R - task_cost tsk + 1)).
            by unfold unzip1 in *; rewrite -MAP -HAS -big_filter.
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
          unfold I, total_interference_bound_fp_jitter.
          rewrite [\sum_(i <- _ | let '(tsk_other, _) := i in _)_]big_mkcond.
          rewrite big_seq_cond [\sum_(i <- _ | true) _]big_seq_cond.
          apply leq_sum; move => tsk_k /andP [HPk _]; destruct tsk_k as [tsk_k R_k].
          specialize (ALL (tsk_k, R_k) HPk).
          unfold interference_bound, workload_bound, x in *.
          fold (interferes_with_tsk); destruct (interferes_with_tsk tsk_k) eqn:INTERFk;
            [rewrite andbT in ALL; rewrite andbT | by rewrite andbF min0n].
          destruct (tsk_k \in ts) eqn:INk; last by rewrite min0n.
          by rewrite andTb -leqNgt in ALL.
        }
        
        (* For this particular task, we show that x_k > W_k.
           This contradicts the previous claim. *)
        move: EX => /hasP EX; destruct EX as [tup_k HPk LTmin].
        destruct tup_k as [tsk_k R_k]; simpl in LTmin.
        move: LTmin => /andP [INTERFk LTmin]; move: (INTERFk) => /andP [INk INTERFk'].
        rewrite INTERFk' in LTmin; unfold minn at 1 in LTmin.
        destruct (W_jitter task_cost task_period task_jitter tsk_k R_k R < R - task_cost tsk + 1); rewrite leq_min in LTmin;
          last by move: LTmin => /andP [_ BUG]; rewrite ltnn in BUG.
        move: LTmin => /andP [BUG _]; des.
        specialize (WORKLOAD tsk_k INTERFk R_k HPk).
        apply leq_ltn_trans with (p := x tsk_k) in WORKLOAD; first by rewrite ltnn in WORKLOAD.
        by unfold workload_bound; rewrite INTERFk'; apply BUG.
         *)
      Qed.

  End ResponseTimeBoundGuan.

End ResponseTimeAnalysisGuan.