Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs
        PlatformDefs WorkloadDefs SchedulabilityDefs PriorityDefs
        ResponseTimeDefs BertognaResponseTimeDefs divround helper
        ssreflect ssrbool eqtype ssrnat seq fintype bigop div path tuple.

Module ResponseTimeAnalysisEDF.

  Export Job SporadicTaskset Schedule Workload Schedulability ResponseTime Priority SporadicTaskArrival ResponseTimeAnalysis.

  Section InterferenceBoundEDF.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.

    Let task_with_response_time := (sporadic_task * time)%type.
    
    (* Assume a known response-time bound for each interfering task ... *)
    Variable R_prev: seq task_with_response_time.

    (* ... and an interval length delta. *)
    Variable delta: time.

    Section PerTask.

      Variable tsk_R: task_with_response_time.
      Let tsk_other := fst tsk_R.
      Let R_other := snd tsk_R.

      (* By combining Bertogna's interference bound for a work-conserving
         scheduler ... *)
      Let basic_interference_bound := interference_bound task_cost task_period tsk delta tsk_R.

      (* ... with and EDF-specific interference bound, ... *)
      Definition edf_specific_bound :=
        let d_tsk := task_deadline tsk in
        let e_other := task_cost tsk_other in
        let p_other := task_period tsk_other in
        let d_other := task_deadline tsk_other in
          (div_floor d_tsk p_other) * e_other +
          minn e_other ((d_tsk %% p_other) - d_other + R_other).

      
      (* Bertogna and Cirinei define the following interference bound
         under EDF scheduling. *)
      Definition interference_bound_edf :=
        minn basic_interference_bound edf_specific_bound.

    End PerTask.

    Section AllTasks.

      Definition is_interfering_task_jlfp (tsk_other: sporadic_task) :=
        tsk_other != tsk.

      (* The total interference incurred by tsk is thus bounded by: *)
      Definition total_interference_bound_edf :=
        \sum_((tsk_other, R_other) <- R_prev | is_interfering_task_jlfp tsk_other)
           interference_bound_edf (tsk_other, R_other).

    End AllTasks.

    Section Proofs.

    (* Proof of edf-specific bound should go here *)
      
    End Proofs.
    
  End InterferenceBoundEDF.

  Section ResponseTimeBound.

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
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_restricted_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task rate sched tsk.
    Let response_time_bounded_by (j: JobIn arr_seq) (R: time) :=
      completed job_cost rate sched j (job_arrival j + R).

    (* Assume a known response-time bound R is known...  *)
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable rt_bounds: seq task_with_response_time.

    (* ...for any task in the task set, ...*)
    Hypothesis H_rt_bounds_contains_all_tasks:
      unzip1 rt_bounds = ts.

    (* ..., R is a fixed-point of the response-time recurrence, ... *)
    Let I (tsk: sporadic_task) (delta: time) :=
      total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds delta.
    Hypothesis H_response_time_is_fixed_point :
      forall tsk R,
        (tsk, R) \in rt_bounds ->
        R = task_cost tsk + div_floor (I tsk R) num_cpus.
    
    (* ..., R is as larger as the task cost, ... *)
    (*Hypothesis H_response_time_bounds_ge_cost:
      forall tsk_other R,
        (tsk_other, R) \in rt_bounds -> R >= task_cost tsk_other.*)
      
    (* ..., and R is no larger than the deadline. *)
    Hypothesis H_interfering_tasks_miss_no_deadlines:
      forall tsk_other R,
        (tsk_other, R) \in rt_bounds -> R <= task_deadline tsk_other.

    (* Assume that the schedule satisfies the global scheduling
       invariant, i.e., if any job of tsk is backlogged, all
       the processors must be busy with jobs of equal or higher
       priority. *)
    Hypothesis H_global_scheduling_invariant:
      forall (tsk: sporadic_task) (j: JobIn arr_seq) (t: time),
        tsk \in ts ->
        job_task j = tsk ->
        backlogged job_cost rate sched j t ->
        count
          (fun tsk_other : sporadic_task =>
             is_interfering_task_jlfp tsk tsk_other &&
               task_is_scheduled job_task sched tsk_other t) ts = num_cpus.
        
    (* Next, we define Bertogna and Cirinei's response-time bound recurrence *)  
    Variable tsk: sporadic_task.

    Variable R: time.
    Hypothesis H_tsk_R_in_rt_bounds: (tsk, R) \in rt_bounds.

    Variable j: JobIn arr_seq.
    Hypothesis H_job_of_tsk: job_task j = tsk.

    (* Now, we prove that R bounds the response time of tsk in any schedule. *)
    Theorem bertogna_cirinei_response_time_bound_edf :
      response_time_bounded_by j R.
    Proof.
        unfold response_time_bounded_by, completed, completed_jobs_dont_execute,
             valid_sporadic_job in *.
        rename H_completed_jobs_dont_execute into COMP,
               H_valid_job_parameters into PARAMS,
               H_valid_task_parameters into TASK_PARAMS,
               H_restricted_deadlines into RESTR,
               H_rt_bounds_contains_all_tasks into HASTASKS,
               H_interfering_tasks_miss_no_deadlines into NOMISS,
               H_rate_equals_one into RATE,
               H_global_scheduling_invariant into INVARIANT,
               (*H_response_time_bounds_ge_cost into GE_COST,*)
               H_response_time_is_fixed_point into FIX,
               H_tsk_R_in_rt_bounds into INbounds,
               H_job_of_tsk into JOBtsk.

        (* Let's prove some basic facts about the tasks. *)
        assert (INts: forall tsk R, (tsk, R) \in rt_bounds -> tsk \in ts).
        {
          by intros tsk0 R0 IN0; rewrite -HASTASKS; apply/mapP; exists (tsk0, R0).
        }

        assert (GE_COST: forall tsk R, (tsk, R) \in rt_bounds -> task_cost tsk <= R).
        {
          by intros tsk0 R0 IN0; rewrite [R0](FIX tsk0); first apply leq_addr.
        }
          
        (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
        remember (job_arrival j + R) as ctime; rename Heqctime into EQc.
        assert (R = ctime - job_arrival j).
        {
          by rewrite -[R](addKn (job_arrival j)) -EQc.
        } subst R; clear EQc.
        revert tsk j JOBtsk INbounds.

        (* Now, we apply strong induction on the absolute response-time bound. *)
        induction ctime as [ctime BEFOREok] using strong_ind_lt.
        intros tsk' j' JOBtsk INbounds.
        remember (ctime - job_arrival j') as R. 
        assert (EQc: ctime = job_arrival j' + R).
        {
          rewrite HeqR addnBA; first by rewrite addnC -addnBA // subnn addn0.
          specialize (GE_COST tsk' R INbounds).
          rewrite leqNgt; apply/negP; red; intros BUG.
          apply ltnW in BUG; rewrite -subn_eq0 in BUG; move: BUG => /eqP BUG.
          rewrite HeqR BUG leqNgt in GE_COST.
          exploit (TASK_PARAMS tsk');
            [by ins; apply (INts tsk' R) | unfold is_valid_sporadic_task; intro PARAMStsk; des].
          by unfold task_cost_positive in PARAMStsk; rewrite PARAMStsk in GE_COST.
        } subst ctime; clear HeqR.
        
        (* According to the IH, all jobs with absolute response-time bound t < (job_arrival j + R)
           have correct response-time bounds.
           Now, we prove the same result for job j by contradiction.
           Assume that (job_arrival j + R) is not a response-time bound for job j. *)
        destruct (completed job_cost rate sched j' (job_arrival j' + R)) eqn:COMPLETED;
          first by move: COMPLETED => /eqP COMPLETED; rewrite COMPLETED eq_refl.
        apply negbT in COMPLETED; exfalso.

        (* Let x be the cumulative time during [job_arrival j, job_arrival j + R)
           where a job j is interfered with by tsk_k, ... *)
        set x := fun tsk_other =>
               if (tsk_other \in ts) && is_interfering_task_jlfp tsk' tsk_other then
                  task_interference job_cost job_task rate sched j'
                     (job_arrival j') (job_arrival j' + R) tsk_other
               else 0.

        (* ..., and let X be the cumulative time in the same interval where j is interfered
           with by any task. *)
        set X :=
          total_interference job_cost rate sched j' (job_arrival j') (job_arrival j' + R).
        
        (* Let's recall the interference bound under EDF scheduling. *)
        set I_edf := fun (tup: task_with_response_time) =>
          let (tsk_k, R_k) := tup in
            if is_interfering_task_jlfp tsk' tsk_k then
              interference_bound_edf task_cost task_period task_deadline tsk' R (tsk_k, R_k)
            else 0.
        
        (* Since j has not completed, recall the time when it is not
           executing is the total interference. *)
        exploit (complement_of_interf_equals_service job_cost rate sched j' (job_arrival j')
                                                     (job_arrival j' + R));
          last intro EQinterf; ins; unfold has_arrived;
          first by apply leqnn.
        rewrite {2}[_ + R]addnC -addnBA // subnn addn0 in EQinterf.
        
        (* In order to derive a contradiction, we first show that per-task
           interference x_k is no larger than the basic interference bound (based on W). *)
        assert (BASICBOUND:
                  forall tsk_k R_k,
                    (tsk_k, R_k) \in rt_bounds ->
                                     x tsk_k <= W task_cost task_period tsk_k R_k R).
        {
          intros tsk_k R_k INBOUNDSk.
          unfold x.
          destruct ((tsk_k \in ts) && is_interfering_task_jlfp tsk' tsk_k) eqn:INTERFk;
            last by done.
          move: INTERFk => /andP [INk INTERFk].
          unfold task_interference.
          apply leq_trans with (n := workload job_task rate sched tsk_k
                                     (job_arrival j') (job_arrival j' + R)).
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
            apply workload_bounded_by_W with (task_deadline0 := task_deadline) (job_cost0 := job_cost) (job_deadline0 := job_deadline); try (by ins); last 2 first;
              [ by apply GE_COST
              | by ins; apply BEFOREok with (tsk := tsk_k); try rewrite addKn
              | by ins; rewrite RATE
              | by ins; apply TASK_PARAMS
              | by ins; apply RESTR |].
            red; move => j'' /eqP JOBtsk' LEdl; unfold job_misses_no_deadline.
            specialize (PARAMS j''); des; rewrite PARAMS1 JOBtsk'.
            apply completion_monotonic with (t := job_arrival j'' + (R_k)); ins;
              first by rewrite leq_add2l; apply NOMISS.
            apply BEFOREok with (tsk := tsk_k); try (by done); last by rewrite addKn.
            apply leq_ltn_trans with (n := job_arrival j'' + job_deadline j''); last by done.
            by rewrite leq_add2l PARAMS1 JOBtsk'; apply NOMISS.
          }
        }

        assert (EDFBOUND:
                forall tsk_k R_k,
                  (tsk_k, R_k) \in rt_bounds ->
                  x tsk_k <= edf_specific_bound task_cost task_period task_deadline tsk' (tsk_k, R_k)).
        {
          intros tsk_k R_k INBOUNDSk.
          admit.
        }
        
        (* In the remaining of the proof, we show that the workload bound
           W_k is less than the task interference x (contradiction!).
           For that, we require a few auxiliary lemmas: *)

        (* 1) We show that the total interference X >= R - e_k + 1.
              Otherwise, job j would have completed on time. *)
        assert (INTERF: X >= R - task_cost tsk' + 1).
        {
          unfold completed in COMPLETED.
          rewrite addn1.
          move: COMPLETED; rewrite neq_ltn; move => /orP COMPLETED; des;
            last first.
          {
            apply (leq_ltn_trans (COMP j' (job_arrival j' + R))) in COMPLETED.
            by rewrite ltnn in COMPLETED.
          }
          apply leq_trans with (n := R - service rate sched j' (job_arrival j' + R)); last first.
          {
            unfold service; rewrite service_before_arrival_eq_service_during; ins.
            rewrite EQinterf.
            rewrite subKn; first by ins.
            {
              unfold total_interference.
              rewrite -{1}[_ j']add0n big_addn addnC -addnBA // subnn addn0.
              rewrite -{2}[R]subn0 -[R-_]mul1n -[1*_]addn0 -iter_addn.
              by rewrite -big_const_nat leq_sum //; ins; apply leq_b1.
            }
          }
          {
            apply ltn_sub2l; last first.
            {
              apply leq_trans with (n := job_cost j'); first by ins.
              by rewrite -JOBtsk; specialize (PARAMS j'); des; apply PARAMS0.
            }
            apply leq_trans with (n := job_cost j'); first by ins.
            apply leq_trans with (n := task_cost tsk');
              first by rewrite -JOBtsk; specialize (PARAMS j'); des; apply PARAMS0.
            by rewrite [R](FIX tsk'); first by apply leq_addr.
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
          destruct (backlogged job_cost rate sched j' t) eqn:BACK;
            last by rewrite (eq_bigr (fun i => 0));
              [by rewrite big_const_seq iter_addn mul0n addn0 mul0n|by ins].
          rewrite big_mkcond mul1n /=.
          rewrite (eq_bigr (fun i =>
                              (if (i \in ts) && is_interfering_task_jlfp tsk' i &&
                                             task_is_scheduled job_task sched i t then 1 else 0))); last first.
          {
            ins; destruct ((i \in ts) && is_interfering_task_jlfp tsk' i) eqn:IN;
              [by rewrite andTb | by rewrite andFb].
          }
          rewrite (eq_bigr (fun i => if (i \in ts) && true then (if is_interfering_task_jlfp tsk' i && task_is_scheduled job_task sched i t then 1 else 0) else 0));
            last by ins; destruct (i \in ts) eqn:IN; rewrite ?andTb ?andFb.
          rewrite -big_mkcond -big_seq_cond -big_mkcond sum1_count.
          by apply (INVARIANT tsk' j'); try (by done); apply (INts tsk' R).   
        }
        
        (* 3) Next, we prove the auxiliary lemma from the paper. *)
        assert (MINSERV: \sum_(tsk_k <- ts) x tsk_k >=
                         (R - task_cost tsk' + 1) * num_cpus ->
               \sum_(tsk_k <- ts) minn (x tsk_k) (R - task_cost tsk' + 1) >=
               (R - task_cost tsk' + 1) * num_cpus).
        {
          intro SUMLESS.
          set more_interf := fun tsk_k => x tsk_k >= R - task_cost tsk' + 1.
          rewrite [\sum_(_ <- _) minn _ _](bigID more_interf) /=.
          unfold more_interf, minn.
          rewrite [\sum_(_ <- _ | R - _ + _ <= _)_](eq_bigr (fun i => R - task_cost tsk' + 1));
            last first.
          {
            intros i COND; rewrite leqNgt in COND.
            destruct (R - task_cost tsk' + 1 > x i); ins.
          }
          rewrite [\sum_(_ <- _ | ~~_)_](eq_big (fun i => x i < R - task_cost tsk' + 1)
                                                (fun i => x i));
            [| by red; ins; rewrite ltnNge
             | by intros i COND; rewrite -ltnNge in COND; rewrite COND].

          (* Case 1 |A| = 0 *)
          destruct (~~ has (fun i => R - task_cost tsk' + 1 <= x i) ts) eqn:HASa.
          {
            rewrite [\sum_(_ <- _ | _ <= _) _]big_hasC; last by apply HASa.
            rewrite big_seq_cond; move: HASa => /hasPn HASa.
            rewrite add0n (eq_bigl (fun i => (i \in ts) && true));
              last by red; intros tsk_k; destruct (tsk_k \in ts) eqn:INk;
                [by rewrite andTb ltnNge; apply HASa | by rewrite andFb].
            by rewrite -big_seq_cond.
          } apply negbFE in HASa.
          
          set cardA := count (fun i => R - task_cost tsk' + 1 <= x i) ts.
          destruct (cardA >= num_cpus) eqn:CARD.
          {
            apply leq_trans with ((R - task_cost tsk' + 1) * cardA);
              first by rewrite leq_mul2l; apply/orP; right.
            unfold cardA; rewrite -sum1_count big_distrr /=.
            rewrite -[\sum_(_ <- _ | _) _]addn0.
            by apply leq_add; [by apply leq_sum; ins; rewrite muln1|by ins].
          } apply negbT in CARD; rewrite -ltnNge in CARD.

          assert (GEsum: \sum_(i <- ts | x i < R - task_cost tsk' + 1) x i >=
                           (R - task_cost tsk' + 1) * (num_cpus - cardA)).
          {
            set some_interference_A := fun t =>
              backlogged job_cost rate sched j' t &&
              has (fun tsk_k => (is_interfering_task_jlfp tsk' tsk_k &&
                              ((x tsk_k) >= R - task_cost tsk' + 1) &&
                              task_is_scheduled job_task sched tsk_k t)) ts.      
            set total_interference_B := fun t =>
              backlogged job_cost rate sched j' t *
              count (fun tsk_k =>
                is_interfering_task_jlfp tsk' tsk_k &&
                ((x tsk_k) < R - task_cost tsk' + 1) &&
                task_is_scheduled job_task sched tsk_k t) ts.

            apply leq_trans with ((\sum_(job_arrival j' <= t < job_arrival j' + R)
                                      some_interference_A t) * (num_cpus - cardA)).
            {
              rewrite leq_mul2r; apply/orP; right.
              move: HASa => /hasP HASa; destruct HASa as [tsk_a INa LEa].
              apply leq_trans with (n := x tsk_a); first by apply LEa.
              unfold x, task_interference, some_interference_A.
              destruct ((tsk_a \in ts) && is_interfering_task_jlfp tsk' tsk_a) eqn:INTERFa;
                last by ins.
              move: INTERFa => /andP INTERFa; des.
              apply leq_sum; ins.
              destruct (backlogged job_cost rate sched j' i);
                [rewrite 2!andTb | by ins].
              destruct (task_is_scheduled job_task sched tsk_a i) eqn:SCHEDa;
                [apply eq_leq; symmetry | by ins].
              apply/eqP; rewrite eqb1.
              apply/hasP; exists tsk_a; first by ins.
              apply/andP; split; last by ins.
              by apply/andP; split; ins.
            }
            apply leq_trans with (\sum_(job_arrival j' <= t < job_arrival j' + R)
                                     total_interference_B t).
            {
              rewrite big_distrl /=.
              apply leq_sum; intros t _.
              unfold some_interference_A, total_interference_B. 
              destruct (backlogged job_cost rate sched j' t) eqn:BACK;
                [rewrite andTb mul1n | by ins].
              destruct (has (fun tsk_k : sporadic_task =>
                       is_interfering_task_jlfp tsk' tsk_k &&
                       (R - task_cost tsk' + 1 <= x tsk_k) &&
                       task_is_scheduled job_task sched tsk_k t) ts) eqn:HAS;
                last by ins.
              rewrite mul1n; move: HAS => /hasP HAS.
              destruct HAS as [tsk_k INk H].
              move: H => /andP [/andP [INTERFk LEk] SCHEDk].
              
              exploit INVARIANT;
                [by apply (INts tsk' R) | by apply JOBtsk | by apply BACK | intro COUNT].

              unfold cardA.
              set interfering_tasks_at_t :=
                [seq tsk_k <- ts | is_interfering_task_jlfp tsk' tsk_k &&
                                  task_is_scheduled job_task sched tsk_k t].

              rewrite -(count_filter (fun i => true)) in COUNT.
              fold interfering_tasks_at_t in COUNT.
              rewrite count_predT in COUNT.
              apply leq_trans with (n := num_cpus -
                                      count (fun i => is_interfering_task_jlfp tsk' i &&
                                                    (x i >= R -  task_cost tsk' + 1) &&
                                                    task_is_scheduled job_task sched i t) ts).
              {
                apply leq_sub2l.
                rewrite -2!sum1_count big_mkcond /=.
                rewrite [\sum_(_ <- _ | _ <= _)_]big_mkcond /=.
                apply leq_sum; intros i _.
                unfold x; destruct (is_interfering_task_jlfp tsk' i);
                  [rewrite andTb | by rewrite 2!andFb].
                destruct (task_is_scheduled job_task sched i t);
                  [by rewrite andbT | by rewrite andbF].
              }

              rewrite leq_subLR.
              rewrite -count_predUI.
              apply leq_trans with (n :=
                count (predU (fun i : sporadic_task =>
                                is_interfering_task_jlfp tsk' i &&
                                (R - task_cost tsk' + 1 <= x i) &&
                                task_is_scheduled job_task sched i t)
                             (fun tsk_k0 : sporadic_task =>
                                is_interfering_task_jlfp tsk' tsk_k0 &&
                                (x tsk_k0 < R - task_cost tsk' + 1) &&
                                task_is_scheduled job_task sched tsk_k0 t))
                      ts); last by apply leq_addr.
              apply leq_trans with (n := size interfering_tasks_at_t);
                first by rewrite COUNT.
              unfold interfering_tasks_at_t.
              rewrite -count_predT count_filter.
              rewrite leq_eqVlt; apply/orP; left; apply/eqP.
              apply eq_count; red; simpl.
              intros i.
              destruct (is_interfering_task_jlfp tsk' i),
                       (task_is_scheduled job_task sched i t);
                rewrite 3?andTb ?andFb ?andbF ?andbT /=; try ins.
              by rewrite leqNgt orNb. 
            }
            {
              unfold x at 2, task_interference.
              rewrite [\sum_(i <- ts | _) _](eq_bigr
                (fun i => \sum_(job_arrival j' <= t < job_arrival j' + R)
                             (i \in ts) && is_interfering_task_jlfp tsk' i &&
                             backlogged job_cost rate sched j' t &&
                             task_is_scheduled job_task sched i t));
                last first.
              {
                ins; destruct ((i \in ts) && is_interfering_task_jlfp tsk' i) eqn:INTERi;
                  first by move: INTERi => /andP [_ INTERi]; apply eq_bigr; ins; rewrite INTERi andTb.
                by rewrite (eq_bigr (fun i => 0));
                  [by rewrite big_const_nat iter_addn mul0n addn0 | by ins].
              }
              {
                rewrite exchange_big /=; apply leq_sum; intros t _.
                unfold total_interference_B.
                destruct (backlogged job_cost rate sched j' t); last by ins.
                rewrite mul1n -sum1_count.
                rewrite big_seq_cond big_mkcond [\sum_(i <- ts | _ < _) _]big_mkcond.
                apply leq_sum; ins.
                destruct (x i<R - task_cost tsk' + 1);
                  [by rewrite 2!andbT andbA | by rewrite 2!andbF].
              }
            }
          }
          
          rewrite big_const_seq iter_addn addn0; fold cardA.
          apply leq_trans with (n := (R-task_cost tsk'+1)*cardA +
                                     (R-task_cost tsk'+1)*(num_cpus-cardA));
            last by rewrite leq_add2l.
          by rewrite -mulnDr subnKC //; apply ltnW.
        }

        (* 4) Now, we prove that the Bertogna's interference bound
              is not enough to cover the sum of the "minimum" term over
              all tasks (artifact of the proof by contradiction). *)
        assert (SUM: \sum_((tsk_k, R_k) <- rt_bounds)
                     minn (x tsk_k) (R - task_cost tsk' + 1) >
                     I tsk' R). 
        {
          apply leq_trans with (n := \sum_(tsk_k <- ts) minn (x tsk_k) (R - task_cost tsk' + 1));
            last first.
          {
            rewrite (eq_bigr (fun i => minn (x (fst i)) (R - task_cost tsk' + 1)));
              last by ins; destruct i.
            apply leq_trans with (n := \sum_(tsk_k <- ts | is_interfering_task_jlfp tsk' tsk_k) minn (x tsk_k) (R - task_cost tsk' + 1)).
          {
            rewrite [\sum_(_ <- _ | is_interfering_task_jlfp _ _)_]big_mkcond eq_leq //.
            apply eq_bigr; intros i _; unfold x.
            destruct (is_interfering_task_jlfp tsk' i); last by rewrite andbF min0n.
            by rewrite andbT; destruct (i \in ts); last by rewrite min0n.
          }
            have MAP := big_map (fun x => fst x) (fun i => true) (fun i => minn (x i) (R - task_cost tsk' + 1)).
            unfold unzip1 in *; rewrite -MAP HASTASKS.
            rewrite big_mkcond /= big_seq_cond [\sum_(_ <- _ | true)_]big_seq_cond.
            apply leq_sum; intro i; rewrite andbT; intro INi.
            unfold x; rewrite INi andTb.
            by destruct (is_interfering_task_jlfp tsk' i).
          }
          apply ltn_div_trunc with (d := num_cpus); first by apply H_at_least_one_cpu.
          rewrite -(ltn_add2l (task_cost tsk')) -FIX; last by done.
          rewrite -addn1 -leq_subLR.
          rewrite -[R + 1 - _]subh1; last by apply GE_COST.
          rewrite leq_divRL; last by apply H_at_least_one_cpu.
          apply MINSERV.
          apply leq_trans with (n := X * num_cpus); last by rewrite ALLBUSY.
          by rewrite leq_mul2r; apply/orP; right; apply INTERF.
        }
      
        (* 5) This implies that there exists a tuple (tsk_k, R_k) such that
              min (x_k, R - e_i + 1) > min (W_k, R - e_i + 1). *)
        assert (EX:
            has (fun tup : task_with_response_time => let (tsk_k, R_k) := tup in
                           (tsk_k \in ts) && is_interfering_task_jlfp tsk' tsk_k &&
                              (minn (x tsk_k) (R - task_cost tsk' + 1)  >
                              I_edf (tsk_k, R_k)))
                 rt_bounds).
        {
          unfold I_edf; apply/negP; unfold not; intro NOTHAS.
          move: NOTHAS => /negP /hasPn ALL.
          rewrite -[_ < _]negbK in SUM.
          move: SUM => /negP SUM; apply SUM; rewrite -leqNgt.
          unfold I, total_interference_bound_edf.
          rewrite [\sum_(i <- _ | let '(tsk_other, _) := i in _)_]big_mkcond.
          rewrite big_seq_cond [\sum_(i <- _ | true) _]big_seq_cond.
          apply leq_sum; move => tsk_k /andP [INBOUNDSk _]; destruct tsk_k as [tsk_k R_k].
          assert (INtsk: tsk_k \in ts). by apply (INts tsk_k R_k).
          specialize (ALL (tsk_k, R_k) INBOUNDSk).
          unfold interference_bound_edf.
          destruct (is_interfering_task_jlfp tsk' tsk_k) eqn:INTERFk;
            last by unfold x; rewrite INTERFk andbF min0n.
          rewrite leq_min; apply/andP; split.
          {
            unfold interference_bound; rewrite leq_min; apply/andP; split;
              last by rewrite geq_minr.
            apply leq_trans with (n := x tsk_k); first by rewrite geq_minl.
            by apply BASICBOUND.
          }
          {
            apply leq_trans with (n := x tsk_k); first by rewrite geq_minl.
            admit.
          }
        }

        (* For this particular task, we show that x_k > W_k.
           This contradicts the previous claim. *)
        move: EX => /hasP EX; destruct EX as [tup_k HPk LTmin].
        destruct tup_k as [tsk_k R_k]; simpl in LTmin.
        move: LTmin => /andP [INTERFk LTmin]; move: (INTERFk) => /andP [INk INTERFk'].
        rewrite INTERFk' in LTmin.
        unfold interference_bound_edf, interference_bound in LTmin.
        rewrite minnAC in LTmin; apply min_lt_same in LTmin.
        unfold minn in LTmin; clear -LTmin EDFBOUND BASICBOUND JOBtsk HPk; desf.
        {
          specialize (BASICBOUND tsk_k R_k HPk).
          by apply (leq_ltn_trans BASICBOUND) in LTmin; rewrite ltnn in LTmin. 
        }
        {
          specialize (EDFBOUND tsk_k R_k HPk).
          by apply (leq_ltn_trans EDFBOUND) in LTmin; rewrite ltnn in LTmin.
        }
    Qed.

  End ResponseTimeBound.

End ResponseTimeAnalysisEDF.