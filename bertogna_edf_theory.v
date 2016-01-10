Require Import Vbase task job task_arrival schedule platform interference
        workload workload_bound schedulability priority response_time
        bertogna_fp_theory interference_bound_edf util_divround util_lemmas
        ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisEDF.

  Import Job SporadicTaskset ScheduleOfSporadicTask Workload Schedulability ResponseTime
         Priority SporadicTaskArrival WorkloadBound EDFSpecificBound ResponseTimeAnalysisFP.

  (* In the following section, we define Bertogna and Cirinei's
     interference bound for EDF scheduling. *)
  Section TotalInterferenceBoundEDF.

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
      Let basic_interference_bound := interference_bound_fp task_cost task_period tsk delta tsk_R.

      (* ... with and EDF-specific interference bound, ... *)
      Let edf_specific_bound := edf_specific_interference_bound task_cost task_period task_deadline tsk tsk_other R_other.

      (* Bertogna and Cirinei define the following interference bound
         under EDF scheduling. *)
      Definition interference_bound_edf :=
        minn basic_interference_bound edf_specific_bound.

    End PerTask.

    Section AllTasks.

      Let interferes_with_tsk := is_interfering_task_jlfp tsk.
      
      (* The total interference incurred by tsk is bounded by the sum
         of individual task interferences. *)
      Definition total_interference_bound_edf :=
        \sum_((tsk_other, R_other) <- R_prev | interferes_with_tsk tsk_other)
           interference_bound_edf (tsk_other, R_other).

    End AllTasks.

  End TotalInterferenceBoundEDF.

  (* In this section, we prove that Bertogna and Cirinei's RTA yields
     safe response-time bounds. *)
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

    (* In order not to overcount job interference, we assume that
       jobs of the same task do not execute in parallel.
       Note that under EDF, this is equivalent to task precedence
       constraints.
       This is required because our proof uses a definition of
       interference based on the sum of the individual contributions
       of each job: I_total = I_j1 + I_j2 + ... *)
    Hypothesis H_no_intra_task_parallelism:
      jobs_of_same_task_dont_execute_in_parallel job_task sched.

    (* Assume that we have a task set where all tasks have valid
       parameters and restricted deadlines. *)
    Variable ts: taskset_of sporadic_task.
    Hypothesis all_jobs_from_taskset:
      forall (j: JobIn arr_seq), job_task j \in ts.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_restricted_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task rate sched tsk.
    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_cost job_task tsk rate sched.

    (* Assume a known response-time bound R is known...  *)
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable rt_bounds: seq task_with_response_time.

    (* ...for any task in the task set. *)
    Hypothesis H_rt_bounds_contains_all_tasks: unzip1 rt_bounds = ts.

    (* Also, assume that R is a fixed-point of the response-time recurrence, ... *)
    Let I (tsk: sporadic_task) (delta: time) :=
      total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds delta.
    Hypothesis H_response_time_is_fixed_point :
      forall tsk R,
        (tsk, R) \in rt_bounds ->
        R = task_cost tsk + div_floor (I tsk R) num_cpus.
    
    (* ..., and R is no larger than the deadline. *)
    Hypothesis H_tasks_miss_no_deadlines:
      forall tsk_other R,
        (tsk_other, R) \in rt_bounds -> R <= task_deadline tsk_other.

    (* Assume that the schedule satisfies the global scheduling invariant
       for EDF, i.e., if any job of tsk is backlogged, every processor
       must be busy with jobs with no larger absolute deadline. *)
    Let higher_eq_priority := @EDF Job arr_seq job_deadline. (* TODO: implicit params broken *)    
    Hypothesis H_global_scheduling_invariant:
      JLFP_JLDP_scheduling_invariant_holds job_cost num_cpus rate sched higher_eq_priority.


    (* In order to prove that R is a response-time bound, we first present some lemmas. *)
    Section Lemmas.

      (* Let (tsk, R) be any task to be analyzed, with its response-time bound R. *)
      Variable tsk: sporadic_task.
      Variable R: time.
      Hypothesis H_tsk_R_in_rt_bounds: (tsk, R) \in rt_bounds.

      (* Consider any job j of tsk. *)
      Variable j: JobIn arr_seq.
      Hypothesis H_job_of_tsk: job_task j = tsk.

      (* Assume that job j did not complete on time, ... *)
      Hypothesis H_j_not_completed: ~~ completed job_cost rate sched j (job_arrival j + R).

      (* and that it is the first job not to satisfy its response-time bound. *)
      Hypothesis H_all_previous_jobs_completed_on_time :
        forall (j_other: JobIn arr_seq) tsk_other R_other,
          job_task j_other = tsk_other ->
          (tsk_other, R_other) \in rt_bounds ->
          job_arrival j_other + R_other < job_arrival j + R ->
          completed job_cost rate sched j_other (job_arrival j_other + R_other).

      (* Let's call x the interference incurred by job j due to tsk_other, ...*)
      Let x (tsk_other: sporadic_task) :=
        task_interference job_cost job_task rate sched j
                          tsk_other (job_arrival j) (job_arrival j + R).

      (* and X the total interference incurred by job j due to any task. *)
      Let X := total_interference job_cost rate sched j (job_arrival j) (job_arrival j + R).

      (* Recall Bertogna and Cirinei's workload bound ... *)
      Let workload_bound (tsk_other: sporadic_task) (R_other: time) :=
        W task_cost task_period tsk_other R_other R.

      (*... and the EDF-specific bound, ... *)
      Let edf_specific_bound (tsk_other: sporadic_task) (R_other: time) :=
        edf_specific_interference_bound task_cost task_period task_deadline tsk tsk_other R_other.

      (* ... which combined form the interference bound. *)
      Let interference_bound (tsk_other: sporadic_task) (R_other: time) :=
        interference_bound_edf task_cost task_period task_deadline tsk R (tsk_other, R_other). 
      
      (* Also, let ts_interf be the subset of tasks that interfere with tsk. *)
      Let ts_interf := [seq tsk_other <- ts | is_interfering_task_jlfp tsk tsk_other].

      Section LemmasAboutInterferingTasks.
        
        (* Let (tsk_other, R_other) be any pair of higher-priority task and
           response-time bound computed in previous iterations. *)
        Variable tsk_other: sporadic_task.
        Variable R_other: time.
        Hypothesis H_response_time_of_tsk_other: (tsk_other, R_other) \in rt_bounds.

        (* Note that tsk_other is in task set ts ...*)
        Lemma bertogna_edf_tsk_other_in_ts: tsk_other \in ts.
        Proof.
          by rewrite -H_rt_bounds_contains_all_tasks; apply/mapP; exists (tsk_other, R_other).
        Qed.

        (* Also, R_other is larger than the cost of tsk_other. *)
        Lemma bertogna_edf_R_other_ge_cost :
          R_other >= task_cost tsk_other.
        Proof.
          by rewrite [R_other](H_response_time_is_fixed_point tsk_other);
            first by apply leq_addr.
        Qed.

        (* Since tsk_other cannot interfere more than it executes, we show that
           the interference caused by tsk_other is no larger than workload bound W. *)
        Lemma bertogna_edf_workload_bounds_interference :
          x tsk_other <= workload_bound tsk_other R_other.
        Proof.
          unfold valid_sporadic_job in *.
          rename H_rate_equals_one into RATE,
                 H_all_previous_jobs_completed_on_time into BEFOREok,
                 H_valid_job_parameters into PARAMS,
                 H_valid_task_parameters into TASK_PARAMS,
                 H_restricted_deadlines into RESTR,
                 H_tasks_miss_no_deadlines into NOMISS.
          unfold x, task_interference.
          have INts := bertogna_edf_tsk_other_in_ts.
          apply leq_trans with (n := workload job_task rate sched tsk_other
                                         (job_arrival j) (job_arrival j + R));
            first by apply task_interference_le_workload; ins; rewrite RATE.
          apply workload_bounded_by_W with (task_deadline0 := task_deadline) (job_cost0 := job_cost) (job_deadline0 := job_deadline); try (by ins); last 2 first;
            [ by apply bertogna_edf_R_other_ge_cost
            | by ins; apply BEFOREok with (tsk_other := tsk_other); ins; rewrite RATE
            | by ins; rewrite RATE
            | by ins; apply TASK_PARAMS
            | by ins; apply RESTR |].
          red; move => j' JOBtsk' LEdl; unfold job_misses_no_deadline.
          assert (PARAMS' := PARAMS j'); des; rewrite PARAMS'1 JOBtsk'.
          apply completion_monotonic with (t := job_arrival j' + (R_other)); ins;
            first by rewrite leq_add2l; apply NOMISS.
          apply BEFOREok with (tsk_other := tsk_other); ins.
          apply leq_ltn_trans with (n := job_arrival j' + job_deadline j'); last by done.
          by specialize (PARAMS j'); des; rewrite leq_add2l PARAMS1 JOBtsk'; apply NOMISS.
        Qed.

        (* Recall that the edf-specific interference bound also holds. *)
        Lemma bertogna_edf_specific_bound_holds :
          x tsk_other <= edf_specific_bound tsk_other R_other.
        Proof.
          apply interference_bound_edf_bounds_interference with (job_deadline0 := job_deadline)
                                                                  (ts0 := ts); try (by done);
            [ by apply bertogna_edf_tsk_other_in_ts
            | by apply H_tasks_miss_no_deadlines
            | by apply H_tasks_miss_no_deadlines | ].
          by ins; apply H_all_previous_jobs_completed_on_time with (tsk_other := tsk_other). 
        Qed.
        
      End LemmasAboutInterferingTasks.

      (* Next we prove some lemmas that help to derive a contradiction.*)
      Section DerivingContradiction.

      (* 1) Since job j did not complete by its response time bound, it follows that
            the total interference X >= R - e_k + 1. *)
      Lemma bertogna_edf_too_much_interference : X >= R - task_cost tsk + 1.
      Proof.
        rename H_completed_jobs_dont_execute into COMP,
               H_valid_job_parameters into PARAMS,
               H_job_of_tsk into JOBtsk,
               H_j_not_completed into NOTCOMP.
        unfold completed, valid_sporadic_job in *.

        (* Since j has not completed, recall the time when it is not
         executing is the total interference. *)
        exploit (complement_of_interf_equals_service job_cost rate sched j (job_arrival j)
                                                                      (job_arrival j + R));
          last intro EQinterf; ins; unfold has_arrived; first by apply leqnn.
        rewrite {2}[_ + R]addnC -addnBA // subnn addn0 in EQinterf.
        rewrite addn1.
        move: NOTCOMP; rewrite neq_ltn; move => /orP NOTCOMP; des;
          last first.
        {
          apply (leq_ltn_trans (COMP j (job_arrival j + R))) in NOTCOMP.
          by rewrite ltnn in NOTCOMP.
        }
        apply leq_trans with (n := R - service rate sched j (job_arrival j + R)); last first.
        {
          unfold service; rewrite service_before_arrival_eq_service_during; ins.
          rewrite EQinterf subKn; first by done.
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
            rewrite -JOBtsk; specialize (PARAMS j); des; apply PARAMS0.
          }
          apply leq_trans with (n := job_cost j); first by ins.
          apply leq_trans with (n := task_cost tsk);
            first by rewrite -JOBtsk; specialize (PARAMS j); des; apply PARAMS0.
          by rewrite bertogna_edf_R_other_ge_cost.
        }
      Qed.

      (* 2) Next, we prove that the sum of the interference of each task is equal
            to the total interference multiplied by the number of processors. This
            holds because interference only occurs when all processors are busy. *)
      Lemma bertogna_edf_all_cpus_busy :
        \sum_(tsk_k <- ts_interf) x tsk_k = X * num_cpus.
      Proof.
        rename H_global_scheduling_invariant into INV.
        unfold x, X, total_interference, task_interference.
        rewrite -big_mkcond -exchange_big big_distrl /=.
        rewrite [\sum_(_ <= _ < _ | backlogged _ _ _ _ _) _]big_mkcond.
        apply eq_big_nat; move => t LTt.
        destruct (backlogged job_cost rate sched j t) eqn:BACK;
          last by rewrite (eq_bigr (fun i => 0));
            [by rewrite big_const_seq iter_addn mul0n addn0 | by done].
        rewrite big_mkcond mul1n /=.
        rewrite big_filter big_mkcond.
        rewrite (eq_bigr (fun i => if (is_interfering_task_jlfp tsk i &&
                    task_is_scheduled job_task sched i t) then 1 else 0));
          last by intro i; clear -i; desf.
        rewrite -big_mkcond sum1_count.
        by eapply cpus_busy_with_interfering_tasks; try (by done);
          [by apply INV | by apply H_job_of_tsk | by apply BACK].
      Qed.

      (* Let (cardGE delta) be the number of interfering tasks whose interference
         is larger than delta. *)
      Let cardGE (delta: time) := count (fun i => x i >= delta) ts_interf.

      (* 3) If there is at least one of such tasks (e.g., cardGE > 0), then the
         cumulative interference caused by the complementary set of interfering
         tasks fills at least (num_cpus - cardGE) processors. *)
      Lemma bertogna_edf_helper_lemma :
        forall delta,
          cardGE delta > 0 ->
          \sum_(i <- ts_interf | x i < delta) x i >= delta * (num_cpus - cardGE delta).
      Proof.
        rename H_global_scheduling_invariant into INVARIANT.
        intros delta HAS.
        set some_interference_A := fun t =>
            backlogged job_cost rate sched j t &&
            has (fun tsk_k => ((x tsk_k >= delta) &&
                     task_is_scheduled job_task sched tsk_k t)) ts_interf.      
        set total_interference_B := fun t =>
            backlogged job_cost rate sched j t *
            count (fun tsk_k => (x tsk_k < delta) &&
              task_is_scheduled job_task sched tsk_k t) ts_interf.

        rewrite -has_count in HAS.
        apply leq_trans with ((\sum_(job_arrival j <= t < job_arrival j + R)
                              some_interference_A t) * (num_cpus - cardGE delta)).
        {
          rewrite leq_mul2r; apply/orP; right.
          move: HAS => /hasP HAS; destruct HAS as [tsk_a INa LEa].
          apply leq_trans with (n := x tsk_a); first by apply LEa.
          unfold x, task_interference, some_interference_A.
          apply leq_sum; ins.
          destruct (backlogged job_cost rate sched j i);
            [rewrite 2!andTb | by ins].
          destruct (task_is_scheduled job_task sched tsk_a i) eqn:SCHEDa;
            [apply eq_leq; symmetry | by ins].
          apply/eqP; rewrite eqb1.
          by apply/hasP; exists tsk_a; last by apply/andP.
        }
        apply leq_trans with (\sum_(job_arrival j <= t < job_arrival j + R)
                                   total_interference_B t).
        {
          rewrite big_distrl /=.
          apply leq_sum; intros t _.
          unfold some_interference_A, total_interference_B. 
          destruct (backlogged job_cost rate sched j t) eqn:BACK;
            [rewrite andTb mul1n | by done].
          destruct (has (fun tsk_k : sporadic_task => (delta <= x tsk_k) &&
                     task_is_scheduled job_task sched tsk_k t) ts_interf) eqn:HAS';
            last by done.
          rewrite mul1n; move: HAS => /hasP HAS.
          destruct HAS as [tsk_k INk LEk].

          generalize INVARIANT; intro COUNT.
          apply cpus_busy_with_interfering_tasks with (job_task0 := job_task) (ts0 := ts) (j0 := j) (tsk0 := tsk) (t0 := t) in COUNT;
                try by done.

          unfold cardGE.
          set interfering_tasks_at_t :=
            [seq tsk_k <- ts_interf | task_is_scheduled job_task
                                                        sched tsk_k t].

          rewrite -(count_filter (fun i => true)) in COUNT.
          fold interfering_tasks_at_t in COUNT.
          rewrite count_predT in COUNT.
          apply leq_trans with (n := num_cpus -
                       count (fun i => (x i >= delta) &&
                          task_is_scheduled job_task sched i t) ts_interf).
          {
            apply leq_sub2l.
            rewrite -2!sum1_count big_mkcond /=.
            rewrite [\sum_(_ <- _ | _ <= _)_]big_mkcond /=.
            apply leq_sum; intros i _.
            destruct (task_is_scheduled job_task sched i t);
              [by rewrite andbT | by rewrite andbF].
          }

          rewrite leq_subLR -count_predUI.
          apply leq_trans with (n :=
              count (predU (fun i : sporadic_task =>
                              (delta <= x i) &&
                              task_is_scheduled job_task sched i t)
                           (fun tsk_k0 : sporadic_task =>
                              (x tsk_k0 < delta) &&
                              task_is_scheduled job_task sched tsk_k0 t))
                    ts_interf); last by apply leq_addr.
          apply leq_trans with (n := size interfering_tasks_at_t).
          {
            rewrite -COUNT.
            rewrite leq_eqVlt; apply/orP; left; apply/eqP; f_equal.
            unfold interfering_tasks_at_t.
            rewrite -filter_predI; apply eq_filter; red; simpl.
            by intros i; rewrite andbC.
          }
          unfold interfering_tasks_at_t.
          rewrite -count_predT count_filter.
          rewrite leq_eqVlt; apply/orP; left; apply/eqP.
          apply eq_count; red; simpl.
          intros i.
          destruct (task_is_scheduled job_task sched i t);
            rewrite 3?andTb ?andFb ?andbF ?andbT /=; try ins.
          by rewrite leqNgt orNb. 
        }
        {
            unfold x at 2, task_interference.
            rewrite exchange_big /=; apply leq_sum; intros t _.
            unfold total_interference_B.
            destruct (backlogged job_cost rate sched j t); last by ins.
            rewrite mul1n -sum1_count.
            rewrite big_seq_cond big_mkcond [\sum_(i <- ts_interf | _ < _) _]big_mkcond.
            by apply leq_sum; ins; clear -i; desf; des; rewrite ?Heq2.
        }
      Qed.

      (* 4) Next, we prove that, for any interval delta, if the sum of per-task
            interference exceeds delta * num_cpus, the same applies for the
            sum of the minimum between the interference and delta. *)
      Lemma bertogna_edf_minimum_exceeds_interference :
        forall delta,
          \sum_(tsk_k <- ts_interf) x tsk_k >= delta * num_cpus ->
             \sum_(tsk_k <- ts_interf) minn (x tsk_k) delta >=
             delta * num_cpus.
      Proof.
        intros delta SUMLESS.
        set more_interf := fun tsk_k => x tsk_k >= delta.
        rewrite [\sum_(_ <- _) minn _ _](bigID more_interf) /=.
        unfold more_interf, minn.
        rewrite [\sum_(_ <- _ | delta <= _)_](eq_bigr (fun i => delta));
          last by intros i COND; rewrite leqNgt in COND; destruct (delta > x i).
        rewrite [\sum_(_ <- _ | ~~_)_](eq_big (fun i => x i < delta)
                                              (fun i => x i));
          [| by red; ins; rewrite ltnNge
           | by intros i COND; rewrite -ltnNge in COND; rewrite COND].

        (* Case 1: cardGE = 0 *)
        destruct (~~ has (fun i => delta <= x i) ts_interf) eqn:HASa.
        {
          rewrite [\sum_(_ <- _ | _ <= _) _]big_hasC; last by apply HASa.
          rewrite big_seq_cond; move: HASa => /hasPn HASa.
          rewrite add0n (eq_bigl (fun i => (i \in ts_interf) && true));
            last by red; intros tsk_k; destruct (tsk_k \in ts_interf) eqn:INk;
              [by rewrite andTb ltnNge; apply HASa | by rewrite andFb].
          by rewrite -big_seq_cond.
        } apply negbFE in HASa.
        
        (* Case 2: cardGE >= num_cpus *)
        destruct (cardGE delta >= num_cpus) eqn:CARD.
        {
          apply leq_trans with (delta * cardGE delta);
            first by rewrite leq_mul2l; apply/orP; right.
          unfold cardGE; rewrite -sum1_count big_distrr /=.
          rewrite -[\sum_(_ <- _ | _) _]addn0.
          by apply leq_add; [by apply leq_sum; ins; rewrite muln1|by ins].
        } apply negbT in CARD; rewrite -ltnNge in CARD.

        (* Case 3: cardGE < num_cpus *)
        rewrite big_const_seq iter_addn addn0; fold cardGE.
        apply leq_trans with (n := delta * cardGE delta +
                                   delta * (num_cpus - cardGE delta));
          first by rewrite -mulnDr subnKC //; apply ltnW.
        by rewrite leq_add2l; apply bertogna_edf_helper_lemma; rewrite -has_count.
      Qed.

      (* 5) Now, we prove that the Bertogna's interference bound
            is not enough to cover the sum of the "minimum" term over
            all tasks (artifact of the proof by contradiction). *)
      Lemma bertogna_edf_sum_exceeds_total_interference:
        \sum_((tsk_other, R_other) <- rt_bounds | is_interfering_task_jlfp tsk tsk_other)
          minn (x tsk_other) (R - task_cost tsk + 1) > I tsk R.
      Proof.
        rename H_rt_bounds_contains_all_tasks into UNZIP,
          H_response_time_is_fixed_point into REC.
        have GE_COST := bertogna_edf_R_other_ge_cost.
        apply leq_trans with (n := \sum_(tsk_other <- ts_interf) minn (x tsk_other) (R - task_cost tsk + 1));
          last first.
        {
          rewrite (eq_bigr (fun i => minn (x (fst i)) (R - task_cost tsk + 1)));
            last by ins; destruct i.
          move: UNZIP => UNZIP.
          assert (FILTER: filter (is_interfering_task_jlfp tsk) (unzip1 rt_bounds) =
                          filter (is_interfering_task_jlfp tsk) ts).
            by f_equal.
          unfold ts_interf; rewrite -FILTER; clear FILTER.
          rewrite -[\sum_(_ <- rt_bounds | _)_]big_filter.
          assert (SUBST: [seq i <- rt_bounds
                 | let '(tsk_other, _) := i in
                        is_interfering_task_jlfp tsk tsk_other] = [seq i <- rt_bounds
                           | is_interfering_task_jlfp tsk (fst i)]).
          {
            by apply eq_filter; red; intro i; destruct i.
          } rewrite SUBST; clear SUBST.         
          have MAP := big_map (fun x => fst x) (fun i => true) (fun i => minn (x i) (R - task_cost tsk + 1)).
          by rewrite -MAP; apply eq_leq; f_equal; rewrite filter_map.
        }
        
        apply ltn_div_trunc with (d := num_cpus); first by apply H_at_least_one_cpu.
        rewrite -(ltn_add2l (task_cost tsk)) -REC; last by done.
        rewrite -addn1 -leq_subLR.
        rewrite -[R + 1 - _]subh1; last by apply GE_COST.
        rewrite leq_divRL; last by apply H_at_least_one_cpu.
        apply bertogna_edf_minimum_exceeds_interference.
        apply leq_trans with (n := X * num_cpus);
          last by rewrite bertogna_edf_all_cpus_busy.
        rewrite leq_mul2r; apply/orP; right.
        by apply bertogna_edf_too_much_interference.
      Qed.

      (* 6) After concluding that the sum of the minimum exceeds (R - e_i + 1),
            we prove that there exists a tuple (tsk_k, R_k) such that
            min (x_k, R - e_i + 1) > min (W_k, edf_bound, R - e_i + 1). *)
      Lemma bertogna_edf_exists_task_that_exceeds_bound :
        exists tsk_other R_other,
          (tsk_other, R_other) \in rt_bounds /\
          (minn (x tsk_other) (R - task_cost tsk + 1) > interference_bound tsk_other R_other).
      Proof.
        rename H_rt_bounds_contains_all_tasks into UNZIP.
        assert (HAS: has (fun tup : task_with_response_time =>
                            let (tsk_other, R_other) := tup in
                            (tsk_other \in ts) && is_interfering_task_jlfp tsk tsk_other &&
                              (minn (x tsk_other) (R - task_cost tsk + 1)  >
                              interference_bound tsk_other R_other))
                         rt_bounds).
        {
          apply/negP; unfold not; intro NOTHAS.
          move: NOTHAS => /negP /hasPn ALL.
          have SUM := bertogna_edf_sum_exceeds_total_interference.
          rewrite -[_ < _]negbK in SUM.
          move: SUM => /negP SUM; apply SUM; rewrite -leqNgt.
          unfold I, total_interference_bound_edf.
          rewrite big_seq_cond [\sum_(_ <- _ | let _ := _ in _)_]big_seq_cond.
          apply leq_sum; move => tsk_k /andP [INBOUNDSk INTERFk]; destruct tsk_k as [tsk_k R_k].
          specialize (ALL (tsk_k, R_k) INBOUNDSk).
          unfold interference_bound_edf; simpl in *.
          rewrite leq_min; apply/andP; split.
          {
            unfold interference_bound; rewrite leq_min; apply/andP; split;
              last by rewrite geq_minr.
            apply leq_trans with (n := x tsk_k); first by rewrite geq_minl.
            by apply bertogna_edf_workload_bounds_interference.
          }
          {
            apply leq_trans with (n := x tsk_k); first by rewrite geq_minl.
            by apply bertogna_edf_specific_bound_holds.
          }
        }
        move: HAS => /hasP HAS; destruct HAS as [[tsk_k R_k] HPk MIN].
        move: MIN => /andP [/andP [INts INTERFk] MINk].
        by exists tsk_k, R_k; repeat split.
      Qed.

      End DerivingContradiction.
      
    End Lemmas.

    Section MainProof.
      
      (* Let (tsk, R) be any task to be analyzed, with its response-time bound R. *)
      Variable tsk: sporadic_task.
      Variable R: time.
      Hypothesis H_tsk_R_in_rt_bounds: (tsk, R) \in rt_bounds.

      (* Using the lemmas above, we prove that R bounds the response time of task tsk. *)
      Theorem bertogna_cirinei_response_time_bound_edf :
        response_time_bounded_by tsk R.
      Proof.
        intros j JOBtsk.
       
        (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
        remember (job_arrival j + R) as ctime.

        revert H_tsk_R_in_rt_bounds.
        generalize dependent R; generalize dependent tsk; generalize dependent j.
      
        (* Now, we apply strong induction on the absolute response-time bound. *)
        induction ctime as [ctime IH] using strong_ind_lt.

        intros j tsk' JOBtsk R' EQc INbounds; subst ctime.

        (* First, let's simplify the induction hypothesis. *)
        assert (BEFOREok: forall (j0: JobIn arr_seq) tsk R0,
                                 job_task j0 = tsk ->
                               (tsk, R0) \in rt_bounds ->
                               job_arrival j0 + R0 < job_arrival j + R' ->
                               service rate sched j0 (job_arrival j0 + R0) == job_cost j0).
        {
            by ins; apply IH with (tsk := tsk0) (R := R0).
        }
        clear IH.
        
        (* The proof follows by contradiction. Assume that job j does not complete by its
           response-time bound. By the induction hypothesis, all jobs with absolute
           response-time bound t < (job_arrival j + R) have correct response-time bounds. *)
        destruct (completed job_cost rate sched j (job_arrival j + R')) eqn:NOTCOMP;
          first by done.
        apply negbT in NOTCOMP; exfalso.
        
        (* Next, we derive a contradiction using the previous lemmas. *)
        exploit (bertogna_edf_exists_task_that_exceeds_bound tsk' R' INbounds j JOBtsk NOTCOMP).
        {
          by ins; apply IH with (tsk := tsk_other) (R := R_other).
        } 
        intro EX; destruct EX as [tsk_other [R_other [HP LTmin]]].
        unfold interference_bound_edf, interference_bound_fp in LTmin.
        rewrite minnAC in LTmin; apply min_lt_same in LTmin.
        have BASICBOUND := bertogna_edf_workload_bounds_interference R' j BEFOREok tsk_other R_other HP.
        have EDFBOUND := (bertogna_edf_specific_bound_holds tsk' R' INbounds j JOBtsk BEFOREok tsk_other R_other HP).
        unfold minn in LTmin; clear -LTmin HP BASICBOUND EDFBOUND tsk; desf.
        {
          by apply (leq_ltn_trans BASICBOUND) in LTmin; rewrite ltnn in LTmin. 
        }
        {
          by apply (leq_ltn_trans EDFBOUND) in LTmin; rewrite ltnn in LTmin.
        }
      Qed.

    End MainProof.
    
  End ResponseTimeBound.

End ResponseTimeAnalysisEDF.