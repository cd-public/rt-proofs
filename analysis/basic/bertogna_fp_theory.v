Add LoadPath "../.." as rt.
Require Import rt.util.all.
Require Import rt.model.basic.task rt.model.basic.job rt.model.basic.task_arrival
               rt.model.basic.schedule rt.model.basic.platform rt.model.basic.platform_fp
               rt.model.basic.workload rt.model.basic.schedulability rt.model.basic.priority
               rt.model.basic.response_time rt.model.basic.interference.
Require Import rt.analysis.basic.workload_bound rt.analysis.basic.interference_bound_fp.
Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisFP.

  Export Job SporadicTaskset Schedule Workload Interference InterferenceBoundFP
         Platform PlatformFP Schedulability ResponseTime Priority SporadicTaskArrival WorkloadBound.
    
  Section ResponseTimeBound.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
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
    Variable sched: schedule num_cpus arr_seq.

    (* ...jobs do not execute before their arrival times nor longer
       than their execution costs. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Also assume that jobs do not execute in parallel and that
       there exists at least one processor. *)
    Hypothesis H_no_parallelism:
      jobs_dont_execute_in_parallel sched.
    Hypothesis H_at_least_one_cpu :
      num_cpus > 0.

    (* Consider a task set ts with no duplicates where all jobs
       come from the task set and all tasks have valid parameters
       and restricted deadlines. *)
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_ts_is_a_set: uniq ts.
    Hypothesis H_all_jobs_from_taskset:
      forall (j: JobIn arr_seq), job_task j \in ts.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_restricted_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    (* Next, consider a task tsk that is to be analyzed. *)
    Variable tsk: sporadic_task.
    Hypothesis task_in_ts: tsk \in ts.

    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task sched tsk.
    Let is_response_time_bound (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_cost job_task tsk sched.

    (* Assume a given FP policy. *)
    Variable higher_eq_priority: FP_policy sporadic_task.
    Let can_interfere_with_tsk := fp_can_interfere_with higher_eq_priority tsk.

    (* Assume a response-time bound is known... *)
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable hp_bounds: seq task_with_response_time.
    Hypothesis H_response_time_of_interfering_tasks_is_known:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds ->
        is_response_time_bound_of_task job_cost job_task hp_tsk sched R.
    
    (* ... for any task in ts that interferes with tsk. *)
    Hypothesis H_hp_bounds_has_interfering_tasks:
      [seq tsk_hp <- ts | can_interfere_with_tsk tsk_hp] = unzip1 hp_bounds.

    (* Assume that the response-time bounds are larger than task costs. *)
    Hypothesis H_response_time_bounds_ge_cost:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds -> R >= task_cost hp_tsk.
    
    (* Assume that no deadline is missed by any interfering task, i.e.,
       response-time bound R_other <= deadline. *)
    Hypothesis H_interfering_tasks_miss_no_deadlines:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds -> R <= task_deadline hp_tsk.

    (* Assume that the scheduler is work-conserving and enforces the FP policy. *)
    Hypothesis H_work_conserving: work_conserving job_cost sched.
    Hypothesis H_enforces_FP_policy:
      enforces_FP_policy job_cost job_task sched higher_eq_priority.
    
    (* Let R be the fixed point of Bertogna and Cirinei's recurrence, ...*)
    Variable R: time.
    Hypothesis H_response_time_recurrence_holds :
      R = task_cost tsk +
          div_floor
            (total_interference_bound_fp task_cost task_period tsk hp_bounds R higher_eq_priority)
            num_cpus.

    (* ... and assume that R is no larger than the deadline of tsk.*)
    Hypothesis H_response_time_no_larger_than_deadline:
      R <= task_deadline tsk.

    (* In order to prove that R is a response-time bound, we first present some lemmas. *)
    Section Lemmas.

      (* Consider any job j of tsk. *)
      Variable j: JobIn arr_seq.
      Hypothesis H_job_of_tsk: job_task j = tsk.

      (* Assume that job j is the first job of tsk not to complete by the response time bound. *)
      Hypothesis H_j_not_completed: ~~ completed job_cost sched j (job_arrival j + R).
      Hypothesis H_previous_jobs_of_tsk_completed :
        forall (j0: JobIn arr_seq),
          job_task j0 = tsk ->
          job_arrival j0 < job_arrival j ->
          completed job_cost sched j0 (job_arrival j0 + R).
      
      (* Let's call x the interference incurred by job j due to tsk_other, ...*)
      Let x (tsk_other: sporadic_task) :=
        task_interference_sequential job_cost job_task sched j
                          tsk_other (job_arrival j) (job_arrival j + R).

      (* and X the total interference incurred by job j due to any task. *)
      Let X := total_interference job_cost sched j (job_arrival j) (job_arrival j + R).

      (* Recall Bertogna and Cirinei's workload bound. *)
      Let workload_bound (tsk_other: sporadic_task) (R_other: time) :=
        W task_cost task_period tsk_other R_other R.

      (* Also, let ts_interf be the subset of tasks that interfere with tsk. *)
      Let ts_interf := [seq tsk_other <- ts | can_interfere_with_tsk tsk_other].

      Section LemmasAboutInterferingTasks.
        
        (* Let (tsk_other, R_other) be any pair of higher-priority task and
           response-time bound computed in previous iterations. *)
        Variable tsk_other: sporadic_task.
        Variable R_other: time.
        Hypothesis H_response_time_of_tsk_other: (tsk_other, R_other) \in hp_bounds.

        (* Note that tsk_other is in task set ts ...*)
        Lemma bertogna_fp_tsk_other_in_ts: tsk_other \in ts.
          Proof.
            rename H_hp_bounds_has_interfering_tasks into UNZIP,
                   H_response_time_of_tsk_other into INbounds.
            move: UNZIP => UNZIP.
            cut (tsk_other \in ts_interf);
              first by rewrite mem_filter; move => /andP [_ IN].
            unfold ts_interf; rewrite UNZIP.
            by apply/mapP; exists (tsk_other, R_other).
        Qed.

        (*... and interferes with tsk. *)
        Lemma bertogna_fp_tsk_other_interferes: can_interfere_with_tsk tsk_other.
          Proof.
            rename H_hp_bounds_has_interfering_tasks into UNZIP,
                   H_response_time_of_tsk_other into INbounds.
            move: UNZIP => UNZIP.
            cut (tsk_other \in ts_interf);
              first by rewrite mem_filter; move => /andP [INTERF _].
            unfold ts_interf; rewrite UNZIP.
            by apply/mapP; exists (tsk_other, R_other).
        Qed.

        (* Since tsk_other cannot interfere more than it executes, we show that
           the interference caused by tsk_other is no larger than workload bound W. *)
        Lemma bertogna_fp_workload_bounds_interference :
          x tsk_other <= workload_bound tsk_other R_other.
        Proof.
          unfold is_response_time_bound, is_response_time_bound_of_task,
                 completed, completed_jobs_dont_execute, valid_sporadic_job in *.
          rename H_valid_job_parameters into PARAMS,
                 H_valid_task_parameters into TASK_PARAMS,
                 H_restricted_deadlines into RESTR,
                 H_response_time_of_interfering_tasks_is_known into RESP,
                 H_interfering_tasks_miss_no_deadlines into NOMISS,
                 H_response_time_bounds_ge_cost into GE_COST.
          unfold x, workload_bound.
          have INts := bertogna_fp_tsk_other_in_ts.
          apply leq_trans with (n := workload job_task sched tsk_other
                                              (job_arrival j) (job_arrival j + R));
            first by apply task_interference_seq_le_workload.
          by apply workload_bounded_by_W with (task_deadline0 := task_deadline)
                    (job_cost0 := job_cost) (job_deadline0 := job_deadline);
            try (by ins); last 2 first;
              [ by ins; apply GE_COST 
              | by ins; apply NOMISS
              | by ins; apply TASK_PARAMS
              | by ins; apply RESTR
              | by ins; apply RESP with (hp_tsk := tsk_other)].
        Qed.

      End LemmasAboutInterferingTasks.

      (* Next we prove some lemmas that help to derive a contradiction.*)
      Section DerivingContradiction.

        (* 0) Since job j did not complete by its response time bound, it follows that
              the total interference X >= R - e_k + 1. *)
        Lemma bertogna_fp_too_much_interference : X >= R - task_cost tsk + 1.
        Proof.
          rename H_completed_jobs_dont_execute into COMP,
                 H_valid_job_parameters into PARAMS,
                 H_job_of_tsk into JOBtsk,
                 H_j_not_completed into NOTCOMP.
          unfold completed, valid_sporadic_job in *.

          (* Since j has not completed, recall the time when it is not
           executing is the total interference. *)
          exploit (complement_of_interf_equals_service job_cost sched j (job_arrival j)
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
          apply leq_trans with (n := R - service sched j (job_arrival j + R)); last first.
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
            by rewrite H_response_time_recurrence_holds; apply leq_addr.
          }
        Qed.

        Let scheduled_task_other_than_tsk (t: time) (tsk_other: sporadic_task) :=
          task_is_scheduled job_task sched tsk_other t &&
          can_interfere_with_tsk tsk_other.
        
        (* 1) At all times that j is backlogged, all processors are busy with other tasks. *)
        Lemma bertogna_fp_scheduling_invariant:
          forall t,
            job_arrival j <= t < job_arrival j + R ->
            backlogged job_cost sched j t ->
            count (scheduled_task_other_than_tsk t) ts = num_cpus.
        Proof.
          rename H_valid_task_parameters into PARAMS,
                 H_all_jobs_from_taskset into FROMTS,
                 H_job_of_tsk into JOBtsk,
                 H_sporadic_tasks into SPO,
                 H_valid_job_parameters into JOBPARAMS,
                 H_restricted_deadlines into RESTR,
                 H_hp_bounds_has_interfering_tasks into UNZIP,
                 H_interfering_tasks_miss_no_deadlines into NOMISS,
                 H_response_time_of_interfering_tasks_is_known into PREV.
          unfold sporadic_task_model, is_response_time_bound_of_task in *.
          move => t /andP [LEt LTt] BACK.
          apply platform_fp_cpus_busy_with_interfering_tasks with (task_cost0 := task_cost)
          (task_period0 := task_period) (task_deadline0 := task_deadline) (job_task0 := job_task)
          (ts0 := ts) (tsk0 := tsk) (higher_eq_priority0 := higher_eq_priority) in BACK;
            try (by done); first by apply PARAMS.
          {
            apply leq_trans with (n := job_arrival j + R); first by done.
            rewrite leq_add2l.
            by apply leq_trans with (n := task_deadline tsk); last by apply RESTR.
          }      
          {
            intros j_other tsk_other JOBother INTERF.
            move: UNZIP => UNZIP.
            cut (tsk_other \in unzip1 hp_bounds); last first.
            {
              rewrite -UNZIP mem_filter; apply/andP; split; first by done.
              by rewrite -JOBother; apply FROMTS.
            } intro IN.
            move: IN => /mapP [p IN EQ]; destruct p as [tsk' R']; simpl in *; subst tsk'.
            apply completion_monotonic with (t0 := job_arrival j_other + R'); try (by done);
              last by apply PREV with (hp_tsk := tsk_other).
            {
              rewrite leq_add2l.
              apply leq_trans with (n := task_deadline tsk_other); first by apply NOMISS.
              apply RESTR.
              cut (tsk_other \in unzip1 hp_bounds); last by apply/mapP; exists (tsk_other, R').
              by rewrite -UNZIP mem_filter; move => /andP [_ IN'].
            }
          }
          {
            ins; apply completion_monotonic with (t0 := job_arrival j0 + R); try (by done);
              last by apply H_previous_jobs_of_tsk_completed.
            rewrite leq_add2l.
            by apply leq_trans with (n := task_deadline tsk); last by apply RESTR.
          }
        Qed.


        (* 2) Next, we prove that the sum of the interference of each task is equal
              to the total interference multiplied by the number of processors. This
              holds because interference only occurs when all processors are busy. *)
        Lemma bertogna_fp_all_cpus_busy :
          \sum_(tsk_k <- ts_interf) x tsk_k = X * num_cpus.
        Proof.
          unfold x, X, total_interference, task_interference.
          rewrite -big_mkcond -exchange_big big_distrl /=.
          rewrite [\sum_(_ <= _ < _ | backlogged _ _ _ _) _]big_mkcond.
          apply eq_big_nat; move => t LTt.
          destruct (backlogged job_cost sched j t) eqn:BACK;
            last by rewrite (eq_bigr (fun i => 0));
              [by rewrite big_const_seq iter_addn mul0n addn0 | by done].
          rewrite big_mkcond mul1n /=.
          rewrite big_filter big_mkcond.
          rewrite (eq_bigr (fun i => if (scheduled_task_other_than_tsk t i) then 1 else 0));
            last first.
          {
            intros i _; clear -i.
            unfold scheduled_task_other_than_tsk.
            by destruct (task_is_scheduled job_task sched i t); rewrite ?andFb ?andTb ?andbT //; desf.
          }
          rewrite -big_mkcond sum1_count.
          by apply bertogna_fp_scheduling_invariant.
        Qed.

        (* Let (cardGE delta) be the number of interfering tasks whose interference
           is larger than delta. *)
        Let cardGE (delta: time) := count (fun i => x i >= delta) ts_interf.

        (* 3) If there is at least one of such tasks (e.g., cardGE > 0), then the
           cumulative interference caused by the complementary set of interfering
           tasks fills at least (num_cpus - cardGE) processors. *)
        Lemma bertogna_fp_helper_lemma :
          forall delta,
            cardGE delta > 0 ->
            \sum_(i <- ts_interf | x i < delta) x i >= delta * (num_cpus - cardGE delta).
        Proof.
          intros delta HAS.
          set some_interference_A := fun t =>
              backlogged job_cost sched j t &&
              has (fun tsk_k => ((x tsk_k >= delta) &&
                       task_is_scheduled job_task sched tsk_k t)) ts_interf.      
          set total_interference_B := fun t =>
              backlogged job_cost sched j t *
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
            destruct (backlogged job_cost sched j i);
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
            rewrite big_nat_cond [\sum_(_ <= _ < _ | true)_]big_nat_cond.
            apply leq_sum; move => t /andP [LEt _].
            unfold some_interference_A, total_interference_B. 
            destruct (backlogged job_cost sched j t) eqn:BACK;
              [rewrite andTb mul1n | by done].
            destruct (has (fun tsk_k : sporadic_task => (delta <= x tsk_k) &&
                       task_is_scheduled job_task sched tsk_k t) ts_interf) eqn:HAS';
              last by done.
            rewrite mul1n; move: HAS => /hasP HAS.
            destruct HAS as [tsk_k INk LEk].

            have COUNT := bertogna_fp_scheduling_invariant t LEt BACK.

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
              destruct (backlogged job_cost sched j t); last by ins.
              rewrite mul1n -sum1_count.
              rewrite big_seq_cond big_mkcond [\sum_(i <- ts_interf | _ < _) _]big_mkcond.
              by apply leq_sum; ins; clear -i; desf; des; rewrite ?Heq2.
          }
        Qed.

        (* 4) Next, we prove that, for any interval delta, if the sum of per-task
              interference exceeds delta * num_cpus, the same applies for the
              sum of the minimum between the interference and delta. *)
        Lemma bertogna_fp_minimum_exceeds_interference :
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
          by rewrite leq_add2l; apply bertogna_fp_helper_lemma; rewrite -has_count.
        Qed.

        (* 5) Now, we prove that the Bertogna's interference bound
              is not enough to cover the sum of the "minimum" term over
              all tasks (artifact of the proof by contradiction). *)
        Lemma bertogna_fp_sum_exceeds_total_interference:
          \sum_((tsk_k, R_k) <- hp_bounds)
            minn (x tsk_k) (R - task_cost tsk + 1) >
          total_interference_bound_fp task_cost task_period tsk hp_bounds
                                      R higher_eq_priority.
        Proof.
          rename H_hp_bounds_has_interfering_tasks into UNZIP,
                 H_response_time_recurrence_holds into REC.
          apply leq_trans with (n := \sum_(tsk_k <- ts_interf) minn (x tsk_k) (R - task_cost tsk + 1));
            last first.
          {
            rewrite (eq_bigr (fun i => minn (x (fst i)) (R - task_cost tsk + 1)));
              last by ins; destruct i.
            rewrite big_filter.
            have MAP := big_map (fun x => fst x) (fun i => true) (fun i => minn (x i) (R - task_cost tsk + 1)).
            by unfold unzip1 in *; rewrite -MAP -UNZIP -big_filter.
          }
          apply ltn_div_trunc with (d := num_cpus);
            first by apply H_at_least_one_cpu.
          rewrite -(ltn_add2l (task_cost tsk)) -REC.
          rewrite -addn1 -leq_subLR.
          rewrite -[R + 1 - _]subh1; last by rewrite REC; apply leq_addr.
          rewrite leq_divRL; last by apply H_at_least_one_cpu.
          apply bertogna_fp_minimum_exceeds_interference.
          apply leq_trans with (n := X * num_cpus);
            last by rewrite bertogna_fp_all_cpus_busy.
          rewrite leq_mul2r; apply/orP; right.
          by apply bertogna_fp_too_much_interference.
        Qed.

        (* 6) After concluding that the sum of the minimum exceeds (R - e_i + 1),
              we prove that there exists a tuple (tsk_k, R_k) such that
              min (x_k, R - e_i + 1) > min (W_k, R - e_i + 1). *)
        Lemma bertogna_fp_exists_task_that_exceeds_bound :
          exists tsk_k R_k,
            (tsk_k, R_k) \in hp_bounds /\
            (minn (x tsk_k) (R - task_cost tsk + 1) >
              minn (workload_bound tsk_k R_k) (R - task_cost tsk + 1)).
        Proof.
          rename H_hp_bounds_has_interfering_tasks into UNZIP.
          assert (HAS: has (fun tup : task_with_response_time =>
                             let (tsk_k, R_k) := tup in
                               (minn (x tsk_k) (R - task_cost tsk + 1) >
                                minn (workload_bound tsk_k R_k)(R - task_cost tsk + 1)))
                            hp_bounds).
          {
            apply/negP; unfold not; intro NOTHAS.
            move: NOTHAS => /negP /hasPn ALL.
            have SUM := bertogna_fp_sum_exceeds_total_interference.
            rewrite -[_ < _]negbK in SUM.
            move: SUM => /negP SUM; apply SUM; rewrite -leqNgt.
            unfold total_interference_bound_fp.
            rewrite [\sum_(i <- _ | let '(tsk_other, _) := i in _)_]big_mkcond.
            rewrite big_seq_cond [\sum_(i <- _ | true) _]big_seq_cond.
            apply leq_sum; move => tsk_k /andP [HPk _]; destruct tsk_k as [tsk_k R_k].
            specialize (ALL (tsk_k, R_k) HPk).
            rewrite -leqNgt in ALL.
            have INTERFk := bertogna_fp_tsk_other_interferes tsk_k R_k HPk.
            fold (can_interfere_with_tsk); rewrite INTERFk.
            by apply ALL.
          }
          move: HAS => /hasP HAS; destruct HAS as [[tsk_k R_k] HPk MINk]; exists tsk_k, R_k.
          by repeat split.
        Qed.

      End DerivingContradiction.

    End Lemmas.
    
    (* Using the lemmas above, we prove that R bounds the response time of task tsk. *)
    Theorem bertogna_cirinei_response_time_bound_fp :
      is_response_time_bound tsk R.
    Proof.
      rename H_response_time_bounds_ge_cost into GE_COST,
             H_interfering_tasks_miss_no_deadlines into NOMISS,
             H_response_time_recurrence_holds into REC,
             H_response_time_of_interfering_tasks_is_known into RESP,
             H_hp_bounds_has_interfering_tasks into UNZIP,
             H_response_time_no_larger_than_deadline into LEdl.
      intros j JOBtsk.
       
      (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
      remember (job_arrival j + R) as ctime.
      
      (* Now, we apply strong induction on the absolute response-time bound. *)
      generalize dependent j.
      induction ctime as [ctime IH] using strong_ind.

      intros j JOBtsk EQc; subst ctime.

      (* First, let's simplify the induction hypothesis. *)
      assert (BEFOREok: forall (j0: JobIn arr_seq),
                          job_task j0 = tsk ->
                          job_arrival j0 < job_arrival j ->
                          service sched j0 (job_arrival j0 + R) == job_cost j0).
      {
        by ins; apply IH; try (by done); rewrite ltn_add2r.
      } clear IH.
              
      unfold is_response_time_bound, is_response_time_bound_of_task,
             completed, completed_jobs_dont_execute, valid_sporadic_job in *.

      (* Now we start the proof. Assume by contradiction that job j
         is not complete at time (job_arrival j + R). *)
      destruct (completed job_cost sched j (job_arrival j + R)) eqn:NOTCOMP;
        first by done.
      apply negbT in NOTCOMP; exfalso.

      (* We derive a contradiction using the previous lemmas. *)
      have EX := bertogna_fp_exists_task_that_exceeds_bound j JOBtsk NOTCOMP BEFOREok.
      destruct EX as [tsk_k [R_k [HPk LTmin]]].
      unfold minn at 1 in LTmin.
      have WORKLOAD := bertogna_fp_workload_bounds_interference j tsk_k R_k HPk.
      destruct (W task_cost task_period tsk_k R_k R < R - task_cost tsk + 1); rewrite leq_min in LTmin; 
        last by move: LTmin => /andP [_ BUG]; rewrite ltnn in BUG.
      move: LTmin => /andP [BUG _]; des.
      apply leq_trans with (p := W task_cost task_period tsk_k R_k R) in BUG; last by done.
      by rewrite ltnn in BUG.
    Qed.

  End ResponseTimeBound.

End ResponseTimeAnalysisFP.