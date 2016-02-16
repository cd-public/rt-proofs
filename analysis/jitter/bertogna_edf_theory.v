Add LoadPath "../.." as rt.
Require Import rt.util.Vbase rt.util.lemmas rt.util.divround.
Require Import rt.model.jitter.job rt.model.jitter.task rt.model.jitter.task_arrival
               rt.model.jitter.schedule rt.model.jitter.platform rt.model.jitter.interference
               rt.model.jitter.workload rt.model.jitter.schedulability
               rt.model.jitter.priority rt.model.jitter.platform rt.model.jitter.response_time.
Require Import rt.analysis.jitter.workload_bound
               rt.analysis.jitter.interference_bound_edf.
Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisEDFJitter.

  Export JobWithJitter SporadicTaskset ScheduleWithJitter ScheduleOfSporadicTask Workload
         Schedulability ResponseTime Priority SporadicTaskArrival WorkloadBoundJitter
         InterferenceBoundEDFJitter Platform Interference.

  (* In this section, we prove that Bertogna and Cirinei's RTA yields
     safe response-time bounds. *)
  Section ResponseTimeBound.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    Variable task_jitter: sporadic_task -> nat.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    Variable job_jitter: Job -> nat.
    
    (* Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.

    (* ... in which jobs arrive sporadically and have valid parameters.
       Note: the jitter of a valid job is bounded by the jitter of its task. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period arr_seq job_task.
    Hypothesis H_valid_job_parameters:
      forall (j: JobIn arr_seq),
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost
                                                 job_deadline job_task job_jitter j.

    (* Consider any schedule such that...*)
    Variable num_cpus: nat.
    Variable sched: schedule num_cpus arr_seq.

    (* ...jobs execute after jitter and no longer than their execution costs. *)
    Hypothesis H_jobs_execute_after_jitter:
      jobs_execute_after_jitter job_jitter sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Also assume that jobs do not execute in parallel and that
       there exists at least one processor. *)
    Hypothesis H_no_parallelism:
      jobs_dont_execute_in_parallel sched.
    Hypothesis H_at_least_one_cpu :
      num_cpus > 0.

    (* Assume that we have a task set where all tasks have valid
       parameters and restricted deadlines. *)
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_all_jobs_from_taskset:
      forall (j: JobIn arr_seq), job_task j \in ts.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_restricted_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task sched tsk.
    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_cost job_task tsk sched.

    (* Assume a known response-time bound R is known...  *)
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable rt_bounds: seq task_with_response_time.

    (* ...for any task in the task set. *)
    Hypothesis H_rt_bounds_contains_all_tasks: unzip1 rt_bounds = ts.

    (* Also, assume that R is a fixed-point of the response-time recurrence, ... *)
    Let I (tsk: sporadic_task) (delta: time) :=
      total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds delta.
    Hypothesis H_response_time_is_fixed_point :
      forall tsk R,
        (tsk, R) \in rt_bounds ->
        R = task_cost tsk + div_floor (I tsk R) num_cpus.
    
    (* ..., and R is no larger than the deadline. *)
    Hypothesis H_tasks_miss_no_deadlines:
      forall tsk R,
        (tsk, R) \in rt_bounds ->
        task_jitter tsk + R <= task_deadline tsk.

    (* Assume that we have a work-conserving EDF scheduler. *)
    Hypothesis H_work_conserving: work_conserving job_cost job_jitter sched.
    Hypothesis H_edf_policy: enforces_JLDP_policy job_cost job_jitter sched (EDF job_deadline).

    (* Assume that the task set has no duplicates. Otherwise, counting
       the number of tasks that have some property does not make sense
       (for example, for stating the global scheduling invariant as
        using number of scheduled interfering tasks = number of cpus). *)
    Hypothesis H_ts_is_a_set : uniq ts.

    (* In order to prove that R is a response-time bound, we first present some lemmas. *)
    Section Lemmas.

      (* Let (tsk, R) be any task to be analyzed, with its response-time bound R. *)
      Variable tsk: sporadic_task.
      Variable R: time.
      Hypothesis H_tsk_R_in_rt_bounds: (tsk, R) \in rt_bounds.

      (* Consider any job j of tsk. *)
      Variable j: JobIn arr_seq.
      Hypothesis H_job_of_tsk: job_task j = tsk.

      (* Let t1 be the first point in time where j can actually be scheduled. *)
      Let t1 := job_arrival j + job_jitter j.

      (* Assume that job j did not complete on time, ... *)
      Hypothesis H_j_not_completed: ~~ completed job_cost sched j (t1 + R).

      (* and that it is the first job not to satisfy its response-time bound. *)
      Hypothesis H_all_previous_jobs_completed_on_time :
        forall (j_other: JobIn arr_seq) tsk_other R_other,
          job_task j_other = tsk_other ->
          (tsk_other, R_other) \in rt_bounds ->
          job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R ->
          completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other).

      (* Let's call x the interference incurred by job j due to tsk_other, ...*)
      Let x (tsk_other: sporadic_task) :=
        task_interference job_cost job_task job_jitter sched j tsk_other t1 (t1 + R).

      (* and X the total interference incurred by job j due to any task. *)
      Let X := total_interference job_cost job_jitter sched j t1 (t1 + R).

      (* Recall Bertogna and Cirinei's workload bound ... *)
      Let workload_bound (tsk_other: sporadic_task) (R_other: time) :=
        W_jitter task_cost task_period task_jitter tsk_other R_other R.

      (*... and the EDF-specific bound, ... *)
      Let edf_specific_bound (tsk_other: sporadic_task) (R_other: time) :=
        edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk tsk_other R_other.

      (* ... which combined form the interference bound. *)
      Let interference_bound (tsk_other: sporadic_task) (R_other: time) :=
        interference_bound_edf task_cost task_period task_deadline task_jitter tsk R (tsk_other, R_other). 
      
      (* Also, let ts_interf be the subset of tasks that interfere with tsk. *)
      Let ts_interf := [seq tsk_other <- ts | jldp_can_interfere_with tsk tsk_other].

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
          rename H_all_previous_jobs_completed_on_time into BEFOREok,
                 H_valid_job_parameters into PARAMS,
                 H_valid_task_parameters into TASK_PARAMS,
                 H_restricted_deadlines into RESTR,
                 H_tasks_miss_no_deadlines into NOMISS.
          unfold x, task_interference, valid_sporadic_job_with_jitter, valid_sporadic_job in *.
          have INts := bertogna_edf_tsk_other_in_ts.
          apply leq_trans with (n := workload job_task sched tsk_other t1 (t1 + R));
            first by apply task_interference_le_workload.
          apply workload_bounded_by_W with (task_deadline0 := task_deadline)
            (job_jitter0 := job_jitter) (job_cost0 := job_cost) (job_deadline0 := job_deadline);
            try (by ins); last 2 first;
            [ by apply NOMISS |
            | by ins; apply TASK_PARAMS
            | by apply RESTR
            | by apply bertogna_edf_R_other_ge_cost].
          {
            intros j0 JOB0 LT0; apply BEFOREok; try (by done).
            unfold t1 in *.
            apply leq_trans with (n := job_arrival j + job_jitter j + R); first by done.
            rewrite leq_add2r leq_add2l.
            specialize (PARAMS j); des.
            rewrite -H_job_of_tsk; apply PARAMS0.
          }
        Qed.

        (* Recall that the edf-specific interference bound also holds. *)
        Lemma bertogna_edf_specific_bound_holds :
          x tsk_other <= edf_specific_bound tsk_other R_other.
        Proof.
          by apply interference_bound_edf_bounds_interference with (job_deadline0 := job_deadline)
                                                                  (ts0 := ts); try (by done);
          [  by apply bertogna_edf_tsk_other_in_ts
          |  by apply H_tasks_miss_no_deadlines
          |  by apply leq_trans with (n := task_jitter tsk + R);
               [apply leq_addl | by apply H_tasks_miss_no_deadlines]
          |  by ins; apply H_all_previous_jobs_completed_on_time with (tsk_other := tsk_other)].
        Qed.
        
      End LemmasAboutInterferingTasks.

      (* Next we prove some lemmas that help to derive a contradiction.*)
      Section DerivingContradiction.

        (* 0) Since job j did not complete by its response time bound, it follows that
              the total interference X >= R - e_k + 1. *)
        Lemma bertogna_edf_too_much_interference : X >= R - task_cost tsk + 1.
        Proof.
          rename H_completed_jobs_dont_execute into COMP,
                 H_valid_job_parameters into PARAMS,
                 H_job_of_tsk into JOBtsk,
                 H_j_not_completed into NOTCOMP.
          unfold completed, valid_sporadic_job_with_jitter, valid_sporadic_job in *.

          (* Since j has not completed, recall the time when it is not
           executing is the total interference. *)
          exploit (complement_of_interf_equals_service job_cost job_jitter sched j t1 (t1 + R));
            try (by done); first by apply leqnn. 
          intros EQinterf.
          rewrite {2}[_ + R]addnC -addnBA // subnn addn0 in EQinterf.
          rewrite addn1.
          move: NOTCOMP; rewrite neq_ltn; move => /orP NOTCOMP; des;
            last first.
          {
            apply (leq_ltn_trans (COMP j (t1 + R))) in NOTCOMP.
            by rewrite ltnn in NOTCOMP.
          }
          apply leq_trans with (n := R - service sched j (t1 + R)); last first.
          {
            unfold service.
            rewrite -> big_cat_nat with (n := t1); [simpl | by done | by apply leq_addr].
            rewrite -> cumulative_service_before_jitter_zero with (job_jitter0 := job_jitter);
              [rewrite add0n | by done | by apply leqnn].
            rewrite EQinterf subKn; first by done.
            {
              unfold total_interference.
              apply leq_trans with (n := \sum_(t1 <= t < t1 + R) 1);
                first by apply leq_sum; ins; apply leq_b1.
              rewrite big_const_nat iter_addn mul1n addn0.
              by rewrite addnC -addnBA // subnn addn0.
            }
          }
          {
            apply ltn_sub2l; last first.
            {
              apply leq_trans with (n := job_cost j); first by ins.
              rewrite -JOBtsk; specialize (PARAMS j); des; apply PARAMS1.
            }
            apply leq_trans with (n := job_cost j); first by ins.
            apply leq_trans with (n := task_cost tsk);
              first by rewrite -JOBtsk; specialize (PARAMS j); des; apply PARAMS1.
            by rewrite bertogna_edf_R_other_ge_cost.
          }
        Qed.

        Let scheduled_task_other_than_tsk (t: time) (tsk_other: sporadic_task) :=
          task_is_scheduled job_task sched tsk_other t &&
          jldp_can_interfere_with tsk tsk_other.
      
        (* 1) At all times that j is backlogged, all processors are busy with other tasks. *)
        Lemma bertogna_edf_scheduling_invariant:
          forall t,
            t1 <= t < t1 + R ->
            backlogged job_cost job_jitter sched j t ->
            count (scheduled_task_other_than_tsk t) ts = num_cpus.
        Proof.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS,
                 H_valid_job_parameters into JOBPARAMS,
                 H_job_of_tsk into JOBtsk,
                 H_sporadic_tasks into SPO,
                 H_tsk_R_in_rt_bounds into INbounds,
                 H_all_previous_jobs_completed_on_time into BEFOREok,
                 H_tasks_miss_no_deadlines into NOMISS,
                 H_rt_bounds_contains_all_tasks into UNZIP,
                 H_restricted_deadlines into RESTR,
                 H_work_conserving into WORK.
          unfold valid_sporadic_job_with_jitter, valid_sporadic_job in *.
          move => t /andP [LEt LTt] BACK.
          unfold scheduled_task_other_than_tsk in *.
          eapply platform_cpus_busy_with_interfering_tasks; try (by done);
            [ by apply WORK
            | by done
            | by apply SPO 
            | apply PARAMS; rewrite -JOBtsk; apply FROMTS
            | by apply JOBtsk | by apply BACK | ].
          {
            intros j0 tsk0 TSK0 LE.
            cut (tsk0 \in unzip1 rt_bounds); [intro IN | by rewrite UNZIP -TSK0 FROMTS].
            move: IN => /mapP [p IN EQ]; destruct p as [tsk' R0]; simpl in *; subst tsk'.
            apply completion_monotonic with (t0 := job_arrival j0 + task_jitter tsk0 + R0); try (by done).
            {
              rewrite -addnA leq_add2l TSK0.
              apply leq_trans with (n := task_deadline tsk0); first by apply NOMISS.
              by apply RESTR; rewrite -TSK0 FROMTS.
            }
            {
              apply BEFOREok with (tsk_other := tsk0); try (by done).
              apply leq_trans with (n := t1 + R); last first.
              {
                  rewrite leq_add2r leq_add2l -JOBtsk.
                  by specialize (JOBPARAMS j); des.
              }
              apply leq_ltn_trans with (n := t); last by done.
              apply leq_trans with (n := job_arrival j0 + task_period tsk0);
                last by done.
              rewrite -addnA leq_add2l.
              apply leq_trans with (n := task_deadline tsk0); first by apply NOMISS.
              by apply RESTR; rewrite -TSK0; apply FROMTS.
            }
          }
        Qed.
      
        (* 2) Next, we prove that the sum of the interference of each task is equal
          to the total interference multiplied by the number of processors. This
          holds because interference only occurs when all processors are busy. *)
        Lemma bertogna_edf_all_cpus_busy :
          \sum_(tsk_k <- ts_interf) x tsk_k = X * num_cpus.
        Proof.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS,
                 H_valid_job_parameters into JOBPARAMS,
                 H_job_of_tsk into JOBtsk,
                 H_sporadic_tasks into SPO,
                 H_tsk_R_in_rt_bounds into INbounds,
                 H_all_previous_jobs_completed_on_time into BEFOREok,
                 H_tasks_miss_no_deadlines into NOMISS,
                 H_restricted_deadlines into RESTR.
          unfold sporadic_task_model, valid_sporadic_job_with_jitter, valid_sporadic_job in *.
          unfold x, X, total_interference, task_interference.
          rewrite -big_mkcond -exchange_big big_distrl /=.
          rewrite [\sum_(_ <= _ < _ | backlogged _ _ _ _ _) _]big_mkcond.
          apply eq_big_nat; move => t LEt.
          destruct (backlogged job_cost job_jitter sched j t) eqn:BACK;
            last by rewrite (eq_bigr (fun i => 0));
              [by rewrite big_const_seq iter_addn mul0n addn0 | by done].
          rewrite big_mkcond mul1n /=.
          rewrite big_filter big_mkcond.
          rewrite (eq_bigr (fun i => if (scheduled_task_other_than_tsk t i) then 1 else 0)); last first.
          {
            unfold scheduled_task_other_than_tsk; intros i _; clear -i.
            by destruct (task_is_scheduled job_task sched i t);
              rewrite ?andFb ?andTb ?andbT //; desf.
          }
          rewrite -big_mkcond sum1_count.
          by apply bertogna_edf_scheduling_invariant.
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
          rename H_all_jobs_from_taskset into FROMTS,
                 H_valid_task_parameters into PARAMS,
                 H_job_of_tsk into JOBtsk,
                 H_sporadic_tasks into SPO,
                 H_tsk_R_in_rt_bounds into INbounds,
                 H_all_previous_jobs_completed_on_time into BEFOREok,
                 H_tasks_miss_no_deadlines into NOMISS,
                 H_restricted_deadlines into RESTR.
          unfold sporadic_task_model in *.
          intros delta HAS.
          set some_interference_A := fun t =>
              backlogged job_cost job_jitter sched j t &&
              has (fun tsk_k => ((x tsk_k >= delta) &&
                       task_is_scheduled job_task sched tsk_k t)) ts_interf.      
          set total_interference_B := fun t =>
              backlogged job_cost job_jitter sched j t *
              count (fun tsk_k => (x tsk_k < delta) &&
                task_is_scheduled job_task sched tsk_k t) ts_interf.

          rewrite -has_count in HAS.
          apply leq_trans with ((\sum_(t1 <= t < t1 + R)
                                some_interference_A t) * (num_cpus - cardGE delta)).
          {
            rewrite leq_mul2r; apply/orP; right.
            move: HAS => /hasP HAS; destruct HAS as [tsk_a INa LEa].
            apply leq_trans with (n := x tsk_a); first by apply LEa.
            unfold x, task_interference, some_interference_A.
            apply leq_sum; ins.
            destruct (backlogged job_cost job_jitter sched j i);
              [rewrite 2!andTb | by ins].
            destruct (task_is_scheduled job_task sched tsk_a i) eqn:SCHEDa;
              [apply eq_leq; symmetry | by ins].
            apply/eqP; rewrite eqb1.
            by apply/hasP; exists tsk_a; last by apply/andP.
          }
          apply leq_trans with (\sum_(t1 <= t < t1 + R)
                                     total_interference_B t).
          {
            rewrite big_distrl /=.
            rewrite big_nat_cond [\sum_(_ <= _ < _ | true)_]big_nat_cond.
            apply leq_sum; move => t /andP [LEt _].
            unfold some_interference_A, total_interference_B. 
            destruct (backlogged job_cost job_jitter sched j t) eqn:BACK;
              [rewrite andTb mul1n | by done].
            destruct (has (fun tsk_k : sporadic_task => (delta <= x tsk_k) &&
                       task_is_scheduled job_task sched tsk_k t) ts_interf) eqn:HAS';
              last by done.
            rewrite mul1n; move: HAS => /hasP HAS.
            destruct HAS as [tsk_k INk LEk].

            have COUNT := bertogna_edf_scheduling_invariant t LEt BACK.

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
              destruct (backlogged job_cost job_jitter sched j t); last by ins.
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
          \sum_((tsk_other, R_other) <- rt_bounds | jldp_can_interfere_with tsk tsk_other)
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
            assert (FILTER: filter (jldp_can_interfere_with tsk) (unzip1 rt_bounds) =
                            filter (jldp_can_interfere_with tsk) ts).
              by f_equal.
            unfold ts_interf; rewrite -FILTER; clear FILTER.
            rewrite -[\sum_(_ <- rt_bounds | _)_]big_filter.
            assert (SUBST: [seq i <- rt_bounds
                   | let '(tsk_other, _) := i in
                          jldp_can_interfere_with tsk tsk_other] = [seq i <- rt_bounds
                             | jldp_can_interfere_with tsk (fst i)]).
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
                              (tsk_other \in ts) && jldp_can_interfere_with tsk tsk_other &&
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
        response_time_bounded_by tsk (task_jitter tsk + R).
      Proof.
        rename H_valid_job_parameters into JOBPARAMS.
        unfold valid_sporadic_job_with_jitter, valid_sporadic_job in *.
        intros j JOBtsk.

        rewrite addnA.
        (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
        remember (job_arrival j + task_jitter tsk + R) as ctime.

        revert H_tsk_R_in_rt_bounds.
        generalize dependent R; generalize dependent tsk; generalize dependent j.
      
        (* Now, we apply strong induction on the absolute response-time bound. *)
        induction ctime as [ctime IH] using strong_ind.

        intros j tsk' JOBtsk R' EQc INbounds; subst ctime.

        (* First, let's simplify the induction hypothesis. *)
        assert (BEFOREok: forall (j0: JobIn arr_seq) tsk R0,
                                 job_task j0 = tsk ->
                               (tsk, R0) \in rt_bounds ->
                               job_arrival j0 + task_jitter tsk + R0 < job_arrival j + task_jitter tsk' + R' ->
                               service sched j0 (job_arrival j0 + task_jitter tsk + R0) == job_cost j0).
        {
            by ins; apply IH with (tsk := tsk0) (R := R0).
        }
        clear IH.
        
        (* The proof follows by contradiction. Assume that job j does not complete by its
           response-time bound. By the induction hypothesis, all jobs with absolute
           response-time bound t < (job_arrival j + R) have correct response-time bounds. *)
        destruct (completed job_cost sched j (job_arrival j + job_jitter j + R')) eqn:NOTCOMP.
        {
          apply completion_monotonic with (t := job_arrival j + job_jitter j + R'); try (by done).
          rewrite leq_add2r leq_add2l.
          specialize (JOBPARAMS j); des.
          by rewrite -JOBtsk; apply JOBPARAMS0.
        }
        apply negbT in NOTCOMP; exfalso.
        
        (* Next, we derive a contradiction using the previous lemmas. *)
        exploit (bertogna_edf_exists_task_that_exceeds_bound tsk' R' INbounds j JOBtsk NOTCOMP).
        {
          by ins; apply IH with (tsk := tsk_other) (R := R_other).
        } 
        intro EX; destruct EX as [tsk_other [R_other [HP LTmin]]].
        unfold interference_bound_edf, interference_bound_generic in LTmin.
        rewrite minnAC in LTmin; apply min_lt_same in LTmin.
        have BASICBOUND := bertogna_edf_workload_bounds_interference tsk' R' j JOBtsk BEFOREok tsk_other R_other HP.
        have EDFBOUND := bertogna_edf_specific_bound_holds tsk' R' INbounds j JOBtsk BEFOREok tsk_other R_other HP.
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

End ResponseTimeAnalysisEDFJitter.