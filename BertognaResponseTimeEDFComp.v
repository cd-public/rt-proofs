Require Import Vbase ScheduleDefs BertognaResponseTimeDefs divround helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop div path tuple.

Module ResponseTimeIterationEDF.

  Import Schedule ResponseTimeAnalysis.

  Section Analysis.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    Let task_with_response_time := (sporadic_task * nat)%type.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.

    Variable num_cpus: nat.

    (* Next we define the fixed-point iteration for computing
       Bertogna's response-time bound for any task in ts. *)
    
    (*Computation of EDF on list of pairs (T,R)*)
    
    Let max_steps (ts: taskset_of sporadic_task) :=
      \max_(tsk <- ts) task_deadline tsk.

    Let response_time_bound (tsk: sporadic_task) (rt_bounds: seq task_with_response_time)
                            (delta: time) :=
      task_cost tsk +
      div_floor
       (total_interference_bound_jlfp task_cost task_period tsk rt_bounds delta)
       num_cpus.
    
    Let initial_state (ts: taskset_of sporadic_task) :=
      map (fun t => (t, task_cost t)) ts.
    
    Definition edf_rta_iteration (rt_bounds: seq task_with_response_time) :=
      map (fun pair : task_with_response_time =>
             let (tsk, R) := pair in
               (tsk, response_time_bound tsk rt_bounds R))
          rt_bounds.

    Definition R_le_deadline (pair: task_with_response_time) :=
      let (tsk, R) := pair in
        R <= task_deadline tsk.
    
    Definition R_list_edf (ts: taskset_of sporadic_task) :=
      let R_values := iter (max_steps ts) edf_rta_iteration (initial_state ts) in
        if (all R_le_deadline R_values) then
          Some R_values
        else None.
    
    (* The schedulability test simply checks if we got a list of
       response-time bounds (i.e., if the computation did not fail). *)
    Definition edf_schedulable (ts: taskset_of sporadic_task) :=
      R_list_edf ts != None.
    
    Section AuxiliaryLemmas.

    End AuxiliaryLemmas.
    
    Section Proof.

      (* Consider a task set ts. *)
      Variable ts: taskset_of sporadic_task.
      
      (* Assume the task set has no duplicates, ... *)
      Hypothesis H_ts_is_a_set: uniq ts.

      (* ...all tasks have valid parameters, ... *)
      Hypothesis H_valid_task_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline ts.

      (* ...restricted deadlines, ...*)
      Hypothesis H_restricted_deadlines:
        forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

      (* ...and tasks are ordered by increasing priorities. *)
      (*Hypothesis H_sorted_ts: sorted EDF ts.*)

      (* Next, consider any arrival sequence such that...*)
      Context {arr_seq: arrival_sequence Job}.

     (* ...all jobs come from task set ts, ...*)
      Hypothesis H_all_jobs_from_taskset:
        forall (j: JobIn arr_seq), job_task j \in ts.
      
      (* ...they have valid parameters,...*)
      Hypothesis H_valid_job_parameters:
        forall (j: JobIn arr_seq),
          valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
      
      (* ... and satisfy the sporadic task model.*)
      Hypothesis H_sporadic_tasks:
        sporadic_task_model task_period arr_seq job_task.
      
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
               is_interfering_task_jlfp tsk tsk_other &&
               task_is_scheduled job_task sched tsk_other t) ts = num_cpus.

      Definition no_deadline_missed_by_task (tsk: sporadic_task) :=
        task_misses_no_deadline job_cost job_deadline job_task rate sched tsk.
      Definition no_deadline_missed_by_job :=
        job_misses_no_deadline job_cost job_deadline rate sched.

      Section HelperLemma.
        
        (* The following lemma states that the response-time bounds
           computed using R_list are valid. *)
        Lemma R_list_has_response_time_bounds :
          forall rt_bounds tsk R,
            R_list_edf ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            forall j : JobIn arr_seq,
              job_task j = tsk ->
              completed job_cost rate sched j (job_arrival j + R).
        Proof.
          rename H_valid_job_parameters into JOBPARAMS,
                 H_valid_task_parameters into TASKPARAMS,
                 H_restricted_deadlines into RESTR,
                 H_completed_jobs_dont_execute into COMP,
                 H_jobs_must_arrive_to_execute into MUSTARRIVE,
                 H_global_scheduling_invariant into INVARIANT,
                 (*H_transitive into TRANS,
                 H_unique_priorities into UNIQ,
                 H_total into TOTAL,*)
                 H_all_jobs_from_taskset into ALLJOBS,
                 H_ts_is_a_set into SET.
          clear ALLJOBS.

          intros rt_bounds tsk R SOME IN j JOBj.
          unfold R_list_edf, edf_rta_iteration in *.
          assert (FIXED: forall tsk R,
                           (tsk, R) \in rt_bounds ->
                           R = task_cost tsk + response_time_bound tsk rt_bounds R).
          {
            admit.
          }
          generalize dependent j.
          generalize dependent R.
          generalize dependent tsk.

          cut ((forall tsk R, (tsk, R) \in rt_bounds -> R = task_cost tsk + response_time_bound tsk rt_bounds R) -> (forall tsk R (j: JobIn arr_seq), (tsk, R) \in rt_bounds -> job_task j = tsk -> completed job_cost rate sched j (job_arrival j + R))).
          {
            by intro ASSUMP; ins; apply ASSUMP with (tsk := tsk).
          }
          {
            ins.
            admit.
          }

          (*
          ins. 
          unfold edf_schedulable, R_list_edf in *.


          ins. 
          induction ts as [| ts' tsk_i IH] using last_ind.
          {
            intros rt_bounds tsk R SOME IN.
            by inversion SOME; subst; rewrite in_nil in IN.
          }
          {
           intros rt_bounds tsk R SOME IN j JOBj.
             destruct (lastP rt_bounds) as [| hp_bounds (tsk_lst, R_lst)];
              first by rewrite in_nil in IN.
            rewrite mem_rcons in_cons in IN; move: IN => /orP IN.
            destruct IN as [LAST | BEGINNING]; last first.
            {
              apply IH with (rt_bounds := hp_bounds) (tsk := tsk); try (by ins).
              by rewrite rcons_uniq in SET; move: SET => /andP [_ SET].
              by ins; red; ins; apply TASKPARAMS; rewrite mem_rcons in_cons; apply/orP; right.
              by ins; apply RESTR; rewrite mem_rcons in_cons; apply/orP; right.
              by apply sorted_rcons_prefix in SORT.
              {
                intros tsk0 j0 t IN0 JOB0 BACK0.
                exploit (INVARIANT tsk0 j0 t); try (by ins);
                  [by rewrite mem_rcons in_cons; apply/orP; right | intro INV].
                rewrite -cats1 count_cat /= in INV.
                unfold is_interfering_task_fp in INV.
                generalize SOME; apply R_list_rcons_task in SOME; subst tsk_i; intro SOME.
                assert (HP: higher_eq_priority tsk_lst tsk0 = false).
                {
                  apply order_sorted_rcons with (x := tsk0) in SORT; [|by ins | by ins].
                  apply negbTE; apply/negP; unfold not; intro BUG.
                  exploit UNIQ; [by apply/andP; split; [by apply SORT | by ins] | intro EQ].
                  by rewrite rcons_uniq -EQ IN0 in SET.
                }              
                by rewrite HP 2!andFb 2!addn0 in INV.
              }
              by apply R_list_rcons_prefix in SOME.
            }
            {
              move: LAST => /eqP LAST.
              inversion LAST as [[EQ1 EQ2]].
              rewrite -> EQ1 in *; rewrite -> EQ2 in *; clear EQ1 EQ2 LAST.
              generalize SOME; apply R_list_rcons_task in SOME; subst tsk_i; intro SOME.
              generalize SOME; apply R_list_rcons_prefix in SOME; intro SOME'.
              have BOUND := bertogna_cirinei_response_time_bound_fp.
              unfold is_response_time_bound_of_task, job_has_completed_by in BOUND.
              apply BOUND with (task_cost := task_cost) (task_period := task_period) (task_deadline := task_deadline) (job_deadline := job_deadline) (job_task := job_task) (tsk := tsk_lst)
                               (ts := rcons ts' tsk_lst) (hp_bounds := hp_bounds)
                               (higher_eq_priority := higher_eq_priority); clear BOUND; try (by ins).
              by apply R_list_unzip1 with (R := R_lst).
              {
                intros hp_tsk R0 HP j0 JOB0.
                apply IH with (rt_bounds := hp_bounds) (tsk := hp_tsk); try (by ins).
                by rewrite rcons_uniq in SET; move: SET => /andP [_ SET].
                by red; ins; apply TASKPARAMS; rewrite mem_rcons in_cons; apply/orP; right.
                by ins; apply RESTR; rewrite mem_rcons in_cons; apply/orP; right.
                by apply sorted_rcons_prefix in SORT.
                {
                  intros tsk0 j1 t IN0 JOB1 BACK0.
                  exploit (INVARIANT tsk0 j1 t); try (by ins);
                    [by rewrite mem_rcons in_cons; apply/orP; right | intro INV].
                  rewrite -cats1 count_cat /= addn0 in INV.
                  unfold is_interfering_task_fp in INV.
                  assert (NOINTERF: higher_eq_priority tsk_lst tsk0 = false).
                  {
                    apply order_sorted_rcons with (x := tsk0) in SORT; [|by ins | by ins].
                    apply negbTE; apply/negP; unfold not; intro BUG.
                    exploit UNIQ; [by apply/andP; split; [by apply BUG | by ins] | intro EQ].
                    by rewrite rcons_uniq EQ IN0 in SET.
                  }
                  by rewrite NOINTERF 2!andFb addn0 in INV.
                }
              }
              by ins; apply R_list_ge_cost with (ts' := ts') (rt_bounds := hp_bounds).
              by ins; apply R_list_le_deadline with (ts' := ts') (rt_bounds := hp_bounds).
              {
                ins; exploit (INVARIANT tsk_lst j0 t); try (by ins).
                by rewrite mem_rcons in_cons; apply/orP; left.
              }
              {
                rewrite [R_lst](R_list_rcons_response_time ts' hp_bounds tsk_lst); last by ins.
                rewrite per_task_rta_fold.
                apply per_task_rta_converges with (ts' := ts'); try (by ins).
                {
                  red; ins; apply TASKPARAMS.
                  by rewrite mem_rcons in_cons; apply/orP; right.
                }
                apply R_list_le_deadline with (ts' := rcons ts' tsk_lst)
                                            (rt_bounds := rcons hp_bounds (tsk_lst, R_lst));
                  first by apply SOME'.
                rewrite mem_rcons in_cons; apply/orP; left; apply/eqP.
                f_equal; symmetry.
                by apply R_list_rcons_response_time with (ts' := ts'). 
              }
            }
          }*)
        Qed.

      End HelperLemma.
      
      (* If the schedulability test suceeds, ...*)
      Hypothesis H_test_succeeds: edf_schedulable ts.
      
      (*..., then no task misses its deadline,... *)
      Theorem taskset_schedulable_by_fp_rta :
        forall tsk, tsk \in ts -> no_deadline_missed_by_task tsk.
      Proof.
        unfold no_deadline_missed_by_task, task_misses_no_deadline,
               job_misses_no_deadline, completed,
               edf_schedulable,
               valid_sporadic_job in *.
        rename H_valid_job_parameters into JOBPARAMS,
               H_valid_task_parameters into TASKPARAMS,
               H_restricted_deadlines into RESTR,
               H_completed_jobs_dont_execute into COMP,
               H_jobs_must_arrive_to_execute into MUSTARRIVE,
               H_global_scheduling_invariant into INVARIANT,
               (*H_sorted_ts into SORT,
               H_transitive into TRANS,
               H_unique_priorities into UNIQ,
               H_total into TOTAL,*)
               H_all_jobs_from_taskset into ALLJOBS,
               H_test_succeeds into TEST.

        admit.
        
        (*move => tsk INtsk j /eqP JOBtsk.
        have RLIST := (R_list_has_response_time_bounds).
        have NONEMPTY := (R_list_non_empty ts).
        have DL := (R_list_le_deadline ts).

        destruct (R_list ts) as [rt_bounds |]; last by ins.
        exploit (NONEMPTY rt_bounds tsk); [by ins | intros [EX _]; specialize (EX INtsk); des].
        exploit (RLIST rt_bounds tsk R); [by ins | by ins | by apply JOBtsk | intro COMPLETED].
        exploit (DL rt_bounds tsk R); [by ins | by ins | clear DL; intro DL].
        
        rewrite eqn_leq; apply/andP; split; first by apply service_interval_le_cost.
        apply leq_trans with (n := service rate sched j (job_arrival j + R)); last first.
        {
          unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
          apply service_monotonic; rewrite leq_add2l.
          specialize (JOBPARAMS j); des; rewrite JOBPARAMS1.
          by rewrite JOBtsk.
        }
        rewrite leq_eqVlt; apply/orP; left; rewrite eq_sym.
        by apply COMPLETED.*)
      Qed.

      (* ..., and the schedulability test yields safe response-time
         bounds for each task. *)
      Theorem fp_schedulability_test_yields_response_time_bounds :
        forall tsk,
          tsk \in ts ->
          exists R,
            R <= task_deadline tsk /\
            forall (j: JobIn arr_seq),
              job_task j = tsk ->
              completed job_cost rate sched j (job_arrival j + R).
      Proof.
        intros tsk IN.
        admit.
      (*unfold edf_schedulable in *.
        have TASKS := R_list_non_empty ts.
        have BOUNDS := (R_list_has_response_time_bounds).
        have DL := (R_list_le_deadline ts).
        destruct (R_list ts) as [rt_bounds |]; last by ins.
        exploit (TASKS rt_bounds tsk); [by ins | clear TASKS; intro EX].
        destruct EX as [EX _]; specialize (EX IN); des.
        exists R; split.
          by apply DL with (rt_bounds0 := rt_bounds).
          by ins; apply (BOUNDS rt_bounds tsk). *)
      Qed.

      (* For completeness, since all jobs of the arrival sequence
         are spawned by the task set, we conclude that no job misses
         its deadline. *)
      Theorem jobs_schedulable_by_fp_rta :
        forall (j: JobIn arr_seq), no_deadline_missed_by_job j.
      Proof.
        intros j.
        have SCHED := taskset_schedulable_by_fp_rta.
        unfold no_deadline_missed_by_task, task_misses_no_deadline in *.
        apply SCHED with (tsk := job_task j); last by rewrite eq_refl.
        by apply H_all_jobs_from_taskset.
      Qed.
      
    End Proof.

  End Analysis.

End ResponseTimeIterationEDF.