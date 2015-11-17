Require Import Vbase ScheduleDefs BertognaResponseTimeDefsEDF divround helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop div path tuple.

Module ResponseTimeIterationEDF.

  Import Schedule ResponseTimeAnalysisEDF.

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

    Let I (rt_bounds: seq task_with_response_time)
          (tsk: sporadic_task) (delta: time) :=
      total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds delta.
    
    Let response_time_bound (rt_bounds: seq task_with_response_time)
                            (tsk: sporadic_task) (delta: time) :=
      task_cost tsk + div_floor (I rt_bounds tsk delta) num_cpus.
    
    Let initial_state (ts: taskset_of sporadic_task) :=
      map (fun t => (t, task_cost t)) ts.

    Definition update_bound (rt_bounds: seq task_with_response_time)
                        (pair : task_with_response_time) :=
      let (tsk, R) := pair in
        (tsk, response_time_bound rt_bounds tsk R).

    Definition edf_rta_iteration (rt_bounds: seq task_with_response_time) :=
      map (update_bound rt_bounds) rt_bounds.

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

        Lemma R_list_converges : (* this is harder! Check FP file. *)
          forall tsk R rt_bounds,
            R_list_edf ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            R = task_cost tsk + div_floor (I rt_bounds tsk R) num_cpus.
        Proof.
          admit.
        Qed.

        (* The following lemma states that the response-time bounds
           computed using R_list are valid. *)
        Lemma R_list_ge_cost :
          forall rt_bounds tsk R,
            R_list_edf ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            R >= task_cost tsk.
        Proof.
          intros rt_bounds tsk R SOME PAIR.
          unfold R_list_edf in SOME.
          destruct (all R_le_deadline (iter (max_steps ts) edf_rta_iteration (initial_state ts)));
            last by ins.
          inversion SOME as [EQ]; clear SOME; subst.
          generalize dependent R.
          induction (max_steps ts) as [| step]; simpl in *.
          {
            intros R IN; unfold initial_state in IN.
            move: IN => /mapP IN; destruct IN as [tsk' IN EQ]; inversion EQ; subst.
            by apply leqnn.
          }
          {
            intros R IN.
            set prev_state := iter step edf_rta_iteration (initial_state ts).
            fold prev_state in IN, IHstep.
            unfold edf_rta_iteration at 1 in IN.
            move: IN => /mapP IN; destruct IN as [(tsk',R') IN EQ].
            inversion EQ as [[xxx EQ']]; subst.
            by apply leq_addr.
          }      
        Qed.
        
        Lemma R_list_le_deadline :
          forall rt_bounds tsk R,
            R_list_edf ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            R <= task_deadline tsk.
        Proof.
          intros rt_bounds tsk R SOME PAIR; unfold R_list_edf in SOME.
          destruct (all R_le_deadline (iter (max_steps ts)
                                            edf_rta_iteration (initial_state ts))) eqn:DEADLINE;
            last by done.
          move: DEADLINE => /allP DEADLINE.
          inversion SOME as [EQ]; rewrite -EQ in PAIR.
          by specialize (DEADLINE (tsk, R) PAIR).
        Qed.

        Lemma R_list_has_R_for_every_tsk :
          forall rt_bounds tsk,
            R_list_edf ts = Some rt_bounds ->
            tsk \in ts ->
            exists R,
              (tsk, R) \in rt_bounds.
        Proof.
          intros rt_bounds tsk SOME IN.
          unfold R_list_edf in SOME.
          destruct (all R_le_deadline (iter (max_steps ts) edf_rta_iteration (initial_state ts)));
            last by done.
          inversion SOME as [EQ]; clear SOME EQ.
          generalize dependent tsk.
          induction (max_steps ts) as [| step]; simpl in *.
          {
            intros tsk IN; unfold initial_state.
            exists (task_cost tsk).
            by apply/mapP; exists tsk.
          }
          {
            intros tsk IN.
            set prev_state := iter step edf_rta_iteration (initial_state ts).
            fold prev_state in IN, IHstep.
            specialize (IHstep tsk IN); des.
            exists (response_time_bound prev_state tsk R).
            by apply/mapP; exists (tsk, R); [by done | by f_equal].
          }
        Qed.
        
        Lemma R_list_has_response_time_bounds :
          forall rt_bounds tsk R,
            R_list_edf ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            forall j : JobIn arr_seq,
              job_task j = tsk ->
              completed job_cost rate sched j (job_arrival j + R).
        Proof.
          intros rt_bounds tsk R SOME IN j JOBj.
          unfold edf_rta_iteration in *.
          have BOUND := bertogna_cirinei_response_time_bound_edf.
          unfold is_response_time_bound_of_task, job_has_completed_by in *.
          apply BOUND with (task_cost := task_cost) (task_period := task_period)
             (task_deadline := task_deadline) (job_deadline := job_deadline)
             (job_task := job_task) (ts := ts) (tsk := tsk) (rt_bounds := rt_bounds); try (by ins).
            by ins; apply R_list_converges.
            by ins; apply R_list_ge_cost with (rt_bounds := rt_bounds).
            by ins; apply R_list_le_deadline with (rt_bounds := rt_bounds).
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
               H_all_jobs_from_taskset into ALLJOBS,
               H_test_succeeds into TEST.
        
        move => tsk INtsk j /eqP JOBtsk.
        have RLIST := (R_list_has_response_time_bounds).
        have DL := (R_list_le_deadline).
        have HAS := (R_list_has_R_for_every_tsk).
        
        destruct (R_list_edf ts) as [rt_bounds |]; last by ins.
        exploit (HAS rt_bounds tsk); [by ins | by ins | clear HAS; intro HAS; des].
        exploit (RLIST rt_bounds tsk R); [by ins | by ins | by apply JOBtsk | intro COMPLETED ].
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
        by apply COMPLETED.
      Qed.

      (* ..., and the schedulability test yields safe response-time
         bounds for each task. *)
      Theorem edf_schedulability_test_yields_response_time_bounds :
        forall tsk,
          tsk \in ts ->
          exists R,
            R <= task_deadline tsk /\
            forall (j: JobIn arr_seq),
              job_task j = tsk ->
              completed job_cost rate sched j (job_arrival j + R).
      Proof.
        intros tsk IN.
        unfold edf_schedulable in *.
        have BOUNDS := (R_list_has_response_time_bounds).
        have DL := (R_list_le_deadline).
        have HAS := (R_list_has_R_for_every_tsk).
        destruct (R_list_edf ts) as [rt_bounds |]; last by ins.
        exploit (HAS rt_bounds tsk); [by ins | by ins | clear HAS; intro HAS; des].        
        exists R; split.
          by apply DL with (rt_bounds0 := rt_bounds).
          by ins; apply (BOUNDS rt_bounds tsk).
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