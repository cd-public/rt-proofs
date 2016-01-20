Require Import Vbase task schedule job priority interference task_arrival
               util_lemmas
               ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module Platform.

  Import Job ScheduleOfSporadicTask SporadicTaskset SporadicTaskArrival Interference Priority.

  Section SchedulingInvariants.
    
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

    (* Consider any schedule. *)
    Variable num_cpus: nat.
    Variable sched: schedule num_cpus arr_seq.

    (* Assume that we have a task set where all tasks have valid
       parameters and restricted deadlines. *)
    Variable ts: taskset_of sporadic_task.

    Section FP.

      (* Given an FP policy, ...*)
      Variable higher_eq_priority: fp_policy sporadic_task.
 
      (* the global scheduling invariant states that if a job is
         backlogged, then all the processors are busy with jobs
         of higher-priority tasks. *)
      Definition FP_scheduling_invariant_holds :=
        forall (tsk: sporadic_task) (j: JobIn arr_seq) (t: time),
          tsk \in ts ->
          job_task j = tsk ->
          backlogged job_cost sched j t ->
          count
            (fun tsk_other : sporadic_task =>
               is_interfering_task_fp higher_eq_priority tsk tsk_other &&
                 task_is_scheduled job_task sched tsk_other t) ts = num_cpus.

    End FP.

    Section JLDP.

      (* Given a JLFP/JLDP policy, ...*)
      Variable higher_eq_priority: jldp_policy arr_seq.

      (* ... the global scheduling invariant states that at any time t,
         if a job J is backlogged, then all processors are busy with
         jobs of higher-priority. *)
      Definition JLFP_JLDP_scheduling_invariant_holds :=
        forall (j: JobIn arr_seq) (t: time),
          backlogged job_cost sched j t ->
          count
              (fun j_other => higher_eq_priority t j_other j)
              (jobs_scheduled_at sched t)
            = num_cpus.

    End JLDP.

    Section WorkConserving.

      (* A scheduler is work-conserving iff when a job j is backlogged,
         all processors are busy with other jobs. *)
      Definition is_work_conserving :=
        forall (j: JobIn arr_seq) (t: time),
          backlogged job_cost sched j t ->
          size (jobs_scheduled_at sched t) = num_cpus.
      
    End WorkConserving.
    
    Section Lemmas.

      Section InterferingJobHasHigherPriority.

        Variable higher_eq_priority: jldp_policy arr_seq.
        
        Hypothesis H_invariant_holds :
          JLFP_JLDP_scheduling_invariant_holds higher_eq_priority.

        (* The job which is interfering has higher or equal priority to the interfered one. *)
        Lemma interfering_job_has_higher_eq_prio :
          forall j j_other t,
            backlogged job_cost sched j t ->
            scheduled sched j_other t ->
            higher_eq_priority t j_other j.
        Proof.
          intros j j_other t BACK SCHED.
          exploit H_invariant_holds; [by apply BACK | intro COUNT].
          destruct (higher_eq_priority t j_other j) eqn:LOW; first by done.
          apply negbT in LOW.
          generalize SCHED; unfold scheduled in SCHED; intro SCHED'.
          move: SCHED => /existsP EX; destruct EX as [cpu H].
          move: H => /andP [_ /eqP SCHED].
          assert (ATMOST: size (jobs_scheduled_at sched t) <= num_cpus).
          {
            apply size_bigcat_ord; [by apply cpu|].
            by ins; unfold make_sequence; destruct (sched x t).
          }
          rewrite -(count_predC (fun j_other => higher_eq_priority t j_other j)) COUNT in ATMOST.
          assert (BUG: num_cpus < num_cpus).
          {
            apply leq_trans with (n := num_cpus + count (predC (fun j_other => higher_eq_priority t j_other j)) (jobs_scheduled_at sched t));
              last by done.
            rewrite -{1}[num_cpus]addn0 ltn_add2l -has_count.
            apply/hasP; exists j_other; last by done.
            unfold jobs_scheduled_at.
            apply mem_bigcat_ord with (j := cpu);
              first by apply ltn_ord.
            by unfold make_sequence; rewrite SCHED mem_seq1 eq_refl.
          }
          by rewrite ltnn in BUG.
        Qed.

      End InterferingJobHasHigherPriority.
      
      Section JobInvariantAsTaskInvariant.

        Variable higher_eq_priority: jldp_policy arr_seq.
        
        Hypothesis H_invariant_holds :
          JLFP_JLDP_scheduling_invariant_holds higher_eq_priority.
        
        (* Assume the task set has no duplicates, ... *)
        Hypothesis H_ts_is_a_set: uniq ts.
        (* ... and all jobs come from the taskset. *)
        Hypothesis H_all_jobs_from_taskset:
          forall (j: JobIn arr_seq), job_task j \in ts.

        (* Suppose that a single job does not execute in parallel, ...*)
        Hypothesis H_no_parallelism:
          jobs_dont_execute_in_parallel sched.
        (* ... jobs from the same task do not execute in parallel, ... *)
        Hypothesis H_no_intra_task_parallelism:
          jobs_of_same_task_dont_execute_in_parallel job_task sched.
        (* ... and jobs do not execute after completion. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
          
        (* Assume that the schedule satisfies the sporadic task model ...*)
        Hypothesis H_sporadic_tasks:
          sporadic_task_model task_period arr_seq job_task.

        (* and task precedence constraints. *)
        Hypothesis H_task_precedence:
          task_precedence_constraints job_cost job_task sched.

        (* Consider a valid task tsk, ...*)
        Variable tsk: sporadic_task.
        Hypothesis H_valid_task: is_valid_sporadic_task task_cost task_period task_deadline tsk.
          
        (*... whose job j ... *)
        Variable j: JobIn arr_seq.
        Variable H_job_of_tsk: job_task j = tsk.

        (*... is backlogged at time t. *)
        Variable t: time.
        Hypothesis H_j_backlogged: backlogged job_cost sched j t.
           
        (* Assume that any previous jobs of tsk have completed by time t. *)
        Hypothesis H_all_previous_jobs_completed :
          forall (j0: JobIn arr_seq),
            job_task j0 = tsk ->
            job_arrival j0 < job_arrival j ->
            completed job_cost sched j0 t.
        
        (* If a job isn't scheduled, the processor are busy with interfering tasks. *)
        Lemma cpus_busy_with_interfering_tasks :      
          count
            (fun j : sporadic_task =>
               is_interfering_task_jlfp tsk j &&
               task_is_scheduled job_task sched j t)
            ts = num_cpus.
        Proof.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_no_parallelism into SEQUENTIAL,
                 H_no_intra_task_parallelism into NOINTRA,
                 H_invariant_holds into INV,
                 H_j_backlogged into BACK,
                 H_job_of_tsk into JOBtsk,
                 H_task_precedence into PREC,
                 H_sporadic_tasks into SPO,
                 H_valid_task into PARAMS,
                 H_all_previous_jobs_completed into PREV,
                 H_completed_jobs_dont_execute into COMP.
          unfold JLFP_JLDP_scheduling_invariant_holds,
                 valid_sporadic_job, valid_realtime_job,
                 task_precedence_constraints, completed_jobs_dont_execute,
                 sporadic_task_model, is_valid_sporadic_task,
                 jobs_of_same_task_dont_execute_in_parallel,
                 jobs_dont_execute_in_parallel in *.

          clear PREC.
          apply/eqP; rewrite eqn_leq; apply/andP; split.
          {
            apply leq_trans with (n := count (fun x => task_is_scheduled job_task sched x t) ts);
              first by apply sub_count; first by red; move => x /andP [_ SCHED].    
            unfold task_is_scheduled.
            apply count_exists; first by done.
            {
              intros cpu x1 x2 SCHED1 SCHED2.
              unfold schedules_job_of_tsk in *.
              destruct (sched cpu t); last by done.
              move: SCHED1 SCHED2 => /eqP SCHED1 /eqP SCHED2.
              by rewrite -SCHED1 -SCHED2.
            }
          }
          {
            apply leq_trans with (n := count ((higher_eq_priority t)^~ j) (jobs_scheduled_at sched t)).
            rewrite -> INV with (j := j) (t := t);
              [by apply leqnn | by done]. 

            apply leq_trans with (n := count (fun j: JobIn arr_seq => is_interfering_task_jlfp tsk (job_task j) && task_is_scheduled job_task sched (job_task j) t) (jobs_scheduled_at sched t)).
            {
              assert (SUBST: count ((higher_eq_priority t)^~ j) (jobs_scheduled_at sched t) = count (fun x => (higher_eq_priority t x j) && (x \in jobs_scheduled_at sched t)) (jobs_scheduled_at sched t)).
              {
                by apply eq_in_count; red; intros x IN; rewrite IN andbT.
              } rewrite SUBST; clear SUBST.

              apply sub_count; red; move => j_hp /andP [HP IN].
              rewrite mem_scheduled_jobs_eq_scheduled in IN.
              rename IN into SCHED.
              apply/andP; split; last first.
              {
                move: SCHED => /exists_inP SCHED.
                destruct SCHED as [cpu INcpu SCHED].
                move: SCHED => /eqP SCHED.
                apply/exists_inP; exists cpu; first by done.
                by unfold schedules_job_of_tsk; rewrite SCHED.
              }
              {
                unfold is_interfering_task_jlfp.
                destruct (j == j_hp) eqn:EQjob.
                {
                  move: EQjob => /eqP EQjob; subst.
                  unfold backlogged in *.
                  by rewrite SCHED andbF in BACK. 
                }
                apply negbT in EQjob.
                apply/negP; unfold not; move => /eqP SAMEtsk.
                destruct (ltnP (job_arrival j) (job_arrival j_hp)) as [LTarr | GEarr].
                {
                  move: BACK => /andP [PEND NOTSCHED].
                  admit.
                  (*apply PREC with (t := t) in LTarr;
                    [ | by rewrite SAMEtsk JOBtsk | by done].
                  by rewrite SCHED in LTarr.*)
                } subst tsk.
                exploit (SPO j_hp j); try (by done).
                {
                  by unfold not; intro BUG; subst; rewrite eq_refl in EQjob.
                }
                intros INTER.
                exploit (PREV j_hp SAMEtsk).
                {
                  apply leq_trans with (n := job_arrival j_hp + task_period (job_task j_hp)); last by done.
                  by rewrite -addn1 leq_add2l SAMEtsk; des.
                }
                intros COMPLETED.
                have BUG := COMP j_hp t.+1.
                rewrite leqNgt in BUG; move: BUG => /negP BUG; apply BUG.
                unfold service; rewrite -addn1 big_nat_recr ?leq0n // /=.
                apply leq_add;
                  last by rewrite lt0n -not_scheduled_no_service negbK.
                move: COMPLETED => /eqP COMPLETED.
                by rewrite -COMPLETED leqnn.
              }
            }
            have MAP := count_map (fun (x: JobIn arr_seq) => job_task x) (fun x => is_interfering_task_jlfp tsk x && task_is_scheduled job_task sched x t). 
            rewrite -MAP; clear MAP.
            apply count_sub_uniqr.
            {
              rewrite map_inj_in_uniq; first by apply scheduled_jobs_uniq.
              by red; ins; apply NOINTRA with (t := t);
                rewrite // -mem_scheduled_jobs_eq_scheduled.
            }
            {
              red; intros x IN.
              move: IN => /mapP IN; destruct IN as [j' _ EQx].
              by rewrite EQx; apply FROMTS.
            }
          }
        Qed.

      End JobInvariantAsTaskInvariant.

    End Lemmas.

  End SchedulingInvariants.
  
End Platform.