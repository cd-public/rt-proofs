Require Import Vbase task schedule job priority interference util_lemmas
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Platform.

  Import ScheduleOfSporadicTask SporadicTaskset Interference Priority.

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

    (* Consider any schedule such that...*)
    Variable num_cpus: nat.
    Variable rate: Job -> processor num_cpus -> nat.
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
          backlogged job_cost rate sched j t ->
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
          backlogged job_cost rate sched j t ->
          count
              (fun j_other => higher_eq_priority t j_other j)
              (jobs_scheduled_at sched t)
            = num_cpus.

      Section BasicLemmas.

        Hypothesis H_invariant_holds :
          JLFP_JLDP_scheduling_invariant_holds.

        (* The job which is interfering has higher or equal priority to the interfered one. *)
        Lemma interfering_job_has_higher_eq_prio :
          forall j j_other t,
            backlogged job_cost rate sched j t ->
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

        (* Assume all jobs are from the taskset ... *)
        Hypothesis all_jobs_from_taskset:
          forall (j: JobIn arr_seq), job_task j \in ts.
        (* ... and jobs from the same task don't execute in parallel. *)
        Hypothesis no_intra_task_parallelism:
          jobs_of_same_task_dont_execute_in_parallel job_task sched.

        (* If a job isn't scheduled, the processor are busy with interfering tasks. *)
        Lemma cpus_busy_with_interfering_tasks :
          forall (j: JobIn arr_seq) tsk t,
            job_task j = tsk ->
            backlogged job_cost rate sched j t ->
            count
              (fun j : sporadic_task =>
                 is_interfering_task_jlfp tsk j &&
                 task_is_scheduled job_task sched j t)
              ts = num_cpus.
        Proof.
          rename all_jobs_from_taskset into FROMTS,
                 no_intra_task_parallelism into NOINTRA,
                 H_invariant_holds into INV.
          unfold JLFP_JLDP_scheduling_invariant_holds in *.
          intros j tsk t JOBtsk BACK.
          apply eq_trans with (y := count (fun j_other => higher_eq_priority t j_other j) (jobs_scheduled_at sched t));
            last by apply INV.
          unfold jobs_scheduled_at, task_is_scheduled.
          induction num_cpus.
          {
            rewrite big_ord0 /=.
            apply eq_trans with (y := count pred0 ts); last by apply count_pred0.
            apply eq_count; red; ins.
            apply negbTE; rewrite negb_and; apply/orP; right.
            apply/negP; red; intro BUG; move: BUG => /existsP BUG.
            by destruct BUG as [x0]; destruct x0.
          }
          {
            rewrite big_ord_recr /=.
            admit.
          }     
        Qed.
        
      End BasicLemmas.
      
    End JLDP.

  End SchedulingInvariants.
  
End Platform.