Require Import Vbase task schedule job priority interference task_arrival
               platform interference_edf util_lemmas
               ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(* In this file, we prove lemmas about the processor platform under EDF scheduling. *)
Module PlatformEDF.

  Import Job ScheduleOfSporadicTask SporadicTaskset SporadicTaskArrival Interference Priority Platform InterferenceEDF.

  Section Lemmas.
    
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

    (* Assume all jobs have valid parameters, ...*)
      Hypothesis H_valid_job_parameters:
        forall (j: JobIn arr_seq),
          valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
    
    Let higher_eq_priority := @EDF Job arr_seq job_deadline.

    (* Assume that the schedule satisfies the global scheduling invariant
       for EDF, i.e., if any job of tsk is backlogged, every processor
       must be busy with jobs with no larger absolute deadline. *)
    Hypothesis H_global_scheduling_invariant:
      JLFP_JLDP_scheduling_invariant_holds job_cost num_cpus sched higher_eq_priority.

    (* In this section, we show that under EDF, intra-task parallelism
       is equivalent to task precedence constraints (as long as two jobs
       of the same task do not arrive at the same time). *)
    Section IntraTaskParallelismAndTaskPrecedenceUnderEDF.

      Section SufficientCase.

        (* Assume that jobs of same task do not execute in parallel. *)
        Hypothesis H_no_intra_task_parallelism:
          jobs_of_same_task_dont_execute_in_parallel job_task sched.

        (* The EDF scheduling invariant together with no intra-task
           parallelism imply task precedence constraints. *)
        Lemma edf_no_intratask_parallelism_implies_task_precedence :
          task_precedence_constraints job_cost job_task sched.
        Proof.
          rename H_valid_job_parameters into JOBPARAMS,
                 H_no_intra_task_parallelism into NOINTRA.
          unfold task_precedence_constraints, valid_sporadic_job,
                 jobs_of_same_task_dont_execute_in_parallel in *.
          intros j j' t SAMEtsk BEFORE PENDING.
          apply/negP; unfold not; intro SCHED'.
          destruct (scheduled sched j t) eqn:SCHED.
          {
            specialize (NOINTRA j j' t SAMEtsk SCHED SCHED'); subst.
            by rewrite ltnn in BEFORE.
          }
          apply negbT in SCHED.
          assert (INTERF: job_interference job_cost sched j j' t t.+1 != 0).
          {
            unfold job_interference; rewrite -lt0n.
            rewrite big_nat_recr // /=.
            by unfold backlogged; rewrite PENDING SCHED SCHED' 2!andbT addn1.
          }
          apply interference_under_edf_implies_shorter_deadlines
            with (job_deadline0 := job_deadline) in INTERF; last first. by done.
          have PARAMS := (JOBPARAMS j); have PARAMS' := (JOBPARAMS j'); des.
          rewrite PARAMS1 PARAMS'1 SAMEtsk leq_add2r in INTERF.
          by apply (leq_trans BEFORE) in INTERF; rewrite ltnn in INTERF.
        Qed.

      End SufficientCase.

      Section NecessaryCase.

        (* Assume that all tasks have valid parameters. *)
        Hypothesis H_valid_task_parameters:
          forall (j: JobIn arr_seq),
            is_valid_sporadic_task task_cost task_period task_deadline (job_task j).
          
        (* Assume that jobs do not execute before their arrival times,
           nor longer than their completion times. *)
        Hypothesis H_jobs_must_arrive_to_execute:
          jobs_must_arrive_to_execute sched.
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.

        (* Assume that job arrivals are sporadic (but in fact any separation works). *)
        Hypothesis H_sporadic_tasks:
          sporadic_task_model task_period arr_seq job_task.

        (* If we enforce task precedence constraints, ... *)
        Hypothesis H_task_precedence:
          task_precedence_constraints job_cost job_task sched.
        
        (* ... then jobs of same task do not execute in parallel.  *)
        Lemma edf_task_precedence_implies_no_intratask_parallelism :
          jobs_of_same_task_dont_execute_in_parallel job_task sched.
        Proof.
          rename H_valid_job_parameters into JOBPARAMS,
                 H_valid_task_parameters into PARAMS,
                 H_task_precedence into PREC,
                 H_sporadic_tasks into SPO.
          unfold is_valid_sporadic_task,
                 task_precedence_constraints, valid_sporadic_job,
                 jobs_of_same_task_dont_execute_in_parallel,
                 sporadic_task_model in *.
          intros j j' t SAMEtsk SCHED SCHED'.
          apply/eqP; rewrite -[_ == _]negbK; apply/negP; move => /eqP DIFF.
          destruct (ltnP (job_arrival j) (job_arrival j')) as [BEFORE | BEFORE'].
          {
            apply scheduled_implies_pending with (job_cost0 := job_cost) in SCHED;
              try (by done).
            specialize (PREC j j' t SAMEtsk BEFORE SCHED).
            by rewrite SCHED' in PREC.
          }
          {
            apply scheduled_implies_pending with (job_cost0 := job_cost) in SCHED';
              try (by done).
            assert (BEFORE'': job_arrival j' < job_arrival j).
            {
              apply leq_trans with (n := job_arrival j' + task_period (job_task j'));
                first by rewrite -addn1 leq_add2l; specialize (PARAMS j'); des.
              by apply SPO; [ by red; ins; subst | by rewrite SAMEtsk |].
            }
            by exploit (PREC j' j t); try (by done); rewrite SCHED.
          }
        Qed.

      End NecessaryCase.

    End IntraTaskParallelismAndTaskPrecedenceUnderEDF.

  End Lemmas.
  
End PlatformEDF.