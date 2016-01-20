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

    (*Section JobInvariantAsTaskInvariant.

      (* Consider task set ts. *)
      Variable ts: taskset_of sporadic_task.
      
      (* Assume the task set has no duplicates, ... *)
      Hypothesis H_ts_is_a_set: uniq ts.
      (* ... and all jobs come from the taskset. *)
      Hypothesis H_all_jobs_from_taskset:
        forall (j: JobIn arr_seq), job_task j \in ts.

      (* Suppose that a single job does not execute in parallel, ...*)
      Hypothesis H_no_parallelism:
        jobs_dont_execute_in_parallel sched.
      (* ... jobs from the same task do not execute in parallel, ... *)
      (*Hypothesis H_no_intra_task_parallelism:
        jobs_of_same_task_dont_execute_in_parallel job_task sched.*)
      (* ... and jobs do not execute after completion. *)
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.
      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute sched.

      (* Assume that the schedule satisfies the sporadic task model ...*)
      Hypothesis H_sporadic_tasks:
        sporadic_task_model task_period arr_seq job_task.

      (* and task precedence constraints. *)
      (*Hypothesis H_task_precedence:
        task_precedence_constraints job_cost job_task sched.*)

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
        forall (j_other: JobIn arr_seq),
          job_arrival j_other < job_arrival j ->
          completed job_cost sched j_other (job_arrival j_other + task_period (job_task j_other)).

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
               (*H_no_intra_task_parallelism into NOINTRA,*)
               H_global_scheduling_invariant into INV,
               H_j_backlogged into BACK,
               H_job_of_tsk into JOBtsk,
               (*H_task_precedence into PREC,*)
               H_valid_job_parameters into JOBPARAMS,
               H_sporadic_tasks into SPO,
               H_valid_task into TASKPARAMS,
               H_all_previous_jobs_completed into PREV,
               H_completed_jobs_dont_execute into COMP,
               H_jobs_must_arrive_to_execute into ARRIVE.
        unfold JLFP_JLDP_scheduling_invariant_holds,
               valid_sporadic_job, valid_realtime_job,
               task_precedence_constraints, completed_jobs_dont_execute,
               sporadic_task_model, is_valid_sporadic_task,
               jobs_of_same_task_dont_execute_in_parallel,
               jobs_dont_execute_in_parallel in *.

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
          apply leq_trans with (n := count ((higher_eq_priority t)^~ j) (jobs_scheduled_at sched t));
            first by rewrite -> INV with (j := j) (t := t);
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
            apply negbT in EQjob; move: EQjob => /eqP DIFF.
            apply/negP; unfold not; move => /eqP SAMEtsk.
            assert (INTERF: job_interference job_cost sched j j_hp t t.+1 != 0).
            {
              move: BACK => /andP [PENDING NOTSCHED].
              unfold job_interference; rewrite -lt0n.
              rewrite big_nat_recr // /=.
              by unfold backlogged; rewrite PENDING NOTSCHED SCHED 2!andbT addn1.
            }
            apply interference_under_edf_implies_shorter_deadlines
              with (job_deadline0 := job_deadline) in INTERF; last by done.
            have PARAMS := (JOBPARAMS j); have PARAMS' := (JOBPARAMS j_hp); des.
            rewrite PARAMS1 PARAMS'1 JOBtsk SAMEtsk leq_add2r in INTERF.
            exploit (SPO j_hp j);
              [ by red; ins; subst | by rewrite JOBtsk SAMEtsk | by done |].
            intros LEarr.
            assert (LTarr: job_arrival j_hp < job_arrival j).
            {
              eapply leq_trans with (n := job_arrival j_hp + task_period (job_task j_hp));
                last by done.
              by rewrite -addn1 leq_add2l SAMEtsk.
            }
            specialize (PREV j_hp LTarr).
            apply completion_monotonic with (t' := t) in PREV;
              try (by done); last first.
            {
              move: BACK => /andP [/andP [ARRIVED NOTCOMP] NOTSCHED].
              by apply leq_trans with (n := job_arrival j);
                [by apply LEarr | by apply ARRIVED].
            }
            apply completed_implies_not_scheduled in PREV; try (by done).
            by rewrite SCHED in PREV.
          }
        }
        have MAP := count_map (fun (x: JobIn arr_seq) => job_task x) (fun x => is_interfering_task_jlfp tsk x && task_is_scheduled job_task sched x t). 
        rewrite -MAP; clear MAP.
        apply count_sub_uniqr.
        {
          rewrite map_inj_in_uniq; first by apply scheduled_jobs_uniq.
          red; intros j1 j2 SCHED1 SCHED2 SAMEtsk.
          rewrite mem_scheduled_jobs_eq_scheduled in SCHED1.
          rewrite mem_scheduled_jobs_eq_scheduled in SCHED2.
  
          move: (SCHED1) (SCHED2) => PENDING1 PENDING2.
          apply scheduled_implies_pending with (job_cost0 := job_cost) in PENDING1.
          apply scheduled_implies_pending with (job_cost0 := job_cost) in PENDING2.
          move: BACK => /andP [PENDING NOTSCHED].
          assert (INTERF1: job_interference job_cost sched j j1 t t.+1 != 0).
          {
            unfold job_interference; rewrite -lt0n.
            rewrite big_nat_recr // /=.
            by unfold backlogged; rewrite PENDING NOTSCHED SCHED1 2!andbT addn1.
          }
          assert (INTERF2: job_interference job_cost sched j j2 t t.+1 != 0).
          {
            unfold job_interference; rewrite -lt0n.
            rewrite big_nat_recr // /=.
            by unfold backlogged; rewrite PENDING NOTSCHED SCHED2 2!andbT addn1.
          }
          apply interference_under_edf_implies_shorter_deadlines with (job_deadline0 := job_deadline) in INTERF1.
          apply interference_under_edf_implies_shorter_deadlines with (job_deadline0 := job_deadline) in INTERF2.

          destruct (job_arrival j1 < job_arrival j2) eqn:LEarr.
          {
            assert (DIFF: j1 <> j2). admit.
            specialize (SPO j1 j2 DIFF SAMEtsk).
            specialize (PREV j2).
          Print task_precedence_constraints.
          (*by red; ins; apply NOINTRA with (t := t);
            rewrite // -mem_scheduled_jobs_eq_scheduled.*)
          
        }
        {
          red; intros x IN.
          move: IN => /mapP IN; destruct IN as [j' _ EQx].
          by rewrite EQx; apply FROMTS.
        }
      }
    Qed.

    End JobInvariantAsTaskInvariant.*)

    Section WorkConserving.

      (* We show that the EDF scheduling invariant implies work conservation. *)
      Lemma edf_invariant_implies_work_conservation:
        is_work_conserving job_cost num_cpus sched.
      Proof.
        rename H_global_scheduling_invariant into INV.
        unfold is_work_conserving,
               JLFP_JLDP_scheduling_invariant_holds in *.
        intros j t BACK.
        specialize (INV j t BACK).
        apply/eqP; rewrite eqn_leq; apply/andP; split;
          first by apply num_scheduled_jobs_le_num_cpus.
        eapply leq_trans;
          first by apply eq_leq; symmetry; apply INV.
        by apply leq_trans with (n := count predT (jobs_scheduled_at sched t));
          [by apply sub_count | by apply count_size].
      Qed.
      
    End WorkConserving.
    
  End Lemmas.
  
End PlatformEDF.