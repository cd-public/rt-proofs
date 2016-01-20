Add LoadPath "../.." as rt.
Require Import rt.util.Vbase rt.util.lemmas.
Require Import rt.model.jitter.task rt.model.jitter.job rt.model.jitter.schedule
               rt.model.jitter.priority rt.model.jitter.task_arrival rt.model.jitter.interference.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module Platform.

  Import Job SporadicTaskset ScheduleWithJitter ScheduleOfSporadicTask SporadicTaskset SporadicTaskArrival Interference Priority.

  Section SchedulingInvariants.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    Variable job_jitter: Job -> nat.
    
    (* Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.

    (* Consider any schedule. *)
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    Section WorkConserving.

      (* A scheduler is work-conserving iff when a job j is backlogged,
         all processors are busy with other jobs.
         NOTE: backlogged means that jitter has passed. *)
      Definition work_conserving :=
        forall (j: JobIn arr_seq) t,
          backlogged job_cost job_jitter sched j t ->
          size (jobs_scheduled_at sched t) = num_cpus.
      
    End WorkConserving.

    Section JLDP.

      (* A JLFP/JLDP policy ...*)
      Variable higher_eq_priority: JLDP_policy arr_seq.

      (* ... is enforced by the scheduler iff at any time t,
         a scheduled job has higher (or same) priority than (as)
         a backlogged job. *)
      Definition enforces_JLDP_policy :=
        forall (j j_hp: JobIn arr_seq) t,
          backlogged job_cost job_jitter sched j t ->
          scheduled sched j_hp t ->
          higher_eq_priority t j_hp j.
      
    End JLDP.
    
    Section FP.

      (* Given an FP policy, ...*)
      Variable higher_eq_priority: FP_policy sporadic_task.

      (* ... this policy is enforced by the scheduler iff
         a corresponding JLDP policy is enforced by the scheduler. *)
      Definition enforces_FP_policy :=
        enforces_JLDP_policy (FP_to_JLDP job_task higher_eq_priority).

    End FP.
    
    Section Lemmas.

      (* Assume all jobs have valid parameters, ...*)
      Hypothesis H_valid_job_parameters:
        forall (j: JobIn arr_seq),
          valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

      Section JobInvariantAsTaskInvariant.

        (* Assume any work-conserving priority-based scheduler. *)
        Variable higher_eq_priority: JLDP_policy arr_seq.
        Hypothesis H_work_conserving: work_conserving.
        Hypothesis H_enforces_JLDP_policy: enforces_JLDP_policy higher_eq_priority.
                   
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
        (* ... jobs only execute after the jitter, ... *)
        Hypothesis H_jobs_execute_after_jitter:
          jobs_execute_after_jitter job_jitter sched.
        (* ... and jobs do not execute after completion. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
        
        (* Assume that the schedule satisfies the sporadic task model ...*)
        Hypothesis H_sporadic_tasks:
          sporadic_task_model task_period arr_seq job_task.

        (* Consider a valid task tsk, ...*)
        Variable tsk: sporadic_task.
        Hypothesis H_valid_task: is_valid_sporadic_task task_cost task_period task_deadline tsk.

        (*... whose job j ... *)
        Variable j: JobIn arr_seq.
        Variable H_job_of_tsk: job_task j = tsk.

        (*... is backlogged at time t. *)
        Variable t: time.
        Hypothesis H_j_backlogged: backlogged job_cost job_jitter sched j t.

        (* Assume that any previous jobs of tsk have completed by the period. *)
        Hypothesis H_all_previous_jobs_completed :
          forall (j_other: JobIn arr_seq) tsk_other,
            job_task j_other = tsk_other ->
            job_arrival j_other + task_period tsk_other <= t ->
            completed job_cost sched j_other (job_arrival j_other + task_period (job_task j_other)).

        Let scheduled_task_other_than (tsk tsk_other: sporadic_task) :=
          task_is_scheduled job_task sched tsk_other t && (tsk_other != tsk).

        (* Then, there can be at most one pending job of each task at time t. *)
        Lemma platform_at_most_one_pending_job_of_each_task :
          forall j1 j2,
            pending job_cost job_jitter sched j1 t ->
            pending job_cost job_jitter sched j2 t ->
            job_task j1 = job_task j2 ->
            j1 = j2.
        Proof.
          rename H_sporadic_tasks into SPO, H_all_previous_jobs_completed into PREV.
          intros j1 j2 PENDING1 PENDING2 SAMEtsk.
          apply/eqP; rewrite -[_ == _]negbK; apply/negP; red; move => /eqP DIFF. 
          move: PENDING1 PENDING2 => /andP [ARRIVED1 /negP NOTCOMP1] /andP [ARRIVED2 /negP NOTCOMP2].
          unfold has_actually_arrived_by, actual_arrival in *.
          destruct (leqP (job_arrival j1) (job_arrival j2)) as [BEFORE1 | BEFORE2].
          {
            specialize (SPO j1 j2 DIFF SAMEtsk BEFORE1).
            assert (LEt: job_arrival j1 + task_period (job_task j1) <= t).
            {
              apply leq_trans with (n := job_arrival j2); first by done.
              by apply leq_trans with (n := job_arrival j2 + job_jitter j2); first by apply leq_addr.
            }
            exploit (PREV j1 (job_task j1)); try (by done).
            intros COMP1; apply NOTCOMP1.
            by apply completion_monotonic with (t0 := job_arrival j1 + task_period (job_task j1)). 
          }
          {
            apply ltnW in BEFORE2.
            exploit (SPO j2 j1); [by red; ins; subst | by rewrite SAMEtsk | by done | intro SPO'].
            assert (LEt: job_arrival j2 + task_period (job_task j2) <= t).
            {
              apply leq_trans with (n := job_arrival j1); first by done.
              by apply leq_trans with (n := job_arrival j1 + job_jitter j1); first by apply leq_addr.
            }
            exploit (PREV j2 (job_task j2)); try (by done).
            intros COMP2; apply NOTCOMP2.
            by apply completion_monotonic with (t0 := job_arrival j2 + task_period (job_task j2)).
          }
        Qed.

        (* Therefore, all processors are busy with tasks other than tsk. *)
        Lemma platform_cpus_busy_with_interfering_tasks :      
          count (scheduled_task_other_than tsk) ts = num_cpus.
        Proof.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_no_parallelism into SEQUENTIAL,
                 H_work_conserving into WORK,
                 H_enforces_JLDP_policy into PRIO,
                 H_j_backlogged into BACK,
                 H_job_of_tsk into JOBtsk,
                 H_valid_job_parameters into JOBPARAMS,
                 H_valid_task into TASKPARAMS,
                 H_all_previous_jobs_completed into PREV,
                 H_completed_jobs_dont_execute into COMP,
                 H_jobs_execute_after_jitter into JITTER.
          unfold valid_sporadic_job, valid_realtime_job,
                 enforces_JLDP_policy,
                 task_precedence_constraints, completed_jobs_dont_execute,
                 sporadic_task_model, is_valid_sporadic_task,
                 jobs_of_same_task_dont_execute_in_parallel,
                 jobs_dont_execute_in_parallel in *.  
          have UNIQ := platform_at_most_one_pending_job_of_each_task.
          apply/eqP; rewrite eqn_leq; apply/andP; split.
          {
            apply leq_trans with (n := count (fun x => task_is_scheduled job_task sched x t) ts);
              first by apply sub_count; first by red; move => x /andP [SCHED _].    
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
            rewrite -(WORK j t) // -count_predT.       
            apply leq_trans with (n := count (fun j: JobIn arr_seq => scheduled_task_other_than tsk (job_task j)) (jobs_scheduled_at sched t));
              last first.
            {
              rewrite -count_map.
              apply count_sub_uniqr;
                last by red; move => tsk' /mapP [j' _ JOBtsk']; subst; apply FROMTS.
              rewrite map_inj_in_uniq; first by apply scheduled_jobs_uniq.
              red; intros j1 j2 SCHED1 SCHED2 SAMEtsk.
              rewrite 2!mem_scheduled_jobs_eq_scheduled in SCHED1 SCHED2.
              apply scheduled_implies_pending with (job_cost0 := job_cost)
                    (job_jitter0 := job_jitter) in SCHED1; try (by done).
              apply scheduled_implies_pending with (job_cost0 := job_cost)
                    (job_jitter0 := job_jitter) in SCHED2; try (by done).
              by apply UNIQ.
            }
            {
              apply sub_in_count; intros j' SCHED' _.
              rewrite mem_scheduled_jobs_eq_scheduled in SCHED'.
              unfold scheduled_task_other_than; apply/andP; split.
              {
                move: SCHED' => /exists_inP [cpu INcpu /eqP SCHED'].
                apply/exists_inP; exists cpu; first by done.
                by unfold schedules_job_of_tsk; rewrite SCHED' eq_refl.
              }
              {
                apply/eqP; red; intro SAMEtsk; symmetry in SAMEtsk.
                move: BACK => /andP [PENDING NOTSCHED].
                generalize SCHED'; intro PENDING'.
                apply scheduled_implies_pending with (job_cost0 := job_cost)
                      (job_jitter0 := job_jitter) in PENDING'; try (by done).
                exploit (UNIQ j j' PENDING PENDING'); [by rewrite -SAMEtsk | intro EQjob; subst].
                by rewrite SCHED' in NOTSCHED.
              }
            }
          }
        Qed.

      End JobInvariantAsTaskInvariant.

    End Lemmas.

  End SchedulingInvariants.
  
End Platform.