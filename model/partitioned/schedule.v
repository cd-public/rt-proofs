Require Import rt.util.all.
Require Import rt.model.time rt.model.task rt.model.job.
Require Import rt.model.global.schedulability.
Require Import rt.model.global.basic.schedule.
Require rt.model.uni.schedule rt.model.uni.schedulability.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Partitioned.

  Module uni := rt.model.uni.schedule.UniprocessorSchedule.
  Module uni_sched := rt.model.uni.schedulability.Schedulability.
  Import SporadicTaskset Schedule Schedulability.
  Export Time.
  
  Section PartitionedDefs.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence. *)
    Context {arr_seq: arrival_sequence Job}.


    (* Given any multiprocessor schedule of these jobs, ... *)
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* ... we define a notion of "partitioned scheduling" (= no migrations) on
      a per-job, per-task, and finally whole-schedule level. *)

    Section NoJobMigration.

      (* A job is "partitioned" iff it never migrates, i.e., it
       * executes on the same processor whenever it is scheduled. *)

      (* So any job j... *)
      Variable j: JobIn arr_seq.

      (* ... never migrates iff the following holds: ... *)
      Definition never_migrates :=
        (* ...for any point in time t... *)
        forall t,
          (* ...and any processor cpu... *)
        forall cpu,
          (* ... if job j is scheduled at time t on processor cpu... *)
          scheduled_on sched j cpu t ->
          (* ...then at any other time... *)
          forall t',
            (* ...if the same job is scheduled, it must be scheduled on
             * the same processor. *)
            forall cpu',
              scheduled_on sched j cpu' t' -> cpu' = cpu.

      (* Furthermore, we say that the job is assigned to processor assigned_cpu
       * if it executes only on that processor. *)
      Variable assigned_cpu : processor num_cpus.
      Definition job_local_to_processor :=
        forall t, forall cpu,
          scheduled_on sched j cpu t -> cpu = assigned_cpu.

    End NoJobMigration.
    
    (* Having defined a notiont of 'partitioned' for individual jobs, let us
     * now turn to tasks. *)

    Section NoTaskMigration.

      (* Given any task tsk in ts, ... *)
      Variable tsk: Task.

      (* ...we say that tsk is assigned to processor assigned_cpu ... *)
      Variable assigned_cpu : processor num_cpus.

      (* ...iff every job of tsk executes exclusively on assigned_cpu. *)
      Definition task_local_to_processor :=
        forall j : JobIn arr_seq,
          job_task j = tsk -> job_local_to_processor j assigned_cpu.

    End NoTaskMigration.

    (* Finally, a schedule is fully partitioned iff every task is assigned
       to some processor. *)
    Section PartitionedSchedule.

      (* Consider a task set ts to be scheduled. *)
      Variable ts: list Task.
      
      (* Given an assignment from every task in ts to a processor, ...*)
      Variable assigned_cpu: Task -> processor num_cpus.

      (* ...we say that a schedule is partitioned iff every task is local
         to the corresponding processor. *)
      Definition partitioned_schedule :=
        forall tsk,
          tsk \in ts ->
          task_local_to_processor tsk (assigned_cpu tsk).
      
    End PartitionedSchedule.

  End PartitionedDefs.

  Section SimpleProperties.

    Context {Job: eqType}.

    Context {arr_seq: arrival_sequence Job}.
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    Section NoJobMigrationLemmas.

      Variable j: JobIn arr_seq.

      Lemma local_jobs_dont_migrate:
        forall cpu,
          job_local_to_processor sched j cpu -> never_migrates sched j.
      Proof.
        rewrite /job_local_to_processor /never_migrates
             =>  cpu H_is_local t cpu' H_sched_at_t t' cpu'' H_sched_at_t'.
        apply H_is_local in H_sched_at_t.
        apply H_is_local in H_sched_at_t'.
        by rewrite H_sched_at_t H_sched_at_t'.
      Qed.

    End NoJobMigrationLemmas.

  End SimpleProperties.

  Section PartitionedAsUniprocessor.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> Task.
    
    (* Consider any job arrival sequence that is to be scheduled. *)
    Context {arr_seq: arrival_sequence Job}.
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* Assume that all jobs in the arrival sequence come from a task set ts. *)
    Variable ts: list Task.
    Hypothesis H_all_jobs_from_ts:
      forall (j: JobIn arr_seq), job_task j \in ts.

    (* Also assume that every task is assigned to a processor, ... *)
    Variable assigned_cpu: Task -> processor num_cpus.

    (* ...forming a partitioned schedule. *)
    Hypothesis H_partitioned: partitioned_schedule job_task sched ts assigned_cpu.

    (* Next, we related total service with per-processor service received by each job. *)
    Section SameService.

      (* Consider the partition where each job is assigned to. *)
      Let partition_of (j: JobIn arr_seq) := assigned_cpu (job_task j).

      (* We prove that the service received by job j (on the multiprocessor)
         is the same as the service received by job j in its partition. *)
      Lemma same_per_processor_service :
        forall j t1 t2,
          service_during sched j t1 t2 =
          uni.service_during (sched (partition_of j)) j t1 t2.
      Proof.
        intros j t1 t2.
        unfold partitioned_schedule, task_local_to_processor,
               job_local_to_processor, service_during, service_at,
               uni.service_during, uni.service_at,
               uni.scheduled_at, scheduled_on, partition_of in *.
        rename H_partitioned into PART, H_all_jobs_from_ts into FROMTS.
        apply eq_bigr; intros t _.
        unfold uni.service_at, uni.scheduled_at.
        feed (PART (job_task j) (FROMTS j) j); [by done | specialize (PART t)].
        destruct (scheduled sched j t) eqn:SCHED; last first.
        {
          apply negbT in SCHED; rewrite negb_exists in SCHED.
          move: SCHED => /forallP SCHED.
          have SCHEDcpu := SCHED (assigned_cpu (job_task j)); apply negbTE in SCHEDcpu.
          unfold scheduled_on in *; rewrite SCHEDcpu.
          rewrite big1; first by done.
          move => cpu /eqP SCHED'.
          by specialize (SCHED cpu); rewrite SCHED' eq_refl in SCHED.
        }
        {
          move: SCHED => /existsP [cpu SCHED].
          rewrite (bigD1 cpu) /=; last by done.
          have SAME := PART cpu SCHED; rewrite -SAME.
          unfold scheduled_on in *; rewrite SCHED.
          rewrite add1n; apply/eqP; rewrite eqSS; apply/eqP.
          rewrite big1; first by done.
          move => cpu' /andP [SCHED' NEQ].
          have SAME' := (PART cpu' SCHED'); subst cpu cpu'.
          by rewrite eq_refl in NEQ.
        }
      Qed.
        
    End SameService.

    Section Schedulability.

      (* Recall the definitions of schedulability on a uniprocessor and on
         a multiprocessor. *)
      Let schedulable_on tsk cpu := uni_sched.task_misses_no_deadline job_cost job_deadline job_task (sched cpu) tsk.
      Let schedulable := task_misses_no_deadline job_cost job_deadline job_task sched.


      (* Here we prove that if every task is schedulable in their assigned processors, ...*)
      Hypothesis H_locally_schedulable:
        forall tsk,
          tsk \in ts -> schedulable_on tsk (assigned_cpu tsk).

      (* ...then every task is schedulable at the level of the multiprocessor system. *)
      Lemma schedulable_at_system_level:
        forall tsk,
          tsk \in ts -> schedulable tsk.
      Proof.
        have SAME := same_per_processor_service.
        unfold partitioned_schedule, task_local_to_processor,
               job_local_to_processor, schedulable, schedulable_on,
               task_misses_no_deadline, job_misses_no_deadline,
               completed, uni_sched.task_misses_no_deadline,
               uni_sched.job_misses_no_deadline, uni.completed_by in *.
        rename H_locally_schedulable into SCHED,
               H_partitioned into PART.
        intros tsk IN j JOBtsk.
        specialize (SCHED tsk IN j JOBtsk).
        move: SCHED => /eqP <-.
        unfold service, uni.service, service_during, uni.service_during in *.
        by apply/eqP; rewrite SAME JOBtsk.
      Qed.

    End Schedulability.

  End PartitionedAsUniprocessor.
  
End Partitioned.