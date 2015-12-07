Require Import Vbase TaskDefs ScheduleDefs
               ssreflect eqtype ssrbool ssrnat seq.

Module Schedulability.

  Import Schedule SporadicTaskset.

  Section SchedulableDefs.
    
    Context {Job: eqType}.
    Context {arr_seq: arrival_sequence Job}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
  
    Section ScheduleOfJobs.

      Context {num_cpus: nat}.
      Variable rate: Job -> processor num_cpus -> nat.
      Variable sched: schedule num_cpus arr_seq.

      Variable j: JobIn arr_seq.

      Definition job_misses_no_deadline :=
        completed job_cost rate sched j (job_arrival j + job_deadline j).

    End ScheduleOfJobs.

    Section ScheduleOfTasks.

      Context {sporadic_task: eqType}.
      Variable job_task: Job -> sporadic_task.
    
      Context {num_cpus: nat}.
      Variable rate: Job -> processor num_cpus -> nat.
      Variable sched: schedule num_cpus arr_seq.

      Variable ts: taskset_of sporadic_task.
      Variable tsk: sporadic_task.

      Definition task_misses_no_deadline :=
        forall (j: JobIn arr_seq),
          job_task j == tsk ->
          job_misses_no_deadline rate sched j.

      Definition task_misses_no_deadline_before (t': time) :=
        forall (j: JobIn arr_seq),
          job_task j == tsk ->
          job_arrival j + job_deadline j < t' ->
          job_misses_no_deadline rate sched j.

    End ScheduleOfTasks.

  End SchedulableDefs.

End Schedulability.