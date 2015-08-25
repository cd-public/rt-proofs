Require Import Vbase TaskDefs ScheduleDefs
               ssreflect eqtype ssrbool ssrnat seq.

Module Schedulability.

  Import Schedule SporadicTaskset.

  Section SchedulableDefs.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> nat.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
  
    Section SingleSchedule.

      Variable num_cpus: nat.
      Variable rate: Job -> processor -> nat.
      Variable schedule_from_platform: schedule Job -> Prop.
      Variable sched: schedule Job.
    
      Hypothesis sched_platform: schedule_from_platform sched.

      Definition job_misses_no_deadline (j: Job) :=
        completed job_cost num_cpus rate sched j (job_arrival j + job_deadline j).

      Definition no_deadline_misses_in :=
        forall j arr,
          arrives_at job_arrival j arr ->
          completed job_cost num_cpus rate sched j (arr + job_deadline j).

    End SingleSchedule.

    Section SingleScheduleTasks.

      Variable job_task: Job -> sporadic_task.
    
      Variable num_cpus: nat.
      Variable rate: Job -> processor -> nat.
      Variable schedule_from_platform: schedule Job -> Prop.
      Variable sched: schedule Job.
    
      Hypothesis sched_platform: schedule_from_platform sched.

      Variable ts: sporadic_taskset.
      Variable tsk: sporadic_task.
      Hypothesis task_in_taskset : tsk \in ts.

      Definition task_misses_no_deadline :=
        forall j,
          job_task j == tsk ->
          job_misses_no_deadline num_cpus rate sched j.

      Definition task_misses_no_deadline_before (t': time) :=
        forall j,
          job_task j == tsk ->
          job_arrival j + job_deadline j <= t' ->
          job_misses_no_deadline num_cpus rate sched j.

    End SingleScheduleTasks.

  End SchedulableDefs.

End Schedulability.


  (*Definition schedulable_task (ts: taskset) (tsk: sporadic_task) :=
  forall sched (PLAT: platform sched), task_misses_no_dl sched ts tsk.

Definition schedulable_taskset (ts: taskset) :=
  forall sched (PLAT: platform sched) (ARRts: ts_arrival_sequence ts sched)
         tsk (IN: tsk \in ts), task_misses_no_dl sched ts tsk.*)
