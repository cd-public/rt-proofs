Require Import Vbase job task task_arrival schedule platform
               ssrbool ssrnat seq.

Section Schedulability.

Variable platform: processor_platform.

Section SingleSchedule.

Variable sched: schedule.
Hypothesis sched_platform: platform sched.

Definition job_misses_no_dl (j: job) :=
  << COMP: completed sched j (job_arrival j + job_deadline j) >>.

Definition no_dl_misses :=
  forall j arr (ARR: arrives_at sched j arr),
    completed sched j (arr + job_deadline j).

Definition task_misses_no_dl (ts: taskset) (tsk: sporadic_task) :=
  << IN: tsk \in ts >> /\
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall j (JOB: job_task j = tsk) arr (ARR: arrives_at sched j arr),
    job_misses_no_dl j.

Definition task_misses_no_dl_before (ts: taskset) (tsk: sporadic_task) (t': time) :=
  << IN: tsk \in ts >> /\
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall j (JOB: job_task j = tsk)
         arr (ARR: arrives_at sched j arr)
         (BEFOREdl: job_arrival j + job_deadline j <= t'),
    job_misses_no_dl j.

End SingleSchedule.

Definition schedulable_task (ts: taskset) (tsk: sporadic_task) :=
  forall sched (PLAT: platform sched), task_misses_no_dl sched ts tsk.

Definition schedulable_taskset (ts: taskset) :=
  forall sched (PLAT: platform sched) (ARRts: ts_arrival_sequence ts sched)
         tsk (IN: tsk \in ts), task_misses_no_ sched ts tsk.

End Schedulability.