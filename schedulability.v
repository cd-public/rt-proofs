Require Import Vbase List job task task_arrival schedule platform.

Section Schedulability.

Variable platform: processor_platform.

Section SingleSchedule.

Variable sched: schedule.
Hypothesis sched_platform: platform sched.

Definition job_misses_no_deadlines (j: job) :=
  exists arr, << ARR: arrives_at sched j arr >> /\
              << SERV: service sched j (arr + job_deadline j) = job_cost j >>.

Definition no_deadline_misses :=
  forall j arr (ARR: arrives_at sched j arr),
    service sched j (arr + job_deadline j) = job_cost j.

Definition task_misses_no_deadlines (ts: taskset) (tsk: sporadic_task) :=
  << IN: In tsk ts >> /\ << ARRts: ts_arrival_sequence ts sched >> /\
  forall j (JOB: job_task j = tsk) arr (ARR: arrives_at sched j arr), job_misses_no_deadlines j.

End SingleSchedule.

Definition schedulable_task (ts: taskset) (tsk: sporadic_task) :=
  forall sched (PLAT: platform sched), task_misses_no_deadlines sched ts tsk.

Definition schedulable_taskset (ts: taskset) :=
  forall sched (PLAT: platform sched) (ARRts: ts_arrival_sequence ts sched)
         tsk (IN: In tsk ts), task_misses_no_deadlines sched ts tsk.

End Schedulability.