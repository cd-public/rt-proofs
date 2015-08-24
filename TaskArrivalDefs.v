Require Import Vbase TaskDefs JobDefs ScheduleDefs helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module SporadicTaskArrival.

Import SporadicTaskset Schedule.
  
  Section ArrivalModels.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_task: Job -> sporadic_task.

    Definition periodic_task_model :=
      forall j arr j' arr',
             j <> j' -> (* Given two different jobs j and j' such that *)
             arrives_at job_arrival j arr -> (* j arrives at time arr, *)
             arrives_at job_arrival j' arr' -> (* j' arrives at time arr', *)
             job_task j = job_task j' -> (* both jobs are from the same task *)
             arr <= arr' -> (* arr <= arr' *)
        (* then the next jobs arrives 'period' time units later. *)
        arr' = arr + task_period (job_task j).

    Definition sporadic_task_model :=
      forall j arr j' arr',
             j <> j' -> (* Given two different jobs j and j' such that *)
             arrives_at job_arrival j arr -> (* j arrives at time arr, *)
             arrives_at job_arrival j' arr' -> (* j' arrives at time arr', *)
             job_task j = job_task j' -> (* both jobs are from the same task *)
             arr <= arr' -> (* arr <= arr', *)
        (* then the job arrivals are separated by the period (at least). *)
        arr' >= arr + task_period (job_task j).

  End ArrivalModels.
  
End SporadicTaskArrival.