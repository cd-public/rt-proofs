Require Import Vbase TaskDefs JobDefs ScheduleDefs helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module SporadicTaskArrival.

Import SporadicTaskset Schedule.
  
  Section ArrivalModels.

    Context {sporadic_task: eqType}.
    Variable task_period: sporadic_task -> nat.
    
    Context {Job: eqType}.
    Variable arr_seq: arrival_sequence Job.
    Variable job_task: Job -> sporadic_task.

    (* TODO: The definition of periodic is wrong. Only the closest
       job has arrives period units later. *)
    (*Definition periodic_task_model :=
      forall j j',
             j <> j' -> (* Given two different jobs j and j' such that *)
             job_task j = job_task j' -> (* they are from the same task *)
             job_arrival j <= job_arrival j' -> (* and arr <= arr' *)
        (* then the next jobs arrives 'period' time units later. *)
        job_arrival j' = job_arrival j' + task_period (job_task j).*)
    
    Definition sporadic_task_model :=
      forall (j j': JobIn arr_seq),
             j <> j' -> (* Given two different jobs j and j' such that *)
             job_task j = job_task j' -> (* they are from the same task *)
             job_arrival j <= job_arrival j' -> (* and arr <= arr' *)
        (* then the next jobs arrives 'period' time units later. *)
        job_arrival j' >= job_arrival j + task_period (job_task j).

  End ArrivalModels.
  
End SporadicTaskArrival.