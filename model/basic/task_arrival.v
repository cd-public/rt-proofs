Add LoadPath "../../" as rt.
Require Import rt.util.Vbase rt.util.lemmas.
Require Import rt.model.basic.task rt.model.basic.job rt.model.basic.schedule.
Require Import ssreflect ssrbool eqtype ssrnat seq.

(* Properties of the job arrival. *)
Module SporadicTaskArrival.

Import SporadicTaskset Schedule.
  
  Section ArrivalModels.

    (* Assume the task period is known. *)
    Context {sporadic_task: eqType}.
    Variable task_period: sporadic_task -> nat.
    
    Context {Job: eqType}.
    Variable arr_seq: arrival_sequence Job.
    Variable job_task: Job -> sporadic_task.

    (* Then, we define the sporadic task model as follows.*)
    
    Definition sporadic_task_model :=
      forall (j j': JobIn arr_seq),
             j <> j' -> (* Given two different jobs j and j' ... *)
             job_task j = job_task j' -> (* ... of the same task, ... *)
             job_arrival j <= job_arrival j' -> (* ... if the arrival of j precedes the arrival of j' ...,  *)
        (* then the arrival of j and the arrival of j' are separated by at least one period. *)
        job_arrival j' >= job_arrival j + task_period (job_task j).

  End ArrivalModels.
  
End SporadicTaskArrival.