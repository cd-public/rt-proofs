Require Import Vbase ssrnat.

Module Job.

Parameter job: Set.

Parameter job_arrival: job -> nat. (* Absolute arrival time *)
Parameter job_cost: job -> nat. (* Actual cost *)
Parameter job_deadline: job -> nat. (* Relative deadline *)

Definition valid_job (j: job) :=
  << job_cost_positive: job_cost j > 0 >> /\
  << job_cost_le_deadline: job_cost j <= job_deadline j >> /\
  << job_dl_positive: job_deadline j > 0 >>.

(* Assume decidable equality for computations using jobs. *)
Load eqjob_dec.

End Job.

Module SporadicTaskJob.
  Require Import TaskDefs.
  Export Job SporadicTask.
  
  (* Sporadic task that spawns this job *)
  Parameter job_task: job -> sporadic_task. 

  (* All jobs spawned by a sporadic task must satisfy their constraints. *)
  Definition job_of_sporadic_task :=
    forall j tsk (JOBtask: job_task j = tsk),
      << JOBmaxcost: job_cost j <= task_cost tsk >> /\
      << JOBdl: job_deadline j = task_deadline tsk >>.

End SporadicTaskJob.