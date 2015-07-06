Require Import Vbase task.

Section Job.

Record job : Type :=
{
  (* UNNEEDED job_id: nat;*) (* job_id allows multiple jobs with same parameters *)
  job_cost: nat; (* actual cost *)
  job_deadline: nat; (* relative deadline *)
  job_task: sporadic_task; (* Task that spawns this job *)

  job_properties:
    << job_cost_positive: job_cost > 0 >> /\
    << job_cost_le_deadline: job_cost <= job_deadline >> /\
    << job_dl_positive: job_deadline > 0 >> /\
    << job_params: (job_cost <= task_cost job_task /\
                    job_deadline = task_deadline job_task)>>
}.

(* Observations / TODO *)
(* 1) It should be ok to have 0-cost jobs. Deadlines can also be 0,
      as long as the cost is no greater than the deadline.
      But let's keep it like this for now. We can remove it if needed.

   2) job_task could be (option sporadic_task), so that we allow jobs that
      don't belong to any task. But our definition of job is not modular yet,
      so we could leave that for when we support different task models.
      For different task models, we might allow multiple jobs with same parameters,
      but the current specification is ok for the sporadic task model.

   3) job_properties restrict the deadline of the job to have the same
      deadline as the task. Doesn't work if we want to use overhead accounting.
      We need to decouple job_properties from job and enforce them only in
      specific schedulability tests.
*)

End Job.